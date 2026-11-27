/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-state complement factorization and the charge-two fractional Virasoro action. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverIntegerFactor
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverVirasoro

/-!
The two nonzero residue grids in the third-cover oscillator Fock space.
The full cover action and its current and Virasoro brackets are those of
`ThirdCoverVirasoro`. The complementary Heisenberg pairing agrees with the
frequency convention in Bakalov and Kac, arXiv:math/0402315v1, (4.23).
The tensor factorization and charge-two commutator are proved here by transport
and subtraction of the ordinary charge-one action.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverComplement

open MvPolynomial PolynomialFockSugawaraSupport ThirdCoverIntegerFactor
open ThirdCoverVirasoro (coverMode)
open scoped TensorProduct

/-- Native cover indices, with creation by multiplication and annihilation by a
weighted derivative in the matching complement variable. -/
def complementMode : ℤ → Module.End ℂ ComplementFock
  | .ofNat 0 => 0
  | .ofNat (k + 1) =>
      if h : ¬ 3 ∣ k + 1 then
        (↑k + 1 : ℂ) • (pderiv (⟨k, h⟩ : Complement)).toLinearMap
      else 0
  | .negSucc k =>
      if h : ¬ 3 ∣ k + 1 then LinearMap.mulLeft ℂ (X (⟨k, h⟩ : Complement))
      else 0

private theorem pderiv_join_complement (s : ℂ) (hs : s ≠ 0) (k : Complement)
    (P : Fock) (Q : ComplementFock) :
    pderiv k.val (join s hs (P ⊗ₜ[ℂ] Q)) =
      join s hs (P ⊗ₜ[ℂ] pderiv k Q) := by
  have hnot : k.val ∉ (rename ordinaryVar (scale s⁻¹ P)).vars := by
    intro h
    obtain ⟨j, _, hj⟩ := mem_vars_rename ordinaryVar (scale s⁻¹ P) h
    exact k.property (hj ▸ dvd_ordinaryVar_succ j)
  rw [join_tmul, pderiv_mul, pderiv_eq_zero_of_notMem_vars hnot, zero_mul, zero_add,
    pderiv_rename Subtype.val_injective, join_tmul]

/-- Each nonintegral current acts on the second factor of every pure tensor. -/
theorem mode_join_complement (s : ℂ) (hs : s ≠ 0) (r : ℤ) (hr : ¬ (3 : ℤ) ∣ r)
    (P : Fock) (Q : ComplementFock) :
    mode r (join s hs (P ⊗ₜ[ℂ] Q)) =
      join s hs (P ⊗ₜ[ℂ] complementMode r Q) := by
  cases r with
  | ofNat r =>
    cases r with
    | zero => exact (hr (dvd_zero _)).elim
    | succ k =>
      have hk : ¬ 3 ∣ k + 1 := by
        change ¬ (3 : ℤ) ∣ ((k + 1 : ℕ) : ℤ) at hr
        exact_mod_cast hr
      simp only [mode, annihilate, complementMode, dite_eq_left hk, LinearMap.smul_apply]
      change (↑k + 1 : ℂ) • pderiv k (join s hs (P ⊗ₜ[ℂ] Q)) =
        join s hs (P ⊗ₜ[ℂ] ((↑k + 1 : ℂ) • pderiv (⟨k, hk⟩ : Complement) Q))
      have hd := pderiv_join_complement s hs ⟨k, hk⟩ P Q
      change pderiv k (join s hs (P ⊗ₜ[ℂ] Q)) = _ at hd
      rw [hd, TensorProduct.tmul_smul, map_smul]
  | negSucc k =>
    have hk : ¬ 3 ∣ k + 1 := by
      rw [Int.negSucc_eq, dvd_neg] at hr
      change ¬ (3 : ℤ) ∣ ((k + 1 : ℕ) : ℤ) at hr
      exact_mod_cast hr
    simp only [mode, create, complementMode, dite_eq_left hk, LinearMap.mulLeft_apply]
    have ht : ((1 : Fock) ⊗ₜ[ℂ] X (⟨k, hk⟩ : Complement)) * (P ⊗ₜ[ℂ] Q) =
        P ⊗ₜ[ℂ] (X (⟨k, hk⟩ : Complement) * Q) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [← ht, map_mul, join_one_tmul_X]

/-- The second-factor current intertwining on the entire tensor product. -/
theorem split_complementMode (s : ℂ) (hs : s ≠ 0) (r : ℤ) (hr : ¬ (3 : ℤ) ∣ r) :
    (split s hs).toLinearEquiv.conj (mode r) =
      TensorProduct.map LinearMap.id (complementMode r) := by
  apply TensorProduct.ext'
  intro P Q
  change split s hs (mode r (join s hs (P ⊗ₜ[ℂ] Q))) = _
  rw [mode_join_complement s hs r hr, TensorProduct.map_tmul, LinearMap.id_apply]
  exact (join s hs).symm_apply_apply _

/-- The smaller index stands to the left, so an annihilation mode acts first
when paired with a creation mode. -/
def complementPair (i j : ℤ) : Module.End ℂ ComplementFock :=
  if j ≤ i then (complementMode j).comp (complementMode i)
  else (complementMode i).comp (complementMode j)

private theorem normalPair_join_complement (s : ℂ) (hs : s ≠ 0) (i j : ℤ)
    (hi : ¬ (3 : ℤ) ∣ i) (hj : ¬ (3 : ℤ) ∣ j) (P : Fock) (Q : ComplementFock) :
    normalPair i j (join s hs (P ⊗ₜ[ℂ] Q)) =
      join s hs (P ⊗ₜ[ℂ] complementPair i j Q) := by
  by_cases h : j ≤ i
  · simp only [normalPair, complementPair, ite_eq_left h, LinearMap.comp_apply,
      mode_join_complement s hs i hi, mode_join_complement s hs j hj]
  · simp only [normalPair, complementPair, ite_eq_right h, LinearMap.comp_apply,
      mode_join_complement s hs j hj, mode_join_complement s hs i hi]

private def integerIndices : Set ℤ := {k | (3 : ℤ) ∣ k}

private theorem noninteger_partner (m k : ℤ) (hk : k ∈ integerIndicesᶜ) :
    ¬ (3 : ℤ) ∣ 3 * m - k := by
  intro h
  apply hk
  change (3 : ℤ) ∣ k
  have hd := dvd_sub (dvd_mul_right (3 : ℤ) m) h
  simpa using hd

private theorem nativePair_finiteSupport (n : ℤ) (P : Fock) :
    Function.HasFiniteSupport (fun k : ℤ => normalPair (n - k) k P) :=
  (Set.finite_Ioo _ _).subset (normalPair_support_interval n P)

private theorem complementPair_finiteSupport (m : ℤ) (Q : ComplementFock) :
    (integerIndicesᶜ ∩ Function.support
      (fun k : ℤ => complementPair (3 * m - k) k Q)).Finite := by
  have hfinite := nativePair_finiteSupport (3 * m)
    (join 1 one_ne_zero ((1 : Fock) ⊗ₜ[ℂ] Q))
  refine hfinite.subset ?_
  intro k hk
  change normalPair (3 * m - k) k (join 1 one_ne_zero ((1 : Fock) ⊗ₜ[ℂ] Q)) ≠ 0
  rw [normalPair_join_complement 1 one_ne_zero _ _ (noninteger_partner m k hk.1) hk.1,
    join_tmul, map_one, map_one, one_mul]
  intro h
  apply hk.2
  apply rename_injective _ Subtype.val_injective
  simpa only [map_zero] using h

private def coverShift (m : ℤ) : ℂ := if m = 0 then 1 / 9 else 0

/-- The pointwise finite normal-ordered sum over the two nonzero residue classes,
in the frequency convention r/3, with the cover vacuum shift. -/
def fractionalVirasoro (m : ℤ) : Module.End ℂ ComplementFock where
  toFun Q := (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ •
    ∑ᶠ k ∈ integerIndicesᶜ, complementPair (3 * m - k) k Q) + coverShift m • Q
  map_add' Q R := by
    simp only [map_add]
    rw [finsum_mem_add_distrib' (complementPair_finiteSupport m Q)
      (complementPair_finiteSupport m R)]
    simp only [smul_add]
    abel
  map_smul' a Q := by
    simp only [map_smul, RingHom.id_apply]
    have hsum : a • (∑ᶠ k ∈ integerIndicesᶜ, complementPair (3 * m - k) k Q) =
        ∑ᶠ k ∈ integerIndicesᶜ, a • complementPair (3 * m - k) k Q := by
      simpa only [DistribSMul.toAddMonoidHom_apply] using
        (DistribSMul.toAddMonoidHom ComplementFock a).map_finsum_mem'
          (complementPair_finiteSupport m Q)
    rw [← hsum, smul_comm (2 : ℂ)⁻¹ a, smul_comm (3 : ℂ)⁻¹ a, smul_comm (coverShift m) a,
      smul_add]

private theorem coverMode_apply (m : ℤ) (P : Fock) :
    coverMode m P =
      (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • ∑ᶠ k : ℤ, normalPair (3 * m - k) k P) + coverShift m • P := by
  simp only [coverMode, coverShift, one_div, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  rfl

private theorem cover_sub_integer_apply (m : ℤ) (P : Fock) :
    (coverMode m - integerSugawara m) P =
      (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • ∑ᶠ k ∈ integerIndicesᶜ, normalPair (3 * m - k) k P) +
        coverShift m • P := by
  let f (k : ℤ) := normalPair (3 * m - k) k P
  have hfinite := nativePair_finiteSupport (3 * m) P
  have hsum := finsum_mem_union' (f := f) (disjoint_compl_right (a := integerIndices))
    (hfinite.subset Set.inter_subset_right) (hfinite.subset Set.inter_subset_right)
  rw [Set.union_compl_self, finsum_mem_univ] at hsum
  rw [LinearMap.sub_apply, coverMode_apply, integerSugawara_apply]
  change (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • ∑ᶠ k, f k) + coverShift m • P -
      (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • ∑ᶠ k ∈ integerIndices, f k) = _
  rw [hsum]
  simp only [smul_add]
  abel

/-- Subtracting the integer Sugawara action leaves the shifted complement sum
on every pure tensor. -/
theorem cover_sub_integer_join_tmul (s : ℂ) (hs : s ≠ 0) (m : ℤ)
    (P : Fock) (Q : ComplementFock) :
    (coverMode m - integerSugawara m) (join s hs (P ⊗ₜ[ℂ] Q)) =
      join s hs (P ⊗ₜ[ℂ] fractionalVirasoro m Q) := by
  let J : ComplementFock →ₗ[ℂ] Fock := (join s hs).toLinearMap.comp
    (TensorProduct.mk ℂ Fock ComplementFock P)
  change (coverMode m - integerSugawara m) (J Q) = J (fractionalVirasoro m Q)
  rw [cover_sub_integer_apply]
  have hsum :
      (∑ᶠ k ∈ integerIndicesᶜ, normalPair (3 * m - k) k (J Q)) =
        J (∑ᶠ k ∈ integerIndicesᶜ, complementPair (3 * m - k) k Q) := by
    calc
      _ = ∑ᶠ k ∈ integerIndicesᶜ, J (complementPair (3 * m - k) k Q) := by
        apply finsum_mem_congr rfl
        intro k hk
        exact normalPair_join_complement s hs _ _ (noninteger_partner m k hk) hk P Q
      _ = _ := (J.toAddMonoidHom.map_finsum_mem' (complementPair_finiteSupport m Q)).symm
  rw [hsum]
  change _ = J ((3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ •
    ∑ᶠ k ∈ integerIndicesᶜ, complementPair (3 * m - k) k Q) + coverShift m • Q)
  rw [map_add, map_smul, map_smul, map_smul]

/-- The complement equality is an equality of endomorphisms on all split states. -/
theorem split_cover_sub_integer (s : ℂ) (hs : s ≠ 0) (m : ℤ) :
    (split s hs).toLinearEquiv.conj (coverMode m - integerSugawara m) =
      (fractionalVirasoro m).lTensor Fock := by
  apply TensorProduct.ext'
  intro P Q
  change split s hs ((coverMode m - integerSugawara m) (join s hs (P ⊗ₜ[ℂ] Q))) = _
  rw [cover_sub_integer_join_tmul, LinearMap.lTensor_tmul]
  exact (join s hs).symm_apply_apply _

/-- The covered Virasoro action on all states is the sum of the two factor actions. -/
theorem split_coverMode {s : ℂ} (hsq : s ^ 2 = 3) (m : ℤ) :
    (split s (ne_zero_of_sq_eq_three hsq)).toLinearEquiv.conj (coverMode m) =
      (L m).rTensor ComplementFock + (fractionalVirasoro m).lTensor Fock := by
  have h := split_cover_sub_integer s (ne_zero_of_sq_eq_three hsq) m
  rw [map_sub, split_integerSugawara hsq] at h
  exact eq_add_of_sub_eq' h

private theorem lTensor_injective :
    Function.Injective (LinearMap.lTensor Fock :
      Module.End ℂ ComplementFock → Module.End ℂ SplitFock) := by
  intro A B h
  apply LinearMap.ext
  intro Q
  have hw := DFunLike.congr_fun h ((1 : Fock) ⊗ₜ[ℂ] Q)
  simp only [LinearMap.lTensor_tmul] at hw
  have hv := congrArg (join 1 one_ne_zero) hw
  simp only [join_tmul, map_one, one_mul] at hv
  exact rename_injective _ Subtype.val_injective hv

private theorem tensor_commutator_add (A B : Module.End ℂ Fock)
    (C D : Module.End ℂ ComplementFock) :
    (A.rTensor ComplementFock + C.lTensor Fock) * (B.rTensor ComplementFock + D.lTensor Fock) -
      (B.rTensor ComplementFock + D.lTensor Fock) * (A.rTensor ComplementFock + C.lTensor Fock) =
        (A * B - B * A).rTensor ComplementFock + (C * D - D * C).lTensor Fock := by
  have commute (P : Module.End ℂ Fock) (Q : Module.End ℂ ComplementFock) :
      P.rTensor ComplementFock * Q.lTensor Fock = Q.lTensor Fock * P.rTensor ComplementFock := by
    change (P.rTensor ComplementFock).comp (Q.lTensor Fock) =
      (Q.lTensor Fock).comp (P.rTensor ComplementFock)
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  simp only [add_mul, mul_add, LinearMap.rTensor_sub, LinearMap.lTensor_sub,
    LinearMap.rTensor_mul, LinearMap.lTensor_mul, commute]
  abel

/-- The canonical complement modes satisfy the Virasoro commutation law at charge two. -/
theorem fractionalVirasoro_commutator (n m : ℤ) :
    fractionalVirasoro n * fractionalVirasoro m - fractionalVirasoro m * fractionalVirasoro n =
      ((n : ℂ) - (m : ℂ)) • fractionalVirasoro (n + m) +
        (if n + m = 0 then (2 * (((n : ℂ) ^ 3 - (n : ℂ)) / 12)) •
          (1 : Module.End ℂ ComplementFock) else 0) := by
  let E := (split sqrtThree (ne_zero_of_sq_eq_three sqrtThree_sq)).toLinearEquiv
  have hmul (A B : Module.End ℂ Fock) : E.conj (A * B) = E.conj A * E.conj B :=
    E.conj_comp B A
  have hsplit (j : ℤ) : E.conj (coverMode j) =
      (L j).rTensor ComplementFock + (fractionalVirasoro j).lTensor Fock :=
    split_coverMode sqrtThree_sq j
  have hone : E.conj (1 : Module.End ℂ Fock) = 1 := E.conj_id
  have h := congrArg E.conj (ThirdCoverVirasoro.coverMode_commutator n m)
  simp only [map_sub, hmul, map_add, map_smul, Int.cast_ofNat, mul_one, hsplit,
    tensor_commutator_add, PolynomialFockVirasoroCentral.L_commutator] at h
  apply lTensor_injective
  rw [LinearMap.lTensor_add, LinearMap.lTensor_smul]
  by_cases hz : n + m = 0
  · have hleftOne : LinearMap.rTensor ComplementFock (1 : Module.End ℂ Fock) = 1 :=
      LinearMap.rTensor_id ComplementFock Fock
    have hrightOne : LinearMap.lTensor Fock (1 : Module.End ℂ ComplementFock) = 1 :=
      LinearMap.lTensor_id Fock ComplementFock
    simp only [hz, ite_true, map_smul, hone, LinearMap.rTensor_add, LinearMap.rTensor_smul,
      hleftOne, LinearMap.lTensor_smul, hrightOne, smul_add] at h ⊢
    refine add_left_cancel (h.trans ?_)
    module
  · simp only [hz, ite_false, map_zero, add_zero, LinearMap.rTensor_smul,
      LinearMap.lTensor_zero, smul_add] at h ⊢
    exact add_left_cancel h

private theorem complementMode_vacuum (r : ℤ) (hr : 0 ≤ r) :
    complementMode r (1 : ComplementFock) = 0 := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  cases k with
  | zero => rfl
  | succ k =>
    change complementMode (Int.ofNat (k + 1)) 1 = 0
    simp only [complementMode]
    split <;> simp

/-- The constant polynomial is a highest-weight vacuum for the two fractional grids. -/
theorem fractionalVirasoro_vacuum (m : ℤ) (hm : 0 ≤ m) :
    fractionalVirasoro m (1 : ComplementFock) =
      (if m = 0 then (1 / 9 : ℂ) else 0) • (1 : ComplementFock) := by
  have hpair (k : ℤ) : complementPair (3 * m - k) k (1 : ComplementFock) = 0 := by
    by_cases hk : k ≤ 3 * m - k
    · simp only [complementPair, ite_eq_left hk, LinearMap.comp_apply,
        complementMode_vacuum (3 * m - k) (by omega), map_zero]
    · simp only [complementPair, ite_eq_right hk, LinearMap.comp_apply,
        complementMode_vacuum k (by omega), map_zero]
  change (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ •
    ∑ᶠ k ∈ integerIndicesᶜ, complementPair (3 * m - k) k (1 : ComplementFock)) + _ = _
  simp [hpair, coverShift]

/-- The current whose frequency is the native integer index divided by three. -/
def fractionalCurrent (r : ℤ) : Module.End ℂ ComplementFock :=
  sqrtThree⁻¹ • complementMode r

private theorem inverse_scale_sq : sqrtThree⁻¹ * sqrtThree⁻¹ = (3 : ℂ)⁻¹ := by
  rw [← pow_two, inv_pow, sqrtThree_sq]

/-- In normalized current coordinates the coefficient of the normal-ordered sum
is one half, and only pairs from the two complementary residue grids occur. -/
theorem fractionalVirasoro_apply (m : ℤ) (Q : ComplementFock) :
    fractionalVirasoro m Q =
      (2 : ℂ)⁻¹ • (∑ᶠ k ∈ {k : ℤ | ¬ (3 : ℤ) ∣ k},
        (if k ≤ 3 * m - k then fractionalCurrent k * fractionalCurrent (3 * m - k)
          else fractionalCurrent (3 * m - k) * fractionalCurrent k) Q) +
        (if m = 0 then (1 / 9 : ℂ) else 0) • Q := by
  have hterm (i j : ℤ) :
      (if j ≤ i then fractionalCurrent j * fractionalCurrent i
        else fractionalCurrent i * fractionalCurrent j) =
        (3 : ℂ)⁻¹ • complementPair i j := by
    by_cases h : j ≤ i
    · simp only [fractionalCurrent, complementPair, ite_eq_left h, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, smul_smul, inverse_scale_sq, Module.End.mul_eq_comp]
    · simp only [fractionalCurrent, complementPair, ite_eq_right h, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, smul_smul, inverse_scale_sq, Module.End.mul_eq_comp]
  change (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ •
    ∑ᶠ k ∈ integerIndicesᶜ, complementPair (3 * m - k) k Q) + coverShift m • Q = _
  simp only [hterm, LinearMap.smul_apply]
  have hsum :
      (3 : ℂ)⁻¹ • (∑ᶠ k ∈ integerIndicesᶜ, complementPair (3 * m - k) k Q) =
        ∑ᶠ k ∈ integerIndicesᶜ, (3 : ℂ)⁻¹ • complementPair (3 * m - k) k Q := by
    simpa only [DistribSMul.toAddMonoidHom_apply] using
      (DistribSMul.toAddMonoidHom ComplementFock (3 : ℂ)⁻¹).map_finsum_mem'
        (complementPair_finiteSupport m Q)
  change _ = (2 : ℂ)⁻¹ • (∑ᶠ k ∈ integerIndicesᶜ, (3 : ℂ)⁻¹ •
    complementPair (3 * m - k) k Q) + coverShift m • Q
  rw [← hsum, smul_comm (3 : ℂ)⁻¹ (2 : ℂ)⁻¹]

private theorem split_fractionalCurrent (r : ℤ) (hr : ¬ (3 : ℤ) ∣ r) :
    let E := (split sqrtThree (ne_zero_of_sq_eq_three sqrtThree_sq)).toLinearEquiv
    E.conj (ThirdCoverVirasoro.current sqrtThree⁻¹ r) = (fractionalCurrent r).lTensor Fock := by
  dsimp only
  rw [ThirdCoverVirasoro.current, map_smul, split_complementMode _ _ r hr, fractionalCurrent,
    LinearMap.lTensor_smul]
  rfl

/-- Opposite frequencies in the two fractional grids form the normalized
Heisenberg pairs on the complement polynomial Fock space. -/
theorem fractionalCurrent_commutator (r t : ℤ) (hr : ¬ (3 : ℤ) ∣ r)
    (ht : ¬ (3 : ℤ) ∣ t) :
    fractionalCurrent r * fractionalCurrent t - fractionalCurrent t * fractionalCurrent r =
      if r + t = 0 then ((r : ℂ) / 3) • (1 : Module.End ℂ ComplementFock) else 0 := by
  let E := (split sqrtThree (ne_zero_of_sq_eq_three sqrtThree_sq)).toLinearEquiv
  have hmul (A B : Module.End ℂ Fock) : E.conj (A * B) = E.conj A * E.conj B :=
    E.conj_comp B A
  have hcurrent (j : ℤ) (hj : ¬ (3 : ℤ) ∣ j) :
      E.conj (ThirdCoverVirasoro.current sqrtThree⁻¹ j) = (fractionalCurrent j).lTensor Fock :=
    split_fractionalCurrent j hj
  have h := (ThirdCoverVirasoro.current_commutator sqrtThree⁻¹ inverse_scale_sq r t).1
  have hsplit := congrArg E.conj h
  simp only [map_sub, hmul] at hsplit
  rw [hcurrent r hr, hcurrent t ht] at hsplit
  apply lTensor_injective
  rw [LinearMap.lTensor_sub, LinearMap.lTensor_mul, LinearMap.lTensor_mul]
  by_cases hrt : r + t = 0
  · have hone : E.conj (1 : Module.End ℂ Fock) = 1 := E.conj_id
    have htensor : LinearMap.lTensor Fock (1 : Module.End ℂ ComplementFock) = 1 :=
      LinearMap.lTensor_id Fock ComplementFock
    simpa only [hrt, ite_true, map_smul, hone, LinearMap.lTensor_smul, htensor] using hsplit
  · simpa only [hrt, ite_false, map_zero, LinearMap.lTensor_zero] using hsplit

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverComplement
