/- GID: D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: PPT channels with U(n₁)⊗U(n₂) symmetry are entanglement breaking after one composition. -/

/- Judgement:
   admission_basis: escape-witness (#14289).
   result has proof_shape: content; escape_witness: sOne_eq and sZero_eq (explicit finite
   decompositions of I + K and n I − K as nonnegative sums of Kronecker products of rank-one
   positive semidefinite matrices) and coeffs_nonneg (the polynomial certificate deriving the
   nonnegativity of the four separable coefficients of Φ ∘ Φ from the eight PPT inequalities).
   Definitions have proof_shape: not-applicable; escape_witness: null:
   chi; ex; pv; term; sOne; sZero; zeta; rootv; regroup; choi; grp; qf; kv; i0; i1; flat; claim.
   phi_comp (public; the map identity of the preregistered statement) has proof_shape:
   bind-only and is consumed by result. Every other theorem is private and consumed on the
   proof path of result:
   prod_I_single -> term_eq; sum_I_pow, term_eq, divides_iff -> char_sum;
   char_sum -> term_sum_apply; term_sum_apply, diag_sum_apply -> sOne_eq;
   zeta_prim -> conj_zeta_mul, sum_conj_rootv; conj_zeta_mul -> conj_rootv_mul_self, sum_conj_rootv;
   term_sum_apply, offdiag_sum_apply, conj_rootv_mul_self, sum_conj_rootv, card_filter_ne
     -> sZero_eq;
   term_posSemidef_left, term_posSemidef_right, sep_kron -> sep_term;
   sOne_eq, sep_sum, sep_term, single_posSemidef, sep_kron -> sep_sOne;
   sZero_eq, sep_sum, sep_term, single_posSemidef, sep_kron -> sep_sZero;
   reindex_kron_kron, sep_sum, sep_kron -> sep_regroup;
   map_apply_expand -> kron_kronecker; compl_apply, depol_depol -> depol_compl, compl_depol,
     compl_compl; kron_kronecker -> phi_kronecker;
   phi_kronecker, depol_depol, depol_compl, compl_depol, compl_compl -> phi_phi_kronecker;
   phi_phi_kronecker -> phi_comp;
   qf_add, qf_smul, qf_kron -> qf_four; star_omega -> qf_dmat_omega, qf_kmat_omega;
   qf_sub, qf_kmat_omega, qf_dmat_omega -> qf_qmat_omega;
   qf_single -> qf_dmat_e, qf_qmat_e, qf_ptd_s, qf_ptq_s; qf_diff -> qf_ptd_a, qf_ptq_a;
   i0_ne_i1 -> qf_qmat_e, qf_ptd_a, qf_ptq_a;
   qf_four, nonneg_of_qf, qf_dmat_omega, qf_qmat_omega, qf_dmat_e, qf_qmat_e -> cp_ineqs;
   pt_choi_reindex, qf_four, nonneg_of_qf, qf_ptd_s, qf_ptq_s, qf_ptd_a, qf_ptq_a -> pt_ineqs;
   dmat_eq_s, qmat_eq_s -> decomp;
   cp_ineqs, pt_ineqs, coeffs_nonneg, phi_comp, flat_eq, decomp, reindex_add', reindex_smul',
     sep_regroup, sep_sZero, sep_sOne -> result.
   Direct frozen dependencies (GID; statement_id): D5/S3/Resource/CompositeCones.separableCone,
   D5/S3/Resource/EntanglementWitness.separableCone_zero, .separableCone_add, .separableCone_smul,
   D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.partialTranspose,
   D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron_def;
   statement ids are listed in the delivery report.
   computational_content: none for every declaration: the statements concern arbitrary
   dimensions and real parameters, with no bounded enumeration, checker, numerical reduction or
   certified fixed instance.
-/

import D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum
import D5.S3.Resource.EntanglementWitness
import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Complex
open scoped BigOperators Kronecker ComplexOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness (separableCone_zero separableCone_add separableCone_smul)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

namespace D5.S3.Quantum.QuantumChannels.ProductUnitaryPPTSquared


/-- `[p = q ∧ r = s] + [p = r ∧ q = s] − [p = q = r = s]`. -/
private def chi {n : ℕ} (p q r s : Fin n) : ℂ :=
  (if p = q ∧ r = s then 1 else 0) + (if p = r ∧ q = s then 1 else 0) -
    (if p = q ∧ q = r ∧ r = s then 1 else 0)

/-- Exponent of the coordinate `m` in `θ_p θ̄_q θ̄_r θ_s`, with `conj I = I ^ 3`. -/
private def ex {n : ℕ} (p q r s m : Fin n) : ℕ :=
  (if p = m then 1 else 0) + 3 * (if q = m then 1 else 0) + 3 * (if r = m then 1 else 0) +
    (if s = m then 1 else 0)

private theorem sum_I_pow (e : ℕ) :
    ∑ t : Fin 4, I ^ ((t : ℕ) * e) = if e % 4 = 0 then 4 else 0 := by
  rw [Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_mul, pow_zero, one_mul]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3]
  have hI : ∀ k : ℕ, I ^ k = I ^ (k % 4) := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k 4, pow_add, pow_mul, I_pow_four, one_pow, one_mul]
  rw [hI e, hI (2 * e), hI (3 * e)]
  have : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : e % 4 <;> simp [Nat.mul_mod, h, pow_succ]
  norm_num

private theorem prod_I_single {n : ℕ} (θ : Fin n → Fin 4) (k : ℕ) (a : Fin n) :
    ∏ m, I ^ ((θ m : ℕ) * (k * if a = m then 1 else 0)) = I ^ ((θ a : ℕ) * k) := by
  rw [Finset.prod_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

private theorem term_eq {n : ℕ} (θ : Fin n → Fin 4) (p q r s : Fin n) :
    I ^ (θ p : ℕ) * (starRingEnd ℂ) (I ^ (θ q : ℕ)) * (starRingEnd ℂ) (I ^ (θ r : ℕ)) *
        I ^ (θ s : ℕ) = ∏ m, I ^ ((θ m : ℕ) * ex p q r s m) := by
  have hc : ∀ k : ℕ, (starRingEnd ℂ) (I ^ k) = I ^ (k * 3) := fun k => by
    rw [map_pow, conj_I, mul_comm, pow_mul]
    congr 1
    rw [pow_succ, I_sq]; ring
  have key : ∀ m, I ^ ((θ m : ℕ) * ex p q r s m) =
      I ^ ((θ m : ℕ) * (1 * if p = m then 1 else 0)) *
        I ^ ((θ m : ℕ) * (3 * if q = m then 1 else 0)) *
        I ^ ((θ m : ℕ) * (3 * if r = m then 1 else 0)) *
        I ^ ((θ m : ℕ) * (1 * if s = m then 1 else 0)) := by
    intro m
    simp only [ex, ← pow_add]
    congr 1
    ring
  rw [hc, hc, Finset.prod_congr rfl (fun m _ => key m)]
  simp only [Finset.prod_mul_distrib, prod_I_single, mul_one]

private theorem divides_iff {n : ℕ} (p q r s : Fin n) :
    (∀ m, ex p q r s m % 4 = 0) ↔ (p = q ∧ r = s) ∨ (p = r ∧ q = s) := by
  constructor
  · intro h
    have hp := h p
    have hq := h q
    have hr := h r
    have hs := h s
    simp only [ex, if_true] at hp hq hr hs
    split_ifs at hp hq hr hs <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) m <;> simp only [ex] <;> split_ifs <;> omega

private theorem char_sum {n : ℕ} (p q r s : Fin n) :
    ∑ θ : Fin n → Fin 4, I ^ (θ p : ℕ) * (starRingEnd ℂ) (I ^ (θ q : ℕ)) *
        (starRingEnd ℂ) (I ^ (θ r : ℕ)) * I ^ (θ s : ℕ) = 4 ^ n * chi p q r s := by
  simp only [term_eq]
  rw [← Fintype.prod_sum (fun m (t : Fin 4) => I ^ ((t : ℕ) * ex p q r s m))]
  simp only [sum_I_pow]
  rw [Finset.prod_ite_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [Finset.mem_univ, true_implies, divides_iff, chi]
  by_cases hA : p = q ∧ r = s
  · obtain ⟨rfl, rfl⟩ := hA
    by_cases hpr : p = r
    · subst hpr; simp
    · simp [hpr]
  · by_cases hB : p = r ∧ q = s
    · obtain ⟨rfl, rfl⟩ := hB
      have hpq : p ≠ q := fun h => hA ⟨h, h⟩
      simp [hpq]
    · have h3 : ¬(p = q ∧ q = r ∧ r = s) := fun h => hA ⟨h.1, h.2.2⟩
      simp [hA, hB, h3]

/-- The vector `m ↦ c m · I ^ θ m`. -/
private def pv {n : ℕ} (c : Fin n → ℂ) (θ : Fin n → Fin 4) : Fin n → ℂ := fun m => c m * I ^ (θ m : ℕ)

/-- One product term `pv c θ (pv c θ)* ⊗ conj(pv d θ) conj(pv d θ)*`. -/
private def term {n : ℕ} (c d : Fin n → ℂ) (θ : Fin n → Fin 4) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  vecMulVec (pv c θ) (star (pv c θ)) ⊗ₖ vecMulVec (star (pv d θ)) (pv d θ)

private theorem term_sum_apply {n : ℕ} (c d : Fin n → ℂ) (p r q s : Fin n) :
    (∑ θ, term c d θ) (p, r) (q, s) =
      4 ^ n * (c p * (starRingEnd ℂ) (c q) * ((starRingEnd ℂ) (d r) * d s)) * chi p q r s := by
  rw [show (4 : ℂ) ^ n * (c p * (starRingEnd ℂ) (c q) * ((starRingEnd ℂ) (d r) * d s)) *
      chi p q r s = (c p * (starRingEnd ℂ) (c q) * ((starRingEnd ℂ) (d r) * d s)) *
      (4 ^ n * chi p q r s) by ring, ← char_sum, Finset.mul_sum]
  simp only [Matrix.sum_apply, term, kroneckerMap_apply, vecMulVec_apply, pv, Pi.star_apply,
    RCLike.star_def, map_mul]
  refine Finset.sum_congr rfl fun θ _ => ?_
  ring

private theorem term_posSemidef_left {n : ℕ} (c : Fin n → ℂ) (θ : Fin n → Fin 4) :
    (vecMulVec (pv c θ) (star (pv c θ))).PosSemidef := posSemidef_vecMulVec_self_star _

private theorem term_posSemidef_right {n : ℕ} (d : Fin n → ℂ) (θ : Fin n → Fin 4) :
    (vecMulVec (star (pv d θ)) (pv d θ)).PosSemidef := posSemidef_vecMulVec_star_self _

/-- `I + K` on pairs. -/
private def sOne (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := 1 + kmat n

/-- `n I − K` on pairs. -/
private def sZero (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := (n : ℂ) • 1 - kmat n

private theorem diag_sum_apply {n : ℕ} (p r q s : Fin n) :
    (∑ i : Fin n, Matrix.single i i (1 : ℂ) ⊗ₖ Matrix.single i i 1) (p, r) (q, s) =
      if p = q ∧ q = r ∧ r = s then 1 else 0 := by
  simp only [Matrix.sum_apply, kroneckerMap_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single p (fun b _ hb => by simp [hb]) (by simp)]
  by_cases hpq : p = q <;> by_cases hqr : q = r <;> by_cases hrs : r = s <;> simp_all

private theorem sOne_eq (n : ℕ) :
    sOne n = ((1 : ℝ) / 4 ^ n) • ∑ θ, term (fun _ => 1) (fun _ => 1) θ +
      ∑ i : Fin n, Matrix.single i i (1 : ℂ) ⊗ₖ Matrix.single i i 1 := by
  ext ⟨p, r⟩ ⟨q, s⟩
  rw [Matrix.add_apply, Matrix.smul_apply, term_sum_apply, diag_sum_apply]
  simp only [sOne, kmat, omega, Matrix.add_apply, Matrix.one_apply, vecMulVec_apply, Prod.mk.injEq,
    map_one, mul_one, chi]
  have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Complex.real_smul]
  push_cast
  field_simp
  by_cases hpq : p = q <;> by_cases hrs : r = s <;> by_cases hpr : p = r <;> by_cases hqs : q = s <;>
    simp_all

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/
private def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / n)

/-- The character vector `m ↦ ζ ^ (k m)`. -/
private def rootv {n : ℕ} (k : Fin n) : Fin n → ℂ := fun m => zeta n ^ ((k : ℕ) * (m : ℕ))

private theorem zeta_prim {n : ℕ} (hn : 1 ≤ n) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n (by omega)

private theorem conj_zeta_mul {n : ℕ} (hn : 1 ≤ n) : (starRingEnd ℂ) (zeta n) * zeta n = 1 := by
  have h := (zeta_prim hn).norm'_eq_one (by omega)
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  norm_num

private theorem conj_rootv_mul_self {n : ℕ} (hn : 1 ≤ n) (k m : Fin n) :
    (starRingEnd ℂ) (rootv k m) * rootv k m = 1 := by
  simp only [rootv, map_pow, ← mul_pow, conj_zeta_mul hn, one_pow]

private theorem sum_conj_rootv {n : ℕ} (hn : 1 ≤ n) {p q : Fin n} (hpq : p ≠ q) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≠ ⟨0, hn⟩),
        (starRingEnd ℂ) (rootv k p) * rootv k q = -1 := by
  set x : ℂ := (starRingEnd ℂ) (zeta n) ^ (p : ℕ) * zeta n ^ (q : ℕ) with hx
  have hterm : ∀ k : Fin n, (starRingEnd ℂ) (rootv k p) * rootv k q = x ^ (k : ℕ) := by
    intro k
    simp only [rootv, map_pow, hx, mul_pow, ← pow_mul]
    ring_nf
  have hconj : (starRingEnd ℂ) (zeta n) = (zeta n)⁻¹ :=
    (eq_inv_of_mul_eq_one_left (conj_zeta_mul hn))
  have hz0 : zeta n ≠ 0 := Complex.exp_ne_zero _
  have hxn : x ^ n = 1 := by
    rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm (p : ℕ), mul_comm (q : ℕ), pow_mul, pow_mul,
      ← map_pow, (zeta_prim hn).pow_eq_one, map_one, one_pow, one_pow, one_mul]
  have hx1 : x ≠ 1 := by
    intro h1
    rw [hx, hconj, inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ hz0)] at h1
    exact hpq (Fin.ext ((zeta_prim hn).pow_inj p.2 q.2 h1))
  have hall : ∑ k : Fin n, (starRingEnd ℂ) (rootv k p) * rootv k q = 0 := by
    simp only [hterm]
    rw [Fin.sum_univ_eq_sum_range (fun i => x ^ i) n, geom_sum_eq hx1, hxn, sub_self, zero_div]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin n => k ≠ ⟨0, hn⟩)
    (fun k => (starRingEnd ℂ) (rootv k p) * rootv k q)
  rw [hall] at hsplit
  have hzero : ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ k ≠ ⟨0, hn⟩),
      (starRingEnd ℂ) (rootv k p) * rootv k q = 1 := by
    rw [Finset.sum_eq_single ⟨0, hn⟩ (fun b hb hb0 => by simp at hb; exact absurd hb hb0)
      (by simp)]
    simp [rootv]
  rw [hzero] at hsplit
  linear_combination hsplit

private theorem card_filter_ne {n : ℕ} (hn : 1 ≤ n) :
    ((Finset.univ.filter (fun k : Fin n => k ≠ ⟨0, hn⟩)).card : ℂ) = n - 1 := by
  rw [Finset.filter_ne' Finset.univ, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  push_cast [Nat.cast_sub hn]
  ring

private theorem offdiag_sum_apply {n : ℕ} (p r q s : Fin n) :
    (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, Matrix.single i i (1 : ℂ) ⊗ₖ Matrix.single j j 1)
        (p, r) (q, s) = if p = q ∧ r = s ∧ p ≠ r then 1 else 0 := by
  simp only [Matrix.sum_apply, kroneckerMap_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single p (fun b _ hb => by simp [hb]) (by simp)]
  by_cases hpr : p = r
  · subst hpr
    rw [Finset.sum_eq_zero (fun b hb => by
      simp only [Finset.mem_erase] at hb; simp [hb.1])]
    simp
  · rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp [Ne.symm hpr])]
    by_cases hpq : p = q <;> by_cases hrs : r = s <;> simp_all

private theorem sZero_eq {n : ℕ} (hn : 1 ≤ n) :
    sZero n = ((1 : ℝ) / 4 ^ n) •
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≠ ⟨0, hn⟩), ∑ θ, term (fun _ => 1) (rootv k) θ +
      ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, Matrix.single i i (1 : ℂ) ⊗ₖ Matrix.single j j 1 := by
  ext ⟨p, r⟩ ⟨q, s⟩
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, offdiag_sum_apply]
  simp only [term_sum_apply, map_one, mul_one, one_mul]
  have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Complex.real_smul]
  simp only [sZero, kmat, omega, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    vecMulVec_apply, Prod.mk.injEq, smul_eq_mul]
  by_cases hA : p = q ∧ r = s
  · obtain ⟨rfl, rfl⟩ := hA
    have hc : ∀ k ∈ Finset.univ.filter (fun k : Fin n => k ≠ ⟨0, hn⟩),
        4 ^ n * ((starRingEnd ℂ) (rootv k r) * rootv k r) * chi p p r r = 4 ^ n := by
      intro k _
      rw [conj_rootv_mul_self hn]
      by_cases hpr : p = r <;> simp [chi, hpr]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, card_filter_ne hn]
    by_cases hpr : p = r
    · subst hpr; push_cast; field_simp; simp
    · simp [hpr]; push_cast; field_simp; ring
  · by_cases hB : p = r ∧ q = s
    · obtain ⟨rfl, rfl⟩ := hB
      have hpq : p ≠ q := fun h => hA ⟨h, h⟩
      have hc : ∀ k ∈ Finset.univ.filter (fun k : Fin n => k ≠ ⟨0, hn⟩),
          4 ^ n * ((starRingEnd ℂ) (rootv k p) * rootv k q) * chi p q p q =
            4 ^ n * ((starRingEnd ℂ) (rootv k p) * rootv k q) := by
        intro k _
        simp [chi, hpq]
      rw [Finset.sum_congr rfl hc, ← Finset.mul_sum, sum_conj_rootv hn hpq]
      simp [hpq]
    · have hc : ∀ k ∈ Finset.univ.filter (fun k : Fin n => k ≠ ⟨0, hn⟩),
          4 ^ n * ((starRingEnd ℂ) (rootv k r) * rootv k s) * chi p q r s = 0 := by
        intro k _
        have h3 : ¬(p = q ∧ q = r ∧ r = s) := fun h => hA ⟨h.1, h.2.2⟩
        simp [chi, hA, hB, h3]
      rw [Finset.sum_congr rfl hc, Finset.sum_const_zero, mul_zero, zero_add]
      have hA' : ¬(p = q ∧ r = s ∧ p ≠ r) := fun h => hA ⟨h.1, h.2.1⟩
      rw [if_neg hA']
      by_cases hpq : p = q <;> by_cases hrs : r = s <;> by_cases hpr : p = r <;> by_cases hqs : q = s <;>
        simp_all

private theorem sep_kron {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : separableCone (A ⊗ₖ B) :=
  ⟨1, fun _ => A, fun _ => B, fun _ => ⟨hA, hB⟩, by simp⟩

private theorem sep_sum {m n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (h : ∀ i ∈ s, separableCone (f i)) :
    separableCone (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (separableCone_zero (m := m) (n := n))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact separableCone_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem single_posSemidef {n : ℕ} (i : Fin n) : (Matrix.single i i (1 : ℂ)).PosSemidef := by
  have : Matrix.single i i (1 : ℂ) = vecMulVec (Pi.single i 1) (star (Pi.single i 1)) := by
    ext a b
    simp only [Matrix.single_apply, vecMulVec_apply, Pi.star_apply, Pi.single_apply]
    by_cases ha : i = a <;> by_cases hb : i = b <;> simp [ha, hb, eq_comm]
  rw [this]
  exact posSemidef_vecMulVec_self_star _

private theorem sep_term {n : ℕ} (c d : Fin n → ℂ) (θ : Fin n → Fin 4) : separableCone (term c d θ) :=
  sep_kron (term_posSemidef_left c θ) (term_posSemidef_right d θ)

private theorem sep_sOne (n : ℕ) : separableCone (sOne n) := by
  rw [sOne_eq]
  refine separableCone_add (separableCone_smul (by positivity) (sep_sum _ _ fun θ _ => sep_term _ _ θ))
    (sep_sum _ _ fun i _ => sep_kron (single_posSemidef i) (single_posSemidef i))

private theorem sep_sZero {n : ℕ} (hn : 1 ≤ n) : separableCone (sZero n) := by
  rw [sZero_eq hn]
  refine separableCone_add (separableCone_smul (by positivity)
    (sep_sum _ _ fun k _ => sep_sum _ _ fun θ _ => sep_term _ _ θ))
    (sep_sum _ _ fun i _ => sep_sum _ _ fun j _ => sep_kron (single_posSemidef i) (single_posSemidef j))

/-- Regrouping `((a₁, b₁), (a₂, b₂)) ↦ ((a₁, a₂), (b₁, b₂))` followed by flattening. -/
private def regroup (n₁ n₂ : ℕ) :
    (Fin n₁ × Fin n₁) × (Fin n₂ × Fin n₂) ≃ Fin (n₁ * n₂) × Fin (n₁ * n₂) :=
  (Equiv.prodProdProdComm (Fin n₁) (Fin n₁) (Fin n₂) (Fin n₂)).trans
    (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)

private theorem reindex_kron_kron {n₁ n₂ : ℕ} (A B : Matrix (Fin n₁) (Fin n₁) ℂ)
    (A' B' : Matrix (Fin n₂) (Fin n₂) ℂ) :
    reindex (regroup n₁ n₂) (regroup n₁ n₂) ((A ⊗ₖ B) ⊗ₖ (A' ⊗ₖ B')) =
      reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ A') ⊗ₖ
        reindex finProdFinEquiv finProdFinEquiv (B ⊗ₖ B') := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  simp only [regroup, reindex_apply, submatrix_apply, kroneckerMap_apply, Equiv.symm_trans_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map, Equiv.prodProdProdComm_symm,
    Equiv.prodProdProdComm_apply]
  ring

private theorem sep_regroup {n₁ n₂ : ℕ} {X : Matrix (Fin n₁ × Fin n₁) (Fin n₁ × Fin n₁) ℂ}
    {Y : Matrix (Fin n₂ × Fin n₂) (Fin n₂ × Fin n₂) ℂ} (hX : separableCone X)
    (hY : separableCone Y) :
    separableCone (reindex (regroup n₁ n₂) (regroup n₁ n₂) (X ⊗ₖ Y)) := by
  obtain ⟨k, A, B, hAB, rfl⟩ := hX
  obtain ⟨l, A', B', hAB', rfl⟩ := hY
  have hsum : reindex (regroup n₁ n₂) (regroup n₁ n₂)
      ((∑ i : Fin k, A i ⊗ₖ B i) ⊗ₖ (∑ j : Fin l, A' j ⊗ₖ B' j)) =
      ∑ i : Fin k, ∑ j : Fin l,
        reindex (regroup n₁ n₂) (regroup n₁ n₂) ((A i ⊗ₖ B i) ⊗ₖ (A' j ⊗ₖ B' j)) := by
    ext a b
    simp only [reindex_apply, submatrix_apply, kroneckerMap_apply, Matrix.sum_apply,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hsum]
  refine sep_sum _ _ fun i _ => sep_sum _ _ fun j _ => ?_
  rw [reindex_kron_kron]
  refine sep_kron ?_ ?_
  · simpa [reindex_apply] using ((hAB i).1.kronecker (hAB' j).1).submatrix
      (finProdFinEquiv (m := n₁) (n := n₂)).symm
  · simpa [reindex_apply] using ((hAB i).2.kronecker (hAB' j).2).submatrix
      (finProdFinEquiv (m := n₁) (n := n₂)).symm

private theorem map_apply_expand {n : ℕ} (M : MatrixMap (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (u v : Fin n) : M X u v = ∑ a, ∑ a', X a a' * M (Matrix.single a a' 1) u v := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [show Matrix.single a a' (X a a') = X a a' • Matrix.single a a' (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, Matrix.smul_apply, smul_eq_mul]

private theorem kron_kronecker {n₁ n₂ : ℕ} (M₁ : MatrixMap (Fin n₁) (Fin n₁) ℂ)
    (M₂ : MatrixMap (Fin n₂) (Fin n₂) ℂ) (A : Matrix (Fin n₁) (Fin n₁) ℂ)
    (B : Matrix (Fin n₂) (Fin n₂) ℂ) :
    MatrixMap.kron M₁ M₂ (A ⊗ₖ B) = M₁ A ⊗ₖ M₂ B := by
  ext ⟨b, d⟩ ⟨b', d'⟩
  rw [MatrixMap.kron_def, kroneckerMap_apply, map_apply_expand M₁ A, map_apply_expand M₂ B]
  simp only [kroneckerMap_apply]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a₁ _ => ?_
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  refine Finset.sum_congr rfl fun c₁ _ => ?_
  refine Finset.sum_congr rfl fun c₂ _ => ?_
  ring

private theorem depol_depol {n : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) :
    depol n (depol n X) = depol n X := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [depol, LinearMap.coe_mk, AddHom.coe_mk, trace_smul, trace_one, Fintype.card_fin,
    smul_eq_mul]
  congr 1
  field_simp

private theorem compl_apply {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : ProductUnitaryChoiSpectrum.compl n X = X - depol n X := by
  simp [ProductUnitaryChoiSpectrum.compl]

private theorem depol_compl {n : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) :
    depol n (ProductUnitaryChoiSpectrum.compl n X) = 0 := by
  rw [compl_apply, map_sub, depol_depol hn, sub_self]

private theorem compl_depol {n : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) :
    ProductUnitaryChoiSpectrum.compl n (depol n X) = 0 := by
  rw [compl_apply, depol_depol hn, sub_self]

private theorem compl_compl {n : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) :
    ProductUnitaryChoiSpectrum.compl n (ProductUnitaryChoiSpectrum.compl n X) = ProductUnitaryChoiSpectrum.compl n X := by
  rw [compl_apply (ProductUnitaryChoiSpectrum.compl n X), depol_compl hn, sub_zero]

private theorem phi_kronecker {n₁ n₂ : ℕ} (a b c : ℂ) (A : Matrix (Fin n₁) (Fin n₁) ℂ)
    (B : Matrix (Fin n₂) (Fin n₂) ℂ) :
    phi n₁ n₂ a b c (A ⊗ₖ B) = depol n₁ A ⊗ₖ depol n₂ B + a • (depol n₁ A ⊗ₖ ProductUnitaryChoiSpectrum.compl n₂ B) +
      b • (ProductUnitaryChoiSpectrum.compl n₁ A ⊗ₖ depol n₂ B) + c • (ProductUnitaryChoiSpectrum.compl n₁ A ⊗ₖ ProductUnitaryChoiSpectrum.compl n₂ B) := by
  simp only [phi, LinearMap.add_apply, LinearMap.smul_apply, kron_kronecker]

private theorem phi_phi_kronecker {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (a b c a' b' c' : ℂ)
    (A : Matrix (Fin n₁) (Fin n₁) ℂ) (B : Matrix (Fin n₂) (Fin n₂) ℂ) :
    phi n₁ n₂ a b c (phi n₁ n₂ a' b' c' (A ⊗ₖ B)) = phi n₁ n₂ (a * a') (b * b') (c * c') (A ⊗ₖ B) := by
  rw [phi_kronecker a' b' c', map_add, map_add, map_add, map_smul, map_smul, map_smul,
    phi_kronecker, phi_kronecker, phi_kronecker, phi_kronecker, phi_kronecker]
  simp only [depol_depol hn₁, depol_depol hn₂, depol_compl hn₁, depol_compl hn₂, compl_depol hn₁,
    compl_depol hn₂, compl_compl hn₁, compl_compl hn₂, Matrix.zero_kronecker, Matrix.kronecker_zero,
    smul_zero, add_zero, zero_add]
  module

/-- The Choi matrix `Σ_{p,q} E_pq ⊗ Ψ(E_pq)`. -/
def choi {ι : Type*} [Fintype ι] [DecidableEq ι] (Ψ : MatrixMap ι ι ℂ) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  ∑ p : ι, ∑ q : ι, Matrix.single p q (1 : ℂ) ⊗ₖ Ψ (Matrix.single p q 1)

/-- Composition multiplies the three weights: in particular `Φ ∘ Φ` has the squared weights. -/
theorem phi_comp {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (a b c a' b' c' : ℂ) :
    phi n₁ n₂ a b c ∘ₗ phi n₁ n₂ a' b' c' = phi n₁ n₂ (a * a') (b * b') (c * c') := by
  apply LinearMap.ext
  intro X
  rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨p₁, p₂⟩ := p
  obtain ⟨q₁, q₂⟩ := q
  have hs : Matrix.single (p₁, p₂) (q₁, q₂) (X (p₁, p₂) (q₁, q₂)) =
      X (p₁, p₂) (q₁, q₂) • (Matrix.single p₁ q₁ (1 : ℂ) ⊗ₖ Matrix.single p₂ q₂ (1 : ℂ)) := by
    rw [Matrix.single_kronecker_single, mul_one, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul, LinearMap.comp_apply, phi_phi_kronecker hn₁ hn₂]

/-- The grouping `((p₁, p₂), (r₁, r₂)) ↦ ((p₁, r₁), (p₂, r₂))`. -/
private abbrev grp (n₁ n₂ : ℕ) :=
  Equiv.prodProdProdComm (Fin n₁) (Fin n₂) (Fin n₁) (Fin n₂)

private theorem pt_choi_reindex (n₁ n₂ : ℕ) (a b c : ℂ) :
    reindex (grp n₁ n₂) (grp n₁ n₂) (partialTranspose (choi (phi n₁ n₂ a b c))) =
      partialTranspose (dmat n₁) ⊗ₖ partialTranspose (dmat n₂) +
        a • (partialTranspose (dmat n₁) ⊗ₖ partialTranspose (qmat n₂)) +
        b • (partialTranspose (qmat n₁) ⊗ₖ partialTranspose (dmat n₂)) +
        c • (partialTranspose (qmat n₁) ⊗ₖ partialTranspose (qmat n₂)) := by
  ext ⟨⟨p₁, r₁⟩, ⟨p₂, r₂⟩⟩ ⟨⟨q₁, s₁⟩, ⟨q₂, s₂⟩⟩
  have h := congrArg (fun M => M ((p₁, s₁), (p₂, s₂)) ((q₁, r₁), (q₂, r₂)))
    (choi_reindex n₁ n₂ a b c)
  simp only [reindex_apply, submatrix_apply, Equiv.prodProdProdComm_symm,
    Equiv.prodProdProdComm_apply] at h
  simp only [grp, reindex_apply, submatrix_apply, Equiv.prodProdProdComm_symm,
    Equiv.prodProdProdComm_apply, partialTranspose, choi]
  rw [h]
  simp only [Matrix.add_apply, Matrix.smul_apply, kroneckerMap_apply, partialTranspose]

/-- The quadratic form `x* M x`. -/
private def qf {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (x : ι → ℂ) : ℂ := star x ⬝ᵥ (M *ᵥ x)

private theorem qf_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (x : ι → ℂ) :
    qf (A + B) x = qf A x + qf B x := by
  simp only [qf, Matrix.add_mulVec, dotProduct_add]

private theorem qf_smul {ι : Type*} [Fintype ι] (a : ℂ) (A : Matrix ι ι ℂ) (x : ι → ℂ) :
    qf (a • A) x = a * qf A x := by
  simp only [qf, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

private theorem qf_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (x : ι → ℂ) :
    qf (A - B) x = qf A x - qf B x := by
  simp only [qf, Matrix.sub_mulVec, dotProduct_sub]

/-- The product vector `(z₁, z₂) ↦ x z₁ · y z₂`. -/
private def kv {α β : Type*} (x : α → ℂ) (y : β → ℂ) : α × β → ℂ := fun z => x z.1 * y z.2

private theorem qf_kron {α β : Type*} [Fintype α] [Fintype β] (X : Matrix α α ℂ) (Y : Matrix β β ℂ)
    (x : α → ℂ) (y : β → ℂ) : qf (X ⊗ₖ Y) (kv x y) = qf X x * qf Y y := by
  have hmv : (X ⊗ₖ Y) *ᵥ kv x y = kv (X *ᵥ x) (Y *ᵥ y) := by
    ext ⟨i, j⟩
    simp only [mulVec, dotProduct, kv, kroneckerMap_apply, Fintype.sum_prod_type,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [qf, hmv, qf, qf]
  simp only [dotProduct, kv, Pi.star_apply, star_mul', Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem qf_single {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ι) :
    qf M (Pi.single u 1) = M u u := by
  simp [qf, mulVec_single_one, dotProduct_single]

private theorem qf_diff {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u v : ι) :
    qf M (Pi.single u 1 - Pi.single v 1) = M u u - M u v - M v u + M v v := by
  simp only [qf, Matrix.mulVec_sub, star_sub, dotProduct_sub, sub_dotProduct, mulVec_single_one,
    Pi.star_single, star_one, single_dotProduct, one_mul]
  simp only [Matrix.col_apply, transpose_apply]
  ring

private theorem star_omega (n : ℕ) : star (omega n) = omega n := by
  ext x
  simp only [omega, Pi.star_apply]
  split_ifs <;> simp

private theorem qf_dmat_omega {n : ℕ} (hn : 1 ≤ n) : qf (dmat n) (omega n) = 1 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [qf, dmat, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, star_omega,
    omega_dot_omega, smul_eq_mul]
  field_simp

private theorem qf_kmat_omega (n : ℕ) : qf (kmat n) (omega n) = (n : ℂ) ^ 2 := by
  simp only [qf, kmat, Matrix.vecMulVec_mulVec, star_omega, dotProduct_smul, omega_dot_omega,
    smul_eq_mul, op_smul_eq_mul]
  ring

/-- The index `0`. -/
private def i0 {n : ℕ} (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

/-- The index `1`. -/
private def i1 {n : ℕ} (hn : 2 ≤ n) : Fin n := ⟨1, by omega⟩

private theorem i0_ne_i1 {n : ℕ} (hn : 2 ≤ n) : i0 hn ≠ i1 hn := by
  simp [i0, i1, Fin.ext_iff]

private theorem qf_four {α β : Type*} [Fintype α] [Fintype β] (D₁ Q₁ : Matrix α α ℂ) (D₂ Q₂ : Matrix β β ℂ)
    (a b c : ℂ) (u : α → ℂ) (v : β → ℂ) :
    qf (D₁ ⊗ₖ D₂ + a • (D₁ ⊗ₖ Q₂) + b • (Q₁ ⊗ₖ D₂) + c • (Q₁ ⊗ₖ Q₂)) (kv u v) =
      qf D₁ u * qf D₂ v + a * (qf D₁ u * qf Q₂ v) + b * (qf Q₁ u * qf D₂ v) +
        c * (qf Q₁ u * qf Q₂ v) := by
  simp only [qf_add, qf_smul, qf_kron]

private theorem nonneg_of_qf {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (v : ι → ℂ)
    {r : ℝ} (h : qf M v = r) : 0 ≤ r := by
  have := hM.dotProduct_mulVec_nonneg v
  rw [← qf, h] at this
  exact_mod_cast this

private theorem qf_qmat_omega {n : ℕ} (hn : 1 ≤ n) : qf (qmat n) (omega n) = (n : ℂ) ^ 2 - 1 := by
  rw [qmat, qf_sub, qf_kmat_omega, qf_dmat_omega hn]

private theorem qf_dmat_e {n : ℕ} (hn : 2 ≤ n) :
    qf (dmat n) (Pi.single (i0 hn, i1 hn) 1) = 1 / n := by
  rw [qf_single]; simp [dmat]

private theorem qf_qmat_e {n : ℕ} (hn : 2 ≤ n) :
    qf (qmat n) (Pi.single (i0 hn, i1 hn) 1) = -(1 / n) := by
  rw [qf_single]; simp [qmat, kmat, dmat, omega, vecMulVec_apply, i0_ne_i1 hn]

private theorem qf_ptd_s {n : ℕ} (hn : 2 ≤ n) :
    qf (partialTranspose (dmat n)) (Pi.single (i0 hn, i0 hn) 1) = 1 / n := by
  rw [qf_single]; simp [partialTranspose, dmat]

private theorem qf_ptq_s {n : ℕ} (hn : 2 ≤ n) :
    qf (partialTranspose (qmat n)) (Pi.single (i0 hn, i0 hn) 1) = 1 - 1 / n := by
  rw [qf_single]; simp [partialTranspose, qmat, kmat, dmat, omega, vecMulVec_apply]

private theorem qf_ptd_a {n : ℕ} (hn : 2 ≤ n) :
    qf (partialTranspose (dmat n))
      (Pi.single (i0 hn, i1 hn) 1 - Pi.single (i1 hn, i0 hn) 1) = 2 / n := by
  have h := i0_ne_i1 hn
  rw [qf_diff]; simp [partialTranspose, dmat, h, Ne.symm h]; ring

private theorem qf_ptq_a {n : ℕ} (hn : 2 ≤ n) :
    qf (partialTranspose (qmat n))
      (Pi.single (i0 hn, i1 hn) 1 - Pi.single (i1 hn, i0 hn) 1) = -2 - 2 / n := by
  have h := i0_ne_i1 hn
  rw [qf_diff]; simp [partialTranspose, qmat, kmat, dmat, omega, vecMulVec_apply, h, Ne.symm h]; ring

private theorem cp_ineqs {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (x y z : ℝ)
    (h : (choi (phi n₁ n₂ x y z)).PosSemidef) :
    0 ≤ 1 + ((n₂ : ℝ) ^ 2 - 1) * x + ((n₁ : ℝ) ^ 2 - 1) * y + ((n₁ : ℝ) ^ 2 - 1) * ((n₂ : ℝ) ^ 2 - 1) * z ∧
    0 ≤ 1 - x + ((n₁ : ℝ) ^ 2 - 1) * y - ((n₁ : ℝ) ^ 2 - 1) * z ∧
    0 ≤ 1 + ((n₂ : ℝ) ^ 2 - 1) * x - y - ((n₂ : ℝ) ^ 2 - 1) * z ∧
    0 ≤ 1 - x - y + z := by
  have hr : (reindex (grp n₁ n₂) (grp n₁ n₂) (choi (phi n₁ n₂ x y z))).PosSemidef :=
    (posSemidef_submatrix_equiv (grp n₁ n₂).symm).mpr h
  rw [choi, choi_reindex] at hr
  have h1 : (1 : ℝ) ≤ n₁ := by exact_mod_cast (show 1 ≤ n₁ by omega)
  have h2 : (1 : ℝ) ≤ n₂ := by exact_mod_cast (show 1 ≤ n₂ by omega)
  have n1' : (n₁ : ℂ) ≠ 0 := by exact_mod_cast (show n₁ ≠ 0 by omega)
  have n2' : (n₂ : ℂ) ≠ 0 := by exact_mod_cast (show n₂ ≠ 0 by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine nonneg_of_qf hr (kv (omega n₁) (omega n₂)) ?_
    rw [qf_four, qf_dmat_omega (by omega), qf_dmat_omega (by omega), qf_qmat_omega (by omega),
      qf_qmat_omega (by omega)]
    push_cast; ring
  · have := nonneg_of_qf hr (kv (omega n₁) (Pi.single (i0 hn₂, i1 hn₂) 1))
      (r := (1 - x + ((n₁ : ℝ) ^ 2 - 1) * y - ((n₁ : ℝ) ^ 2 - 1) * z) / n₂) (by
        rw [qf_four, qf_dmat_omega (by omega), qf_qmat_omega (by omega), qf_dmat_e, qf_qmat_e]
        push_cast; field_simp; ring)
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by
      exfalso; have : (0 : ℝ) < n₂ := by linarith
      linarith [h.2])
  · have := nonneg_of_qf hr (kv (Pi.single (i0 hn₁, i1 hn₁) 1) (omega n₂))
      (r := (1 + ((n₂ : ℝ) ^ 2 - 1) * x - y - ((n₂ : ℝ) ^ 2 - 1) * z) / n₁) (by
        rw [qf_four, qf_dmat_omega (by omega), qf_qmat_omega (by omega), qf_dmat_e, qf_qmat_e]
        push_cast; field_simp; ring)
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by
      exfalso; have : (0 : ℝ) < n₁ := by linarith
      linarith [h.2])
  · have := nonneg_of_qf hr (kv (Pi.single (i0 hn₁, i1 hn₁) 1) (Pi.single (i0 hn₂, i1 hn₂) 1))
      (r := (1 - x - y + z) / (n₁ * n₂)) (by
        rw [qf_four, qf_dmat_e, qf_dmat_e, qf_qmat_e, qf_qmat_e]
        push_cast; field_simp; ring)
    have hpos : (0 : ℝ) < n₁ * n₂ := by positivity
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2])

private theorem pt_ineqs {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (x y z : ℝ)
    (h : (partialTranspose (choi (phi n₁ n₂ x y z))).PosSemidef) :
    0 ≤ 1 + ((n₂ : ℝ) - 1) * x + ((n₁ : ℝ) - 1) * y + ((n₁ : ℝ) - 1) * ((n₂ : ℝ) - 1) * z ∧
    0 ≤ 1 - ((n₂ : ℝ) + 1) * x + ((n₁ : ℝ) - 1) * y - ((n₁ : ℝ) - 1) * ((n₂ : ℝ) + 1) * z ∧
    0 ≤ 1 + ((n₂ : ℝ) - 1) * x - ((n₁ : ℝ) + 1) * y - ((n₁ : ℝ) + 1) * ((n₂ : ℝ) - 1) * z ∧
    0 ≤ 1 - ((n₂ : ℝ) + 1) * x - ((n₁ : ℝ) + 1) * y + ((n₁ : ℝ) + 1) * ((n₂ : ℝ) + 1) * z := by
  have hr : (reindex (grp n₁ n₂) (grp n₁ n₂)
      (partialTranspose (choi (phi n₁ n₂ x y z)))).PosSemidef :=
    (posSemidef_submatrix_equiv (grp n₁ n₂).symm).mpr h
  rw [pt_choi_reindex] at hr
  have n1' : (n₁ : ℂ) ≠ 0 := by exact_mod_cast (show n₁ ≠ 0 by omega)
  have n2' : (n₂ : ℂ) ≠ 0 := by exact_mod_cast (show n₂ ≠ 0 by omega)
  have hpos : (0 : ℝ) < n₁ * n₂ := by positivity
  set s₁ : Fin n₁ × Fin n₁ → ℂ := Pi.single (i0 hn₁, i0 hn₁) 1
  set s₂ : Fin n₂ × Fin n₂ → ℂ := Pi.single (i0 hn₂, i0 hn₂) 1
  set a₁ : Fin n₁ × Fin n₁ → ℂ := Pi.single (i0 hn₁, i1 hn₁) 1 - Pi.single (i1 hn₁, i0 hn₁) 1
  set a₂ : Fin n₂ × Fin n₂ → ℂ := Pi.single (i0 hn₂, i1 hn₂) 1 - Pi.single (i1 hn₂, i0 hn₂) 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := nonneg_of_qf hr (kv s₁ s₂)
      (r := (1 + ((n₂ : ℝ) - 1) * x + ((n₁ : ℝ) - 1) * y + ((n₁ : ℝ) - 1) * ((n₂ : ℝ) - 1) * z) /
        (n₁ * n₂)) (by
        rw [qf_four, qf_ptd_s, qf_ptd_s, qf_ptq_s, qf_ptq_s]
        push_cast; field_simp)
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2])
  · have := nonneg_of_qf hr (kv s₁ a₂)
      (r := 2 * (1 - ((n₂ : ℝ) + 1) * x + ((n₁ : ℝ) - 1) * y -
        ((n₁ : ℝ) - 1) * ((n₂ : ℝ) + 1) * z) / (n₁ * n₂)) (by
        rw [qf_four, qf_ptd_s, qf_ptq_s, qf_ptd_a, qf_ptq_a]
        push_cast; field_simp; ring)
    have := (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2])
    linarith
  · have := nonneg_of_qf hr (kv a₁ s₂)
      (r := 2 * (1 + ((n₂ : ℝ) - 1) * x - ((n₁ : ℝ) + 1) * y -
        ((n₁ : ℝ) + 1) * ((n₂ : ℝ) - 1) * z) / (n₁ * n₂)) (by
        rw [qf_four, qf_ptd_s, qf_ptq_s, qf_ptd_a, qf_ptq_a]
        push_cast; field_simp; ring)
    have := (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2])
    linarith
  · have := nonneg_of_qf hr (kv a₁ a₂)
      (r := 4 * (1 - ((n₂ : ℝ) + 1) * x - ((n₁ : ℝ) + 1) * y +
        ((n₁ : ℝ) + 1) * ((n₂ : ℝ) + 1) * z) / (n₁ * n₂)) (by
        rw [qf_four, qf_ptd_a, qf_ptd_a, qf_ptq_a, qf_ptq_a]
        push_cast; field_simp; ring)
    have := (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2])
    linarith

private theorem coeffs_nonneg {n₁ n₂ : ℝ} (h₁ : 2 ≤ n₁) (h₂ : 2 ≤ n₂) {x y z : ℝ}
    (hPP : 0 ≤ 1 + (n₂ ^ 2 - 1) * x + (n₁ ^ 2 - 1) * y + (n₁ ^ 2 - 1) * (n₂ ^ 2 - 1) * z)
    (hPQ : 0 ≤ 1 - x + (n₁ ^ 2 - 1) * y - (n₁ ^ 2 - 1) * z)
    (hQP : 0 ≤ 1 + (n₂ ^ 2 - 1) * x - y - (n₂ ^ 2 - 1) * z)
    (hQQ : 0 ≤ 1 - x - y + z)
    (hSS : 0 ≤ 1 + (n₂ - 1) * x + (n₁ - 1) * y + (n₁ - 1) * (n₂ - 1) * z)
    (hSA : 0 ≤ 1 - (n₂ + 1) * x + (n₁ - 1) * y - (n₁ - 1) * (n₂ + 1) * z)
    (hAS : 0 ≤ 1 + (n₂ - 1) * x - (n₁ + 1) * y - (n₁ + 1) * (n₂ - 1) * z)
    (hAA : 0 ≤ 1 - (n₂ + 1) * x - (n₁ + 1) * y + (n₁ + 1) * (n₂ + 1) * z) :
    0 ≤ 1 - (n₂ + 1) * x ^ 2 - (n₁ + 1) * y ^ 2 + (n₁ + 1) * (n₂ + 1) * z ^ 2 ∧
    0 ≤ 1 + (n₂ ^ 2 - 1) * x ^ 2 - (n₁ + 1) * y ^ 2 - (n₁ + 1) * (n₂ ^ 2 - 1) * z ^ 2 ∧
    0 ≤ 1 - (n₂ + 1) * x ^ 2 + (n₁ ^ 2 - 1) * y ^ 2 - (n₂ + 1) * (n₁ ^ 2 - 1) * z ^ 2 ∧
    0 ≤ 1 + (n₂ ^ 2 - 1) * x ^ 2 + (n₁ ^ 2 - 1) * y ^ 2 +
      (n₁ ^ 2 - 1) * (n₂ ^ 2 - 1) * z ^ 2 := by
  have a₁ : 0 ≤ n₁ - 2 := by linarith
  have a₂ : 0 ≤ n₂ - 2 := by linarith
  have c₁ : 0 ≤ n₁ - 1 := by linarith
  have c₂ : 0 ≤ n₂ - 1 := by linarith
  have d₁ : 0 ≤ n₁ + 1 := by linarith
  have d₂ : 0 ≤ n₂ + 1 := by linarith
  have b₁ : 0 ≤ n₁ ^ 2 - 1 := by nlinarith
  have b₂ : 0 ≤ n₂ ^ 2 - 1 := by nlinarith
  have p₁ : 0 < n₁ := by linarith
  have p₂ : 0 < n₂ := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hxu : 0 ≤ 1 - (n₂ + 1) * x := by
      have key : 2 * n₁ * (1 - (n₂ + 1) * x) =
          (n₁ + 1) * (1 - (n₂ + 1) * x + (n₁ - 1) * y - (n₁ - 1) * (n₂ + 1) * z) +
            (n₁ - 1) * (1 - (n₂ + 1) * x - (n₁ + 1) * y + (n₁ + 1) * (n₂ + 1) * z) := by ring
      have hr : 0 ≤ 2 * n₁ * (1 - (n₂ + 1) * x) := by
        rw [key]; exact add_nonneg (mul_nonneg d₁ hSA) (mul_nonneg c₁ hAA)
      exact (mul_nonneg_iff_of_pos_left (by linarith)).mp hr
    have hxl : 0 ≤ 1 + (n₂ + 1) * x := by
      have key : n₁ ^ 2 * (n₂ - 1) * (1 + (n₂ + 1) * x) =
          (1 + (n₂ ^ 2 - 1) * x + (n₁ ^ 2 - 1) * y + (n₁ ^ 2 - 1) * (n₂ ^ 2 - 1) * z) +
            (n₁ ^ 2 - 1) * (1 + (n₂ ^ 2 - 1) * x - y - (n₂ ^ 2 - 1) * z) + n₁ ^ 2 * (n₂ - 2) := by
        ring
      have hr : 0 ≤ n₁ ^ 2 * (n₂ - 1) * (1 + (n₂ + 1) * x) := by
        rw [key]
        exact add_nonneg (add_nonneg hPP (mul_nonneg b₁ hQP)) (mul_nonneg (sq_nonneg _) a₂)
      exact (mul_nonneg_iff_of_pos_left (mul_pos (by positivity) (by linarith))).mp hr
    have hyu : 0 ≤ 1 - (n₁ + 1) * y := by
      have key : 2 * n₂ * (1 - (n₁ + 1) * y) =
          (n₂ + 1) * (1 + (n₂ - 1) * x - (n₁ + 1) * y - (n₁ + 1) * (n₂ - 1) * z) +
            (n₂ - 1) * (1 - (n₂ + 1) * x - (n₁ + 1) * y + (n₁ + 1) * (n₂ + 1) * z) := by ring
      have hr : 0 ≤ 2 * n₂ * (1 - (n₁ + 1) * y) := by
        rw [key]; exact add_nonneg (mul_nonneg d₂ hAS) (mul_nonneg c₂ hAA)
      exact (mul_nonneg_iff_of_pos_left (by linarith)).mp hr
    have hyl : 0 ≤ 1 + (n₁ + 1) * y := by
      have key : n₂ ^ 2 * (n₁ - 1) * (1 + (n₁ + 1) * y) =
          (1 + (n₂ ^ 2 - 1) * x + (n₁ ^ 2 - 1) * y + (n₁ ^ 2 - 1) * (n₂ ^ 2 - 1) * z) +
            (n₂ ^ 2 - 1) * (1 - x + (n₁ ^ 2 - 1) * y - (n₁ ^ 2 - 1) * z) + n₂ ^ 2 * (n₁ - 2) := by
        ring
      have hr : 0 ≤ n₂ ^ 2 * (n₁ - 1) * (1 + (n₁ + 1) * y) := by
        rw [key]
        exact add_nonneg (add_nonneg hPP (mul_nonneg b₂ hPQ)) (mul_nonneg (sq_nonneg _) a₁)
      exact (mul_nonneg_iff_of_pos_left (mul_pos (by positivity) (by linarith))).mp hr
    have hx2 : (n₂ + 1) * ((n₂ + 1) * x ^ 2) ≤ 1 := by nlinarith [mul_nonneg hxu hxl]
    have hy2 : (n₁ + 1) * ((n₁ + 1) * y ^ 2) ≤ 1 := by nlinarith [mul_nonneg hyu hyl]
    have hx3 : 3 * ((n₂ + 1) * x ^ 2) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg d₂ (sq_nonneg x))) hx2
    have hy3 : 3 * ((n₁ + 1) * y ^ 2) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg d₁ (sq_nonneg y))) hy2
    nlinarith [mul_nonneg (mul_nonneg d₁ d₂) (sq_nonneg z)]
  · have key : 2 * n₁ ^ 2 * n₂ ^ 2 *
        (1 + (n₂ ^ 2 - 1) * x ^ 2 - (n₁ + 1) * y ^ 2 - (n₁ + 1) * (n₂ ^ 2 - 1) * z ^ 2) =
        4 * (1 + (n₂ ^ 2 - 1) * x + (n₁ ^ 2 - 1) * y + (n₁ ^ 2 - 1) * (n₂ ^ 2 - 1) * z) *
            (1 + (n₂ ^ 2 - 1) * x - y - (n₂ ^ 2 - 1) * z) +
          2 * (n₁ - 2) * (n₁ + 1) * (1 + (n₂ ^ 2 - 1) * x - y - (n₂ ^ 2 - 1) * z) ^ 2 +
          4 * (n₂ ^ 2 - 1) * (1 - x + (n₁ ^ 2 - 1) * y - (n₁ ^ 2 - 1) * z) * (1 - x - y + z) +
          2 * (n₁ - 2) * (n₁ + 1) * (n₂ ^ 2 - 1) * (1 - x - y + z) ^ 2 +
          n₁ * n₂ * ((n₂ + 1) * (1 + (n₂ - 1) * x + (n₁ - 1) * y + (n₁ - 1) * (n₂ - 1) * z) *
              (1 + (n₂ - 1) * x - (n₁ + 1) * y - (n₁ + 1) * (n₂ - 1) * z) +
            (n₂ - 1) * (1 - (n₂ + 1) * x + (n₁ - 1) * y - (n₁ - 1) * (n₂ + 1) * z) *
              (1 - (n₂ + 1) * x - (n₁ + 1) * y + (n₁ + 1) * (n₂ + 1) * z)) := by ring
    have hr : 0 ≤ 2 * n₁ ^ 2 * n₂ ^ 2 *
        (1 + (n₂ ^ 2 - 1) * x ^ 2 - (n₁ + 1) * y ^ 2 - (n₁ + 1) * (n₂ ^ 2 - 1) * z ^ 2) := by
      rw [key]
      have e₁ := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hPP) hQP
      have e₂ := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) a₁) d₁)
        (sq_nonneg (1 + (n₂ ^ 2 - 1) * x - y - (n₂ ^ 2 - 1) * z))
      have e₃ := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) b₂) hPQ) hQQ
      have e₄ := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) a₁) d₁)
        b₂) (sq_nonneg (1 - x - y + z))
      have e₅ := mul_nonneg (mul_nonneg p₁.le p₂.le)
        (add_nonneg (mul_nonneg (mul_nonneg d₂ hSS) hAS) (mul_nonneg (mul_nonneg c₂ hSA) hAA))
      linarith
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp hr
  · have key : 2 * n₁ ^ 2 * n₂ ^ 2 *
        (1 - (n₂ + 1) * x ^ 2 + (n₁ ^ 2 - 1) * y ^ 2 - (n₂ + 1) * (n₁ ^ 2 - 1) * z ^ 2) =
        4 * (1 + (n₂ ^ 2 - 1) * x + (n₁ ^ 2 - 1) * y + (n₁ ^ 2 - 1) * (n₂ ^ 2 - 1) * z) *
            (1 - x + (n₁ ^ 2 - 1) * y - (n₁ ^ 2 - 1) * z) +
          2 * (n₂ - 2) * (n₂ + 1) * (1 - x + (n₁ ^ 2 - 1) * y - (n₁ ^ 2 - 1) * z) ^ 2 +
          4 * (n₁ ^ 2 - 1) * (1 + (n₂ ^ 2 - 1) * x - y - (n₂ ^ 2 - 1) * z) * (1 - x - y + z) +
          2 * (n₁ ^ 2 - 1) * (n₂ - 2) * (n₂ + 1) * (1 - x - y + z) ^ 2 +
          n₁ * n₂ * ((n₁ + 1) * (1 + (n₂ - 1) * x + (n₁ - 1) * y + (n₁ - 1) * (n₂ - 1) * z) *
              (1 - (n₂ + 1) * x + (n₁ - 1) * y - (n₁ - 1) * (n₂ + 1) * z) +
            (n₁ - 1) * (1 + (n₂ - 1) * x - (n₁ + 1) * y - (n₁ + 1) * (n₂ - 1) * z) *
              (1 - (n₂ + 1) * x - (n₁ + 1) * y + (n₁ + 1) * (n₂ + 1) * z)) := by ring
    have hr : 0 ≤ 2 * n₁ ^ 2 * n₂ ^ 2 *
        (1 - (n₂ + 1) * x ^ 2 + (n₁ ^ 2 - 1) * y ^ 2 - (n₂ + 1) * (n₁ ^ 2 - 1) * z ^ 2) := by
      rw [key]
      have e₁ := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hPP) hPQ
      have e₂ := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) a₂) d₂)
        (sq_nonneg (1 - x + (n₁ ^ 2 - 1) * y - (n₁ ^ 2 - 1) * z))
      have e₃ := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) b₁) hQP) hQQ
      have e₄ := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) b₁) a₂)
        d₂) (sq_nonneg (1 - x - y + z))
      have e₅ := mul_nonneg (mul_nonneg p₁.le p₂.le)
        (add_nonneg (mul_nonneg (mul_nonneg d₁ hSS) hSA) (mul_nonneg (mul_nonneg c₁ hAS) hAA))
      linarith
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp hr
  · have := mul_nonneg b₂ (sq_nonneg x)
    have := mul_nonneg b₁ (sq_nonneg y)
    have := mul_nonneg (mul_nonneg b₁ b₂) (sq_nonneg z)
    linarith

private theorem dmat_eq_s {n : ℕ} (hn : 1 ≤ n) :
    dmat n = ((n : ℂ) * (n + 1))⁻¹ • (sZero n + sOne n) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℂ) + 1 ≠ 0 := by
    have : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
    exact_mod_cast this
  ext a b
  simp only [dmat, sZero, sOne, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp
  ring

private theorem qmat_eq_s {n : ℕ} (hn : 1 ≤ n) :
    qmat n = (n : ℂ)⁻¹ • (((n : ℂ) - 1) • sOne n + (-1 : ℂ) • sZero n) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  ext a b
  simp only [qmat, dmat, sZero, sOne, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    smul_eq_mul]
  field_simp
  ring

private theorem decomp {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (x y z : ℝ) :
    dmat n₁ ⊗ₖ dmat n₂ + ((x : ℂ) * x) • (dmat n₁ ⊗ₖ qmat n₂) +
        ((y : ℂ) * y) • (qmat n₁ ⊗ₖ dmat n₂) + ((z : ℂ) * z) • (qmat n₁ ⊗ₖ qmat n₂) =
      (((n₁ * (n₁ + 1) * (n₂ * (n₂ + 1)) : ℝ)⁻¹ *
          (1 - (n₂ + 1) * x ^ 2 - (n₁ + 1) * y ^ 2 + (n₁ + 1) * (n₂ + 1) * z ^ 2) : ℝ) : ℂ) •
          (sZero n₁ ⊗ₖ sZero n₂) +
        (((n₁ * (n₁ + 1) * (n₂ * (n₂ + 1)) : ℝ)⁻¹ *
          (1 + ((n₂ : ℝ) ^ 2 - 1) * x ^ 2 - (n₁ + 1) * y ^ 2 -
            (n₁ + 1) * ((n₂ : ℝ) ^ 2 - 1) * z ^ 2) : ℝ) : ℂ) • (sZero n₁ ⊗ₖ sOne n₂) +
        (((n₁ * (n₁ + 1) * (n₂ * (n₂ + 1)) : ℝ)⁻¹ *
          (1 - (n₂ + 1) * x ^ 2 + ((n₁ : ℝ) ^ 2 - 1) * y ^ 2 -
            (n₂ + 1) * ((n₁ : ℝ) ^ 2 - 1) * z ^ 2) : ℝ) : ℂ) • (sOne n₁ ⊗ₖ sZero n₂) +
        (((n₁ * (n₁ + 1) * (n₂ * (n₂ + 1)) : ℝ)⁻¹ *
          (1 + ((n₂ : ℝ) ^ 2 - 1) * x ^ 2 + ((n₁ : ℝ) ^ 2 - 1) * y ^ 2 +
            ((n₁ : ℝ) ^ 2 - 1) * ((n₂ : ℝ) ^ 2 - 1) * z ^ 2) : ℝ) : ℂ) • (sOne n₁ ⊗ₖ sOne n₂) := by
  have h₁ : (n₁ : ℂ) ≠ 0 := by exact_mod_cast (show n₁ ≠ 0 by omega)
  have h₂ : (n₂ : ℂ) ≠ 0 := by exact_mod_cast (show n₂ ≠ 0 by omega)
  have h₁' : (n₁ : ℂ) + 1 ≠ 0 := by
    have : ((n₁ + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show n₁ + 1 ≠ 0 by omega)
    exact_mod_cast this
  have h₂' : (n₂ : ℂ) + 1 ≠ 0 := by
    have : ((n₂ + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show n₂ + 1 ≠ 0 by omega)
    exact_mod_cast this
  rw [dmat_eq_s hn₁, dmat_eq_s hn₂, qmat_eq_s hn₁, qmat_eq_s hn₂]
  simp only [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.add_kronecker,
    Matrix.kronecker_add, smul_add, smul_smul]
  push_cast
  match_scalars <;> field_simp <;> ring

/-- Flattening of `Fin n₁ × Fin n₂` to `Fin (n₁ * n₂)` on the input and on the output. -/
def flat (n₁ n₂ : ℕ) :
    (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂) ≃ Fin (n₁ * n₂) × Fin (n₁ * n₂) :=
  Equiv.prodCongr finProdFinEquiv finProdFinEquiv

private theorem flat_eq (n₁ n₂ : ℕ) (M : Matrix ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂))
    ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) ℂ) :
    reindex (flat n₁ n₂) (flat n₁ n₂) M =
      reindex (regroup n₁ n₂) (regroup n₁ n₂) (reindex (grp n₁ n₂) (grp n₁ n₂) M) := by
  ext a b
  simp only [flat, regroup, grp, reindex_apply, submatrix_apply, Equiv.prodCongr_symm,
    Equiv.symm_trans_apply, Equiv.prodCongr_apply, Equiv.prodProdProdComm_symm,
    Equiv.prodProdProdComm_apply, Prod.map]

private theorem reindex_add' {α β : Type*} (e : α ≃ β) (A B : Matrix α α ℂ) :
    reindex e e (A + B) = reindex e e A + reindex e e B := by
  ext; simp [reindex_apply]

private theorem reindex_smul' {α β : Type*} (e : α ≃ β) (r : ℂ) (A : Matrix α α ℂ) :
    reindex e e (r • A) = r • reindex e e A := by
  ext; simp [reindex_apply]

/-- The PPT² statement for unital `U(n₁) ⊗ U(n₂)`-equivariant maps. -/
def claim : Prop :=
  ∀ n₁ n₂ : ℕ, 2 ≤ n₁ → 2 ≤ n₂ → ∀ l₀₁ l₁₀ l₁₁ : ℝ,
    (choi (phi n₁ n₂ l₀₁ l₁₀ l₁₁)).PosSemidef →
    (partialTranspose (choi (phi n₁ n₂ l₀₁ l₁₀ l₁₁))).PosSemidef →
    separableCone (reindex (flat n₁ n₂) (flat n₁ n₂)
      (choi (phi n₁ n₂ l₀₁ l₁₀ l₁₁ ∘ₗ phi n₁ n₂ l₀₁ l₁₀ l₁₁)))

theorem result : claim := by
  intro n₁ n₂ hn₁ hn₂ x y z hCP hPT
  obtain ⟨hPP, hPQ, hQP, hQQ⟩ := cp_ineqs hn₁ hn₂ x y z hCP
  obtain ⟨hSS, hSA, hAS, hAA⟩ := pt_ineqs hn₁ hn₂ x y z hPT
  have r₁ : (2 : ℝ) ≤ n₁ := by exact_mod_cast hn₁
  have r₂ : (2 : ℝ) ≤ n₂ := by exact_mod_cast hn₂
  obtain ⟨t₀₀, t₀₁, t₁₀, t₁₁⟩ := coeffs_nonneg r₁ r₂ hPP hPQ hQP hQQ hSS hSA hAS hAA
  have hc : 0 ≤ ((n₁ * (n₁ + 1) * (n₂ * (n₂ + 1)) : ℝ))⁻¹ := by positivity
  rw [phi_comp (by omega) (by omega), flat_eq, choi, choi_reindex, decomp (by omega) (by omega)]
  simp only [reindex_add', reindex_smul', Complex.coe_smul]
  refine separableCone_add (separableCone_add (separableCone_add ?_ ?_) ?_) ?_
  · exact separableCone_smul (mul_nonneg hc t₀₀) (sep_regroup (sep_sZero (by omega)) (sep_sZero (by omega)))
  · exact separableCone_smul (mul_nonneg hc t₀₁) (sep_regroup (sep_sZero (by omega)) (sep_sOne _))
  · exact separableCone_smul (mul_nonneg hc t₁₀) (sep_regroup (sep_sOne _) (sep_sZero (by omega)))
  · exact separableCone_smul (mul_nonneg hc t₁₁) (sep_regroup (sep_sOne _) (sep_sOne _))


end D5.S3.Quantum.QuantumChannels.ProductUnitaryPPTSquared
