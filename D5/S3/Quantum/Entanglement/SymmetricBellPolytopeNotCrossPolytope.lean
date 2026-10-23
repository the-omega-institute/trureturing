/- GID: D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.claim; result=D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.result; claim=D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.claim
   digest: The symmetric three-party Bell polytope at 17 inputs is not a cross-polytope. -/
/-
admission_basis: open-problem-resolution (#15186; Refuted)
The support module is same-delivery content.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
proof_shape: content: odd_frequency_norm_eq_iff, norm_maximizers_are_rotations, invariant_zero_second, invariant_reduce_total, invariant_total, invariant_basis_expansion, projection_formula, Gamma_ext, Gamma_shift, freq_unique_max, freqVertex_exposed, neg_freqVertex_exposed, projection_coords, coord_fullVertex, fullVertex_exposed, neg_fullVertex_exposed, coord_signedVertex, signedVertex_injective, signedVertex_extreme, coord_extraPoint, coord_candidateSet, extraPoint_outside, nineteen_extreme, result.
proof_shape: bind-only: Tensor, normIdx, reduceIdx, gen1, gen2, shiftParty, gen3, gen4, gen, act, act_add, act_smul, act_zero, symSub, Gamma, strategySet, localPolytope, crossPolytope, claim, freqIndex, freqIndex_val, freqSign, freqPhase, freqPhase_decomposition, freqSign_sign, freqIndex_injective, reindex_signedSum, odd_frequency_norm_le, sourceStrategy, integerBaseSigns, halfcircle_cos_sign, freqPhase_re, baseSigns_eq_integerBaseSigns, shiftStrategy, threshold_rotation, rotatedSigns_eq_integerRotatedSigns, zeta_primitive, frequency_coprime, frequency_order, zeta17_denom, threshold9_sum, baseSigns_sum, halfperiod_phase, residue_sum_injective, rotation_eval, rotatedSigns_neg, radius17_pos, affine_extreme_image, not_affine_cross_of_many_extreme, root_reduce, root_reflect, total, totalCoeff, basisCoeff, F, d, fullVertex, productCoeff, P, basis_inner_strategy, basisCoeff_orthogonal, basis_orthogonal, act_at_image, gen3_index_injective, gen4_index_injective, gen1_index_injective, gen2_index_injective, invariant_gen3, reduceIdx_self, reduceIdx_incr, reduceIdx_decr, gen3_tuple, invariant_tuple_step, invariant_gen1, invariant_gen2, invariant_swap_last, reduceIdx_reflect, gen4_zero_tuple, invariant_reflect, shortResidue, foldSign, basis_sum_apply, intNormIdx, intGen3, intGen4, basisCoeff_tuple, totalCoeff_add17, intNorm_incr, intNorm_decr, intGen3_tuple, intGen3_coeff, totalCoeff_sq, totalCoeff_sq_sum, residueCoeff, residueCoeff_reflect, neg_pow_cancel, totalCoeff_reflect, intNorm_reflect, intGen4_coeff, basisCoeff_sq_sum, basis_inner_self, cast_intNorm_sign, cast_intNorm_idx, gen3_int_bridge, gen4_int_bridge, basis_fixed, Gamma_inner_basis, basis_inner_expansion, a, b, c, abc, w, V, dot_wp, dot_wV, dot_wV_le, strategies_are_signs, realPoint, realVertex, ell, ell_realPoint, ell_realVertex, realPoint_outside, strategySet_finite, d_mem_strategySet, Gamma_hull, Gamma_d_mem, totalCoeff_add17_mul, totalCoeff_add34_mul, shiftIndex, shiftSign, shiftIndex_injective, shift_basis, evalAt_product, productCoeff_eval, P_eval, ellTensor, ellTensor_Gamma, bellRoot_anti, bellRoot_norm, evalAt_freq, baseSigns_formula, baseStrategy_eval, baseStrategy_sign, strategySet_as_d, d_neg_first, d_neg_second, d_neg_third, strategySet_neg, projected_strategySet_neg, sourceStrategy_last, altSum, altStrategy_sign, alt_terms_sign, altSum_bound, altSum_eq_pos, altSum_neg, altSum_eq_neg, evalAt_alt, alt_norm_max, alt_eval_norm_le, alt_unique_max, altVertex_generator, altVertex_value, altVertex_exposed, neg_altVertex_exposed, tensorCoords_basis, tensorCoords_expansion, thirdIndex, thirdIndex_total, productCoeff_double, intProductCoeff, productCoeff_cast, certificate_productCoeff, certificate_P, fullBaseSigns, baseSigns_eq_fullBaseSigns, intP2, P_cast_intP2, full_vertices_data_0, full_vertices_data_1, full_vertices_data_2, full_vertices_data_3, full_vertices_data_4, full_vertices_data_5, full_vertices_data_6, full_vertices_data_7, full_vertices_data_8, full_vertices_data, full_vertices_P, sourceStrategy_full, coordMap, signedVertex, signedIntVertex, candidateSet, signedInt_pair_injective, signedVertex_mem, extraPoint, extraPoint_mem.
escape_witness: odd_frequency_norm_eq_iff = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeSupport.threshold_of_no_alternation; norm_maximizers_are_rotations = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeSupport.threshold_of_no_alternation; invariant_zero_second = own construction/computation: induction reducing the second tensor index with the signed wrap transition; invariant_reduce_total = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; invariant_total = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; invariant_basis_expansion = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; projection_formula = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; Gamma_ext = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; Gamma_shift = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; freq_unique_max = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; freqVertex_exposed = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; neg_freqVertex_exposed = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; projection_coords = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; coord_fullVertex = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; fullVertex_exposed = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; neg_fullVertex_exposed = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; coord_signedVertex = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; signedVertex_injective = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; signedVertex_extreme = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; coord_extraPoint = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; coord_candidateSet = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; extraPoint_outside = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.invariant_zero_second; nineteen_extreme = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeSupport.threshold_of_no_alternation; result = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeSupport.threshold_of_no_alternation.
bind-only consumers: freqIndex_injective -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.reindex_signedSum, D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.odd_frequency_norm_eq_iff, D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.baseSigns_sum; reindex_signedSum -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.odd_frequency_norm_le, D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.odd_frequency_norm_eq_iff, D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.baseSigns_sum; odd_frequency_norm_le -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.freq_unique_max; threshold_rotation -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.norm_maximizers_are_rotations; frequency_coprime -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.frequency_order; frequency_order -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.freq_unique_max; baseSigns_sum -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.rotation_eval, D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.baseStrategy_eval; rotation_eval -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.freq_unique_max; totalCoeff_sq_sum -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.basisCoeff_sq_sum; basisCoeff_sq_sum -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.basis_inner_self; basis_inner_self -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.basis_inner_expansion; basis_inner_expansion -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.projection_formula, D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.Gamma_ext; dot_wp -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.ell_realPoint; dot_wV -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.dot_wV_le; dot_wV_le -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.ell_realVertex; strategies_are_signs -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.extraPoint_mem; ell_realPoint -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.realPoint_outside; ell_realVertex -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.realPoint_outside; realPoint_outside -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.extraPoint_outside; baseStrategy_eval -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.freqVertex_exposed, D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.neg_freqVertex_exposed; certificate_productCoeff -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.certificate_P; certificate_P -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.coord_extraPoint; full_vertices_data_0 -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.full_vertices_data; full_vertices_data_1 -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.full_vertices_data; full_vertices_data_2 -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.full_vertices_data; full_vertices_data_3 -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.full_vertices_data; full_vertices_data_4 -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.full_vertices_data; full_vertices_data_5 -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.full_vertices_data; full_vertices_data_6 -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.full_vertices_data; full_vertices_data_7 -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.full_vertices_data; full_vertices_data_8 -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.full_vertices_data; full_vertices_data -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.full_vertices_P; full_vertices_P -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.coord_fullVertex; signedInt_pair_injective -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.signedVertex_injective; extraPoint_mem -> D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.nineteen_extreme.
-/
import D5.S3.Quantum.Entanglement.SymmetricBellPolytopeSupport
import D5.S3.Combinatorics.Geometry.CrossPolytopeFaceCounts
import D5.S0.Asymptotics.Interference.FiniteAutocorrelation
import D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Sign
noncomputable section
open scoped BigOperators ComplexConjugate RealInnerProductSpace InnerProductSpace
open Set
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope
open D5.S3.Quantum.Entanglement.SymmetricBellPolytopeSupport
open D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation (zeta)
open D5.S0.Asymptotics.Interference.FiniteAutocorrelation (finiteSignal)
abbrev Tensor (N m : ℕ) := EuclideanSpace ℝ (Fin N → Fin m)
def normIdx (m : ℕ) (v : ℤ) : ℝ × ℕ := ((-1 : ℝ) ^ (v / (m : ℤ)), (v % (m : ℤ)).toNat)
def reduceIdx {m : ℕ} (x : Fin m) (v : ℤ) : ℝ × Fin m := ((normIdx m v).1, ⟨(normIdx m v).2, by
    have hm : (0 : ℤ) < m := by exact_mod_cast Nat.zero_lt_of_lt x.isLt
    have hlo := Int.emod_nonneg v hm.ne'; have hhi := Int.emod_lt_of_pos v hm; dsimp [normIdx]; exact (Int.toNat_lt_of_ne_zero (by omega)).mpr hhi⟩)
def gen1 {N m : ℕ} (x : Fin N → Fin m) : ℝ × (Fin N → Fin m) := (1, fun n => if h : 1 < N then x (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, h⟩ n) else x n)
def gen2 {N m : ℕ} (x : Fin N → Fin m) : ℝ × (Fin N → Fin m) := (1, fun n => x ((finRotate N).symm n))
def shiftParty {N m : ℕ} (x : Fin N → Fin m) (n : Fin N) : ℝ × Fin m := reduceIdx (x n) ((x n : ℤ) + if n.val = 0 then 1 else if n.val = 1 then -1 else 0)
def gen3 {N m : ℕ} (x : Fin N → Fin m) : ℝ × (Fin N → Fin m) := (∏ n, (shiftParty x n).1, fun n => (shiftParty x n).2)
def gen4 {N m : ℕ} (x : Fin N → Fin m) : ℝ × (Fin N → Fin m) := (∏ n, -(reduceIdx (x n) ((m : ℤ) - (x n : ℤ))).1, fun n => (reduceIdx (x n) ((m : ℤ) - (x n : ℤ))).2)
def gen {N m : ℕ} (i : Fin 4) : (Fin N → Fin m) → ℝ × (Fin N → Fin m) := ![gen1, gen2, gen3, gen4] i
def act {N m : ℕ} (g : (Fin N → Fin m) → ℝ × (Fin N → Fin m)) (p : Tensor N m) : Tensor N m := WithLp.toLp 2 (fun y => ∑ x, if (g x).2 = y then (g x).1 * p x else 0)
private lemma act_add {N m : ℕ} (g : (Fin N → Fin m) → ℝ × (Fin N → Fin m)) (p q : Tensor N m) : act g (p + q) = act g p + act g q := by apply PiLp.ext; intro y; simp only [act, PiLp.add_apply, PiLp.toLp_apply]; simp_rw [mul_add, ite_add_zero]; exact Finset.sum_add_distrib
private lemma act_smul {N m : ℕ} (g : (Fin N → Fin m) → ℝ × (Fin N → Fin m)) (c : ℝ) (p : Tensor N m) : act g (c • p) = c • act g p := by
  apply PiLp.ext; intro y; simp only [act, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x hx
  split_ifs <;> ring
private lemma act_zero {N m : ℕ} (g : (Fin N → Fin m) → ℝ × (Fin N → Fin m)) : act g (0 : Tensor N m) = 0 := by apply PiLp.ext; intro y; simp [act]
def symSub (N m : ℕ) : Submodule ℝ (Tensor N m) where
  carrier := {p | ∀ i : Fin 4, act (gen i) p = p}
  zero_mem' := fun _ => act_zero _
  add_mem' := by intro p q hp hq i; rw [act_add, hp i, hq i]
  smul_mem' := by   intro c p hp i; rw [act_smul, hp i]
def Gamma (N m : ℕ) : Tensor N m →L[ℝ] Tensor N m := (symSub N m).starProjection
private def strategySet (N m : ℕ) : Set (Tensor N m) := {v | ∃ a : Fin N → Fin m → ℝ, (∀ n x, a n x = 1 ∨ a n x = -1) ∧ ∀ x, v x = ∏ n, a n (x n)}
def localPolytope (N m : ℕ) : Set (Tensor N m) := convexHull ℝ (strategySet N m)
def crossPolytope (k : ℕ) : Set (EuclideanSpace ℝ (Fin k)) := (EuclideanSpace.equiv (Fin k) ℝ).symm ''
    D5.S3.Combinatorics.Geometry.CrossPolytopeFaceCounts.crossHull Finset.univ
def claim : Prop := ∀ N m : ℕ, 3 ≤ N → 2 ≤ m →
  ∃ f : Tensor N m →ᵃ[ℝ] EuclideanSpace ℝ (Fin ((m + 1) / 2)),
    Set.InjOn f (Gamma N m '' localPolytope N m) ∧
      f '' (Gamma N m '' localPolytope N m) = crossPolytope ((m + 1) / 2)
private def freqIndex (j : ℕ) (x : Fin 17) : Fin 17 := (Fin.ofNat 17 j) * x
private lemma freqIndex_val (j : ℕ) (x : Fin 17) : (freqIndex j x).val = (j * x.val) % 17 := by simp [freqIndex, Fin.val_mul, Fin.val_ofNat, Nat.mod_mul_mod]
private def freqSign (j : ℕ) (x : Fin 17) : ℝ := (-1) ^ (j * x.val / 17)
private def freqPhase (j : ℕ) (x : Fin 17) : ℂ := zeta 17 ^ (j * x.val)
private lemma freqPhase_decomposition (j : ℕ) (x : Fin 17) : freqPhase j x = (freqSign j x : ℂ) * phase 17 (freqIndex j x) := by
  have hdecomp := Nat.mod_add_div (j * x.val) 17; dsimp [freqPhase, freqSign]; rw [phase_pow]; simp only [freqIndex_val]; change zeta 17 ^ (j * x.val) = ↑((-1 : ℝ) ^ (j * x.val / 17)) *
    zeta 17 ^ ((j * x.val) % 17)
  nth_rw 1 [← hdecomp]
  rw [pow_add, pow_mul, zeta_pow_card (by norm_num)]; push_cast; ring
private lemma freqSign_sign (j : ℕ) (x : Fin 17) : freqSign j x = 1 ∨ freqSign j x = -1 := by dsimp [freqSign]; exact neg_one_pow_eq_or (R := ℝ) _
private lemma freqIndex_injective (j : Fin 8) : Function.Injective (freqIndex (2 * j.val + 1)) := by fin_cases j <;> decide
private lemma reindex_signedSum (j : Fin 8) (a : Fin 17 → ℝ) : ∃ b : Fin 17 → ℝ, (IsSign a → IsSign b) ∧ dotProduct (fun i => (a i : ℂ)) (freqPhase (2 * j.val + 1)) = dotProduct (fun i => (b i : ℂ)) (phase 17) ∧ ∀ x, b (freqIndex (2*j.val+1) x) = a x * freqSign (2*j.val+1) x := by
  classical
  let e : Fin 17 ≃ Fin 17 := Equiv.ofBijective (freqIndex (2 * j.val + 1))
    ⟨freqIndex_injective j, Finite.surjective_of_injective (freqIndex_injective j)⟩
  let b : Fin 17 → ℝ := fun y => a (e.symm y) * freqSign (2 * j.val + 1) (e.symm y)
  refine ⟨b, ?_, ?_, ?_⟩
  · intro ha y; rcases ha (e.symm y) with h | h <;>
      rcases freqSign_sign (2*j.val+1) (e.symm y) with hs | hs <;> simp [b, h, hs]
  · dsimp [dotProduct]; rw [← Equiv.sum_comp e (fun y => (b y : ℂ) * phase 17 y)]; apply Finset.sum_congr rfl; intro x hx; simp only [b, Equiv.symm_apply_apply]; rw [freqPhase_decomposition]; change (a x : ℂ) * ((freqSign (2*j.val+1) x : ℂ) * phase 17 (e x)) =
      ((a x * freqSign (2*j.val+1) x : ℝ) : ℂ) * phase 17 (e x)
    push_cast; ring
  · intro x; change b (e x) = a x * freqSign (2*j.val+1) x; simp [b]
private lemma odd_frequency_norm_le (j : Fin 8) (a : Fin 17 → ℝ) (ha : IsSign a) : ‖dotProduct (fun i => (a i : ℂ)) (freqPhase (2*j.val+1))‖ ≤ radius 17 := by obtain ⟨b, hb, he, _⟩ := reindex_signedSum j a; rw [he]; exact sharp_norm_le (by norm_num) b (hb ha)
private lemma odd_frequency_norm_eq_iff (j : Fin 8) (a : Fin 17 → ℝ) (ha : IsSign a) : ‖dotProduct (fun i => (a i : ℂ)) (freqPhase (2*j.val+1))‖ = radius 17 ↔ ∃ k : ℕ, k ≤ 17 ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ x, a x = freqSign (2*j.val+1) x * threshold 17 k s (freqIndex (2*j.val+1) x) := by
  obtain ⟨b,hb,he,hpoint⟩ := reindex_signedSum j a; rw [he]; constructor
  · intro h; obtain ⟨k,hk,s,hs,hform⟩ := (sharp_norm_eq_iff (by norm_num) b (hb ha)).mp h
    refine ⟨k,hk,s,hs,?_⟩
    intro x; have hx := hpoint x; rw [hform (freqIndex (2*j.val+1) x)] at hx; rcases freqSign_sign (2*j.val+1) x with hp | hp <;>
      rw [hp] at hx ⊢ <;> dsimp [threshold] at * <;> linarith
  · rintro ⟨k,hk,s,hs,hform⟩
    have hbform : b = threshold 17 k s := by funext y; obtain ⟨x,rfl⟩ := Finite.surjective_of_injective (freqIndex_injective j) y; rw [hpoint, hform x]; rcases freqSign_sign (2*j.val+1) x with hp | hp <;> rw [hp] <;> ring
    rw [hbform]; exact threshold_norm (by norm_num) k hk s hs
private def sourceStrategy (j : Fin 9) (x : Fin 17) : ℝ := Real.sign (Real.cos (Real.pi*(2*j.val+1)*x.val/17))
private def integerBaseSigns (j : Fin 8) (x : Fin 17) : ℤ := (-1) ^ ((2*j.val+1)*x.val/17) *
    (if ((2*j.val+1)*x.val)%17 < 9 then 1 else -1)
private lemma halfcircle_cos_sign (x : Fin 17) : (x.val<9 → 0<Real.cos (Real.pi/17*x.val)) ∧ (¬x.val<9 → Real.cos (Real.pi/17*x.val)<0) := by
  constructor
  · intro hx; have hxr : (x.val : ℝ)≤8 := by exact_mod_cast (show x.val≤8 by omega)
    have hx0 : (0 : ℝ)≤x.val := Nat.cast_nonneg _; apply Real.cos_pos_of_mem_Ioo; constructor <;> nlinarith [Real.pi_pos,mul_nonneg hx0 Real.pi_pos.le, mul_le_mul_of_nonneg_right hxr Real.pi_pos.le]
  · intro hx; have hxr : (9 : ℝ)≤x.val := by exact_mod_cast (show 9≤x.val by omega)
    have hxhi : (x.val : ℝ)≤16 := by exact_mod_cast (show x.val≤16 by omega)
    apply Real.cos_neg_of_pi_div_two_lt_of_lt <;>
      nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_right hxr Real.pi_pos.le, mul_le_mul_of_nonneg_right hxhi Real.pi_pos.le]
private lemma freqPhase_re (j : ℕ) (x : Fin 17) : (freqPhase j x).re=Real.cos (Real.pi*j*x.val/17) := by
  have he : freqPhase j x=Complex.exp (Complex.ofReal (Real.pi*j*x.val/17)*Complex.I) := by dsimp [freqPhase,zeta]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [he,Complex.exp_ofReal_mul_I_re]
private lemma baseSigns_eq_integerBaseSigns (j : Fin 8) (x : Fin 17) :
    (sourceStrategy (Fin.castLE (by decide) j)) x = (integerBaseSigns j x : ℝ) := by
  have hc : Real.cos (Real.pi*(2*j.val+1)*x.val/17)=
      freqSign (2*j.val+1) x*Real.cos (Real.pi/17*(freqIndex (2*j.val+1) x).val) := by
    have hh := freqPhase_re (2*j.val+1) x
    push_cast at hh; rw [← hh,freqPhase_decomposition,Complex.mul_re]; simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    have hp : phase 17 (freqIndex (2*j.val+1) x) = freqPhase 1 (freqIndex (2*j.val+1) x) := by simp [phase, freqPhase]
    rw [hp, freqPhase_re]; congr 2; norm_num; ring
  have he : (integerBaseSigns j x : ℝ)=freqSign (2*j.val+1) x*
      (if (freqIndex (2*j.val+1) x).val<9 then (1:ℝ) else -1) := by
    by_cases hlt : ((2*j.val+1)*x.val)%17<9
    · simp [integerBaseSigns,freqSign,freqIndex_val,hlt]
    · simp [integerBaseSigns,freqSign,freqIndex_val,hlt]
  simp only [sourceStrategy, Fin.coe_castLE]; rw [hc, he]; have hs := halfcircle_cos_sign (freqIndex (2*j.val+1) x); rcases freqSign_sign (2*j.val+1) x with hsign | hsign <;>
    rw [hsign] <;> by_cases hlt : (freqIndex (2*j.val+1) x).val<9
  · have hp := hs.1 hlt; simp only [one_mul]; rw [Real.sign_of_pos hp]; simp [hlt]
  · have hn := hs.2 hlt; simp only [one_mul]; rw [Real.sign_of_neg hn]; simp [hlt]
  · have hp := hs.1 hlt; simp only [neg_one_mul]; rw [Real.sign_of_neg (neg_lt_zero.mpr hp)]; simp [hlt]
  · have hn := hs.2 hlt; simp only [neg_one_mul]; rw [Real.sign_of_pos (neg_pos.mpr hn)]; simp [hlt]
private def shiftStrategy {R : Type*} [Ring R] (t : ℕ) (a : Fin 17 → R) : Fin 17 → R := fun x => (-1)^((x.val+t)/17)*a ⟨(x.val+t)%17,by omega⟩
private lemma threshold_rotation (j : Fin 8) (k : Fin 18) : ∃ t : Fin 34, ∀ x : Fin 17, (-1 : ℤ) ^ ((2*j.val+1)*x.val/17) * (if ((2*j.val+1)*x.val)%17 < k.val then 1 else -1) = (fun (t : Fin 34) => shiftStrategy t.val (integerBaseSigns j)) t x := by
  let witness : Fin 8 → Fin 18 → Fin 34 := ![ ![9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 33, 32, 31, 30, 29, 28, 27, 26], ![3, 14, 25, 2, 13, 24, 1, 12, 23, 0, 11, 22, 33, 10, 21, 32, 9, 20], ![29, 22, 15, 8, 1, 28, 21, 14, 7, 0, 27, 20, 13, 6, 33, 26, 19, 12], ![11, 6, 1, 30, 25, 20, 15, 10, 5, 0, 29, 24, 19, 14, 9, 4, 33, 28],
    ![1, 16, 31, 12, 27, 8, 23, 4, 19, 0, 15, 30, 11, 26, 7, 22, 3, 18],
    ![7, 10, 13, 16, 19, 22, 25, 28, 31, 0, 3, 6, 9, 12, 15, 18, 21, 24],
    ![19, 32, 11, 24, 3, 16, 29, 8, 21, 0, 13, 26, 5, 18, 31, 10, 23, 2],
    ![21, 30, 5, 14, 23, 32, 7, 16, 25, 0, 9, 18, 27, 2, 11, 20, 29, 4]]
  refine ⟨witness j k, ?_⟩
  revert j k
  decide
private lemma rotatedSigns_eq_integerRotatedSigns (j : Fin 8) (t : Fin 34) (x : Fin 17) :
    (fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) t x = ((fun (t : Fin 34) => shiftStrategy t.val (integerBaseSigns j)) t x : ℝ) := by
  simp only [shiftStrategy, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]; rw [baseSigns_eq_integerBaseSigns]
private lemma zeta_primitive : IsPrimitiveRoot (zeta 17) 34 := by
  have he : zeta 17 = Complex.exp (2 * Real.pi * Complex.I / 34) := by congr 1; dsimp [zeta]; push_cast; ring
  rw [he]; exact Complex.isPrimitiveRoot_exp 34 (by decide)
private lemma frequency_coprime (j : Fin 8) : (2*j.val+1).Coprime 34 := by fin_cases j <;> decide
private lemma frequency_order (j : Fin 8) (t : ℕ) : zeta 17 ^ ((2*j.val+1)*t) = 1 → 34 ∣ t := by intro ht; have hd := zeta_primitive.dvd_of_pow_eq_one _ ht; exact (frequency_coprime j).symm.dvd_of_dvd_mul_left hd
private lemma zeta17_denom : zeta 17 - 1 = (2 * Real.sin (Real.pi/34) : ℝ) * zeta 17 ^ 9 := by
  have hz : zeta 17 = Complex.exp (((Real.pi / 17 : ℝ) : ℂ) * Complex.I) := by unfold zeta; congr 1; push_cast; ring
  have hz9 : zeta 17 ^ 9 = Complex.exp (((Real.pi/2+Real.pi/34 : ℝ) : ℂ)*Complex.I) := by dsimp [zeta]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have ha : Real.pi/17 = 2*(Real.pi/34) := by ring
  rw [hz9]; apply Complex.ext
  · simp only [hz,Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re, Complex.ofReal_im,zero_mul,sub_zero,Complex.exp_ofReal_mul_I_re]; norm_num only [Nat.cast_ofNat]; rw [ha,Real.cos_two_mul,Real.cos_add,Real.cos_pi_div_two,Real.sin_pi_div_two]; nlinarith [Real.sin_sq_add_cos_sq (Real.pi/34)]
  · simp only [hz,Complex.sub_im,Complex.one_im,Complex.mul_im,Complex.ofReal_re, Complex.ofReal_im,zero_mul,add_zero,sub_zero,Complex.exp_ofReal_mul_I_im]; norm_num only [Nat.cast_ofNat]; rw [ha,Real.sin_two_mul,Real.sin_add,Real.cos_pi_div_two,Real.sin_pi_div_two]; ring
private lemma threshold9_sum : dotProduct (fun i => ((threshold 17 9 1) i : ℂ)) (phase 17) = (radius 17 : ℂ) := by
  rw [threshold_sum (by norm_num) 9 (by norm_num),zeta17_denom]; have hs : Real.sin (Real.pi/34) ≠ 0 := by apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hz : zeta 17 ≠ 0 := Complex.exp_ne_zero _; dsimp [radius]; norm_num; push_cast; field_simp
private lemma baseSigns_sum (j : Fin 8) : dotProduct (fun i => ((fun x => (sourceStrategy (Fin.castLE (by decide) j)) x) i : ℂ)) (freqPhase (2*j.val+1)) = (radius 17 : ℂ) := by
  obtain ⟨b,_,he,hb⟩ := reindex_signedSum j (fun x => (sourceStrategy (Fin.castLE (by decide) j)) x); have hform : b = threshold 17 9 1 := by
    funext y; obtain ⟨x,rfl⟩ := Finite.surjective_of_injective (freqIndex_injective j) y; rw [hb, baseSigns_eq_integerBaseSigns]; simp only [integerBaseSigns,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one, Int.cast_ite,freqSign,threshold,freqIndex_val]
    by_cases hlt : ((2*j.val+1)*x.val)%17<9
    · rcases neg_one_pow_eq_or ℝ ((2*j.val+1)*x.val/17) with h | h <;> simp [hlt,h]
    · rcases neg_one_pow_eq_or ℝ ((2*j.val+1)*x.val/17) with h | h <;> simp [hlt,h]
  rw [he,hform,threshold9_sum]
private lemma halfperiod_phase (j : Fin 8) (t : ℕ) : zeta 17 ^ ((2*j.val+1)*(17*t)) = (-1 : ℂ) ^ t := by have hj : Odd (2*j.val+1) := ⟨j.val,by omega⟩; rw [show (2*j.val+1)*(17*t)=17*((2*j.val+1)*t) by ring,pow_mul,zeta_pow_card (by norm_num), pow_mul,hj.neg_one_pow]
private lemma residue_sum_injective (t : ℕ) : Function.Injective (fun c : Fin 17 => (⟨(t+c.val)%17,by omega⟩ : Fin 17)) := by intro c d h; have he := congrArg Fin.val h; dsimp only at he; apply Fin.ext; omega
private lemma rotation_eval (j : Fin 8) (t : Fin 34) : dotProduct (fun i => ((fun x => ((fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) t x : ℝ)) i : ℂ)) (freqPhase (2*j.val+1)) * zeta 17 ^ ((2*j.val+1)*t.val) = (radius 17 : ℂ) := by
  classical
  let e : Fin 17 ≃ Fin 17 := Equiv.ofBijective
    (fun x => ⟨(x.val+t.val)%17,by omega⟩)
    ⟨by simpa only [Nat.add_comm] using residue_sum_injective t.val,
     Finite.surjective_of_injective (by simpa only [Nat.add_comm] using residue_sum_injective t.val)⟩
  have ht (x : Fin 17) :
      ((fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) t x : ℂ) * freqPhase (2*j.val+1) x * zeta 17 ^ ((2*j.val+1)*t.val) =
        ((sourceStrategy (Fin.castLE (by decide) j)) (e x) : ℂ) * freqPhase (2*j.val+1) (e x) := by
    rw [rotatedSigns_eq_integerRotatedSigns, baseSigns_eq_integerBaseSigns]; simp only [shiftStrategy, Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,freqPhase]; have he : x.val+t.val = (x.val+t.val)%17 + 17*((x.val+t.val)/17) := (Nat.mod_add_div _ _).symm; have heq : e x = (⟨(x.val+t.val)%17,by omega⟩ : Fin 17) := rfl; rw [← heq]; have hval : (e x).val = (x.val+t.val)%17 := rfl; simp only [hval]; push_cast; have hz : zeta 17 ^ ((2*j.val+1)*x.val) * zeta 17 ^ ((2*j.val+1)*t.val) =
        zeta 17 ^ ((2*j.val+1)*((x.val+t.val)%17)) * (-1 : ℂ)^((x.val+t.val)/17) := by
      rw [← pow_add,← Nat.mul_add]
      nth_rw 1 [he]
      rw [Nat.mul_add,pow_add,halfperiod_phase]
    have hs : ((-1 : ℂ)^((x.val+t.val)/17))^2=1 := by rcases neg_one_pow_eq_or ℂ ((x.val+t.val)/17) with h | h <;> norm_num [h]
    change ((-1 : ℂ)^((x.val+t.val)/17) * (integerBaseSigns j (e x) : ℂ)) *
      zeta 17 ^ ((2*j.val+1)*x.val) * zeta 17 ^ ((2*j.val+1)*t.val) = _
    rw [mul_assoc,mul_assoc,hz]
    calc
      _ = (integerBaseSigns j (e x) : ℂ)*zeta 17 ^ ((2*j.val+1)*((x.val+t.val)%17))*
          ((-1 : ℂ)^((x.val+t.val)/17))^2 := by ring
      _ = _ := by rw [hs,mul_one]
  simp only [dotProduct]; rw [Finset.sum_mul]; push_cast; simp_rw [ht]
  calc
    _ = ∑ x : Fin 17,((sourceStrategy (Fin.castLE (by decide) j)) x : ℂ)*freqPhase (2*j.val+1) x := Equiv.sum_comp e (fun x => ((sourceStrategy (Fin.castLE (by decide) j)) x : ℂ)*freqPhase (2*j.val+1) x)
    _ = _ := by simpa [dotProduct] using baseSigns_sum j
private lemma rotatedSigns_neg (j : Fin 8) (t : Fin 34) (x : Fin 17) : (fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) ⟨(t.val+17)%34,by omega⟩ x = -(fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) t x := by
  have hres : (x.val+(t.val+17)%34)%17=(x.val+t.val)%17 := by omega
  dsimp [shiftStrategy]; have hi : (⟨(x.val+(t.val+17)%34)%17,by omega⟩ : Fin 17)=⟨(x.val+t.val)%17,by omega⟩ := Fin.ext hres; rw [hi]
  by_cases ht : t.val<17
  · have hq : (x.val+(t.val+17)%34)/17=(x.val+t.val)/17+1 := by omega
    rw [hq,pow_succ]; ring
  · have hq : (x.val+t.val)/17=(x.val+(t.val+17)%34)/17+1 := by omega
    rw [hq,pow_succ]; ring
private lemma norm_maximizers_are_rotations (j : Fin 8) (a : Fin 17 → ℝ) (ha : IsSign a) (he : ‖dotProduct (fun i => (a i : ℂ)) (freqPhase (2*j.val+1))‖=radius 17) : ∃ t : Fin 34, a=fun x => (fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) t x := by
  obtain ⟨k,hk,s,hs,hform⟩ := (odd_frequency_norm_eq_iff j a ha).mp he
  let k' : Fin 18 := ⟨k,by omega⟩
  obtain ⟨t,ht⟩ := threshold_rotation j k'; rcases hs with rfl | rfl
  · refine ⟨t,?_⟩
    funext x; rw [hform x]; simp only [freqSign, threshold, freqIndex_val]; change (-1 : ℝ)^((2*j.val+1)*x.val/17)*(if ((2*j.val+1)*x.val)%17<k then (1:ℝ) else -1)=(fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) t x; rw [rotatedSigns_eq_integerRotatedSigns]
    exact_mod_cast ht x
  · refine ⟨⟨(t.val+17)%34,by omega⟩,?_⟩
    funext x; rw [hform x, rotatedSigns_neg]; rw [rotatedSigns_eq_integerRotatedSigns, ← ht x]; simp only [freqSign,threshold,freqIndex_val,Int.cast_mul,Int.cast_pow,Int.cast_ite, Int.cast_neg,Int.cast_one]; change (-1 : ℝ)^((2*j.val+1)*x.val/17)*(if _<k then -1 else -(-1)) =
      -((-1 : ℝ)^((2*j.val+1)*x.val/17)*(if _<k then 1 else -1))
    split_ifs <;> ring
private lemma radius17_pos : 0<radius 17 := by apply one_div_pos.mpr; apply Real.sin_pos_of_pos_of_lt_pi <;> norm_num <;> linarith [Real.pi_pos]
private lemma affine_extreme_image {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] (S : Set E) (hS : Convex ℝ S) (f : E →ᵃ[ℝ] F) (hf : Set.InjOn f S) {x : E} (hx : x ∈ S.extremePoints ℝ) : f x ∈ (f '' S).extremePoints ℝ := by
  refine ⟨Set.mem_image_of_mem f hx.1, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hseg
  rw [← image_openSegment ℝ f y z] at hseg; obtain ⟨q, hq, heq⟩ := hseg; have hqS : q ∈ S := hS.segment_subset hy hz (openSegment_subset_segment _ _ _ hq); have hqx : q = x := hf hqS hx.1 heq; subst q; exact congrArg f (hx.2 hy hz hq)
private lemma not_affine_cross_of_many_extreme {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) (hS : Convex ℝ S) (g : Fin 19 → E) (hg : Function.Injective g) (hext : ∀ i, g i ∈ S.extremePoints ℝ) : ¬ ∃ f : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin 9), Set.InjOn f S ∧ f '' S = convexHull ℝ (Set.range (fun i : Fin 9 => EuclideanSpace.single i (1 : ℝ)) ∪ Set.range (fun i : Fin 9 => -EuclideanSpace.single i (1 : ℝ))) := by
  rintro ⟨f, hf, him⟩
  let h : Fin 19 → EuclideanSpace ℝ (Fin 9) := fun i => f (g i)
  have hinj : Function.Injective h := by intro i j hij; exact hg (hf (hext i).1 (hext j).1 hij)
  let U : Set (EuclideanSpace ℝ (Fin 9)) := Set.range (fun i : Fin 9 => EuclideanSpace.single i (1 : ℝ)) ∪
    Set.range (fun i : Fin 9 => -EuclideanSpace.single i (1 : ℝ))
  have hU : U.Finite := (Set.finite_range _).union (Set.finite_range _); have hsub : Set.range h ⊆ U := by
    rintro _ ⟨i,rfl⟩
    have he := affine_extreme_image S hS f hf (hext i); rw [him] at he; exact extremePoints_convexHull_subset he
  have hcard : (Set.range h).ncard = 19 := by
    rw [Set.ncard_range_of_injective hinj]
    simp
  have hle := Set.ncard_le_ncard hsub hU; have hbound : U.ncard ≤ 18 := by
    calc
      U.ncard ≤ (Set.range (fun i : Fin 9 => EuclideanSpace.single i (1 : ℝ))).ncard +
        (Set.range (fun i : Fin 9 => -EuclideanSpace.single i (1 : ℝ))).ncard := Set.ncard_union_le _ _
      _ ≤ 9 + 9 := by
        have hinjplus : Function.Injective (fun i : Fin 9 => EuclideanSpace.single i (1 : ℝ)) := by
          intro i j hij
          by_contra hne
          have hh := congrArg (fun q : EuclideanSpace ℝ (Fin 9) => q i) hij
          simpa [PiLp.single_apply, hne] using hh
        have hinjminus : Function.Injective (fun i : Fin 9 => -EuclideanSpace.single i (1 : ℝ)) := neg_injective.comp hinjplus; rw [Set.ncard_range_of_injective hinjplus, Set.ncard_range_of_injective hinjminus]
        simp
      _ = 18 := rfl
  omega
private lemma root_reduce (z : ℂ) (hz : z^17= -1) (t : ℕ) : z^t=(-1 : ℂ)^(t/17)*z^(t%17) := by
  nth_rw 1 [← Nat.mod_add_div t 17]
  rw [pow_add,pow_mul,hz]; ring
private lemma root_reflect (z : ℂ) (hz : z^17= -1) (hn : ‖z‖=1) (r : ℕ) (hr : r≤17) : (z^(17-r)).re= -(z^r).re := by
  have hnorm : Complex.normSq (z^r)=1 := by rw [Complex.normSq_eq_norm_sq,norm_pow,hn]; norm_num
  have hnon : z^r≠0 := by intro h; rw [h,Complex.normSq_zero] at hnorm; norm_num at hnorm
  have he : z^(17-r)= -conj (z^r) := by apply mul_left_cancel₀ hnon; rw [← pow_add,Nat.add_sub_of_le hr,hz,mul_neg,Complex.mul_conj,hnorm]; norm_num
  rw [he,Complex.neg_re,Complex.conj_re]
private def total (x : Fin 3 → Fin 17) : ℕ := ∑ n, (x n).val
private def totalCoeff (r : Fin 9) (t : ℕ) : ℤ := (-1) ^ (t / 17) * (if t % 17 = r.val then 1 else if r.val ≠ 0 ∧ t % 17 = 17-r.val then -1 else 0)
private def basisCoeff (r : Fin 9) (x : Fin 3 → Fin 17) : ℤ := totalCoeff r (total x)
private def F (r : Fin 9) : Tensor 3 17 := WithLp.toLp 2 (fun x => (basisCoeff r x : ℝ))
private def d (a b c : Fin 17 → ℝ) : Tensor 3 17 := WithLp.toLp 2 (fun x => a (x 0) * b (x 1) * c (x 2))
private def fullVertex (j : Fin 9) : Tensor 3 17 := Gamma 3 17
  (d (sourceStrategy j) (sourceStrategy j) (sourceStrategy j))
private def productCoeff (a b c : Fin 17 → ℝ) (r : Fin 17) : ℝ := ∑ x : Fin 3 → Fin 17,
    if total x % 17 = r.val then ((-1 : ℝ) ^ (total x / 17)) * d a b c x else 0
private def P (a b c : Fin 17 → ℝ) (r : Fin 9) : ℝ := if h : r.val = 0 then productCoeff a b c 0 else
    (productCoeff a b c ⟨r.val, by omega⟩ - productCoeff a b c ⟨17 - r.val, by omega⟩) / 2
private lemma basis_inner_strategy (a b c : Fin 17 → ℝ) (r : Fin 9) : ⟪F r, d a b c⟫_ℝ = if r.val = 0 then P a b c r else 2 * P a b c r := by
  rw [PiLp.inner_apply]; simp only [F, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial]
  by_cases hr : r.val = 0
  · have hz : r = 0 := Fin.ext hr; subst r; simp only [P, Fin.val_zero, ↓reduceDIte, productCoeff, basisCoeff, totalCoeff, Fin.val_zero, ne_eq, not_true_eq_false, false_and, ↓reduceIte, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_zero]; apply Finset.sum_congr rfl; intro x hx
    split_ifs <;> ring
  · simp only [hr, if_false, P, ↓reduceDIte, productCoeff]; rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro x hx; simp only [basisCoeff, totalCoeff, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_ite, Int.cast_zero]; have hrv := r.isLt; have hdiff : 17 - r.val ≠ r.val := by omega
    split_ifs <;> simp_all <;> ring
private lemma basisCoeff_orthogonal (r s : Fin 9) (hrs : r ≠ s) (x : Fin 3 → Fin 17) : basisCoeff r x * basisCoeff s x = 0 := by
  have hr := r.isLt; have hs := s.isLt; have hne : r.val ≠ s.val := by intro h; exact hrs (Fin.ext h)
  simp only [basisCoeff, totalCoeff]
  split_ifs <;> simp_all <;> omega
private lemma basis_orthogonal (r s : Fin 9) (hrs : r ≠ s) : ⟪F r, F s⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]; simp only [F, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial]; apply Finset.sum_eq_zero; intro x hx; have h := basisCoeff_orthogonal s r hrs.symm x
  exact_mod_cast h
private lemma act_at_image {N m : ℕ} (g : (Fin N → Fin m) → ℝ × (Fin N → Fin m)) (hg : Function.Injective (fun x => (g x).2)) (p : Tensor N m) (x : Fin N → Fin m) : act g p (g x).2 = (g x).1 * p x := by
  classical
  simp only [act, PiLp.toLp_apply]; rw [Finset.sum_eq_single x]
  · simp
  · intro y hy hyx; have hneq : (g y).2 ≠ (g x).2 := fun h => hyx (hg h); simp [hneq]
  · simp
private lemma gen3_index_injective : Function.Injective (fun x : Fin 3 → Fin 17 => (gen3 x).2) := by
  have hinj (k : ℤ) (hk : k = 1 ∨ k = -1 ∨ k = 0) :
      Function.Injective (fun i : Fin 17 => (reduceIdx i ((i : ℤ) + k)).2) := by
    rcases hk with rfl | rfl | rfl <;> decide
  intro x y h; funext n; have hn := congrFun h n; change (reduceIdx (x n) ((x n : ℤ) + if n.val = 0 then 1 else if n.val = 1 then -1 else 0)).2 =
      (reduceIdx (y n) ((y n : ℤ) + if n.val = 0 then 1 else if n.val = 1 then -1 else 0)).2 at hn
  exact hinj _ (by split_ifs <;> simp) hn
private lemma gen4_index_injective : Function.Injective (fun x : Fin 3 → Fin 17 => (gen4 x).2) := by
  have hinj : Function.Injective (fun i : Fin 17 => (reduceIdx i (17 - (i : ℤ))).2) := by decide
  intro x y h; funext n; exact hinj (congrFun h n)
private lemma gen1_index_injective : Function.Injective (fun x : Fin 3 → Fin 17 => (gen1 x).2) := by
  intro x y h; funext n; have hh := congrFun h (Equiv.swap (0 : Fin 3) 1 n)
  simpa [gen1] using hh
private lemma gen2_index_injective : Function.Injective (fun x : Fin 3 → Fin 17 => (gen2 x).2) := by
  intro x y h; funext n; have hh := congrFun h (finRotate 3 n)
  simpa [gen2] using hh
private lemma invariant_gen3 (p : Tensor 3 17) (hp : p ∈ symSub 3 17) (x : Fin 3 → Fin 17) : p (gen3 x).2 = (gen3 x).1 * p x := by have hfix := hp (2 : Fin 4); change act gen3 p = p at hfix; have h := congrArg (fun q : Tensor 3 17 => q (gen3 x).2) hfix; rw [act_at_image _ gen3_index_injective] at h; exact h.symm
private lemma reduceIdx_self (x : Fin 17) : reduceIdx x (x : ℤ) = (1, x) := by
  have hq : (x : ℤ) / 17 = 0 := by omega
  have hm : (x : ℤ) % 17 = x := by omega
  apply Prod.ext
  · simp [reduceIdx, normIdx, hq]
  · apply Fin.ext; simp [reduceIdx, normIdx, hm]
private lemma reduceIdx_incr (x : Fin 17) : reduceIdx x ((x : ℤ) + 1) = (if x.val = 16 then -1 else 1, ⟨(x.val + 1) % 17, by omega⟩) := by
  apply Prod.ext
  · by_cases h : x.val = 16
    · have hx : (x : ℤ) = 16 := by exact_mod_cast h
      norm_num [reduceIdx, normIdx, hx, h]
    · have hq : ((x : ℤ) + 1) / 17 = 0 := by omega
      simp [reduceIdx, normIdx, hq, h]
  · apply Fin.ext; simp only [reduceIdx, normIdx]; omega
private lemma reduceIdx_decr (x : Fin 17) (hx : 0 < x.val) : reduceIdx x ((x : ℤ) - 1) = (1, ⟨x.val - 1, by omega⟩) := by
  have hq : ((x : ℤ) - 1) / 17 = 0 := by omega
  have hm : ((x : ℤ) - 1) % 17 = (x : ℤ) - 1 := by omega
  apply Prod.ext
  · simp [reduceIdx, normIdx, hq]
  · apply Fin.ext; simp only [reduceIdx, normIdx, hm]; omega
private lemma gen3_tuple (a b c : Fin 17) (hb : 0 < b.val) : gen3 ![a,b,c] = (if a.val = 16 then -1 else 1, ![⟨(a.val + 1) % 17, by omega⟩, ⟨b.val - 1, by omega⟩, c]) := by
  have hi := reduceIdx_incr a; have hd := reduceIdx_decr b hb; have hc := reduceIdx_self c; apply Prod.ext
  · simp [gen3, shiftParty, Fin.prod_univ_succ, ← sub_eq_add_neg, hi, hd, hc]
  · funext n
    fin_cases n <;> simp [gen3, shiftParty, ← sub_eq_add_neg, hi, hd, hc]
private lemma invariant_tuple_step (p : Tensor 3 17) (hp : p ∈ symSub 3 17) (a b c : Fin 17) (hb : 0 < b.val) : p ![⟨(a.val + 1) % 17, by omega⟩, ⟨b.val - 1, by omega⟩, c] = (if a.val = 16 then -1 else 1) * p ![a,b,c] := by have h := invariant_gen3 p hp ![a,b,c]; rw [gen3_tuple a b c hb] at h; exact h
private lemma invariant_gen1 (p : Tensor 3 17) (hp : p ∈ symSub 3 17) (x : Fin 3 → Fin 17) : p (gen1 x).2 = p x := by
  have hfix := hp (0 : Fin 4); change act gen1 p = p at hfix; have h := congrArg (fun q : Tensor 3 17 => q (gen1 x).2) hfix; rw [act_at_image _ gen1_index_injective] at h
  simpa [gen1] using h.symm
private lemma invariant_gen2 (p : Tensor 3 17) (hp : p ∈ symSub 3 17) (x : Fin 3 → Fin 17) : p (gen2 x).2 = p x := by
  have hfix := hp (1 : Fin 4); change act gen2 p = p at hfix; have h := congrArg (fun q : Tensor 3 17 => q (gen2 x).2) hfix; rw [act_at_image _ gen2_index_injective] at h
  simpa [gen2] using h.symm
private lemma invariant_swap_last (p : Tensor 3 17) (hp : p ∈ symSub 3 17) (a b c : Fin 17) : p ![a,c,b] = p ![a,b,c] := by
  have h1 := invariant_gen1 p hp (gen2 ![a,b,c]).2; have h2 := invariant_gen2 p hp ![a,b,c]; have he : (gen1 (gen2 ![a,b,c]).2).2 = ![a,c,b] := by funext n; fin_cases n <;> simp [gen1, gen2, Fin.sub_def, Fin.neg_def, Equiv.swap_apply_def]
  rw [he] at h1; exact h1.trans h2
private lemma invariant_zero_second (p : Tensor 3 17) (hp : p ∈ symSub 3 17) (b : ℕ) (hb : b < 17) (a c : Fin 17) : p ![a,⟨b,hb⟩,c] = (-1 : ℝ) ^ ((a.val + b) / 17) * p ![⟨(a.val + b) % 17, by omega⟩,0,c] := by
  induction b generalizing a with
  | zero =>
    have ha : a.val / 17 = 0 := by omega
    have hm : a.val % 17 = a.val := by omega
    have he : (⟨a.val % 17, by omega⟩ : Fin 17) = a := Fin.ext hm
    simp only [Nat.add_zero, ha, pow_zero, one_mul, he]; rfl
  | succ b ih =>
    have hb0 : b < 17 := by omega
    let a' : Fin 17 := ⟨(a.val + 1) % 17, by omega⟩
    have hstep := invariant_tuple_step p hp a ⟨b+1,hb⟩ c (by change 0 < b + 1; omega); change p ![a',⟨b,hb0⟩,c] = (if a.val = 16 then -1 else 1) * p ![a,⟨b+1,hb⟩,c] at hstep; have hind := ih hb0 a'
    by_cases ha : a.val = 16
    · have ha' : a'.val = 0 := by simp [a', ha]
      have hq : (a.val + (b + 1)) / 17 = 1 := by omega
      have hm : (a.val + (b + 1)) % 17 = b := by omega
      have hq' : (a'.val + b) / 17 = 0 := by omega
      have hm' : (a'.val + b) % 17 = b := by omega
      have he : (⟨(a'.val + b) % 17, by omega⟩ : Fin 17) =
          ⟨(a.val + (b+1)) % 17, by omega⟩  := Fin.ext (by change (a'.val + b) % 17 = (a.val + (b+1)) % 17; omega)
      rw [hq', pow_zero, one_mul, he] at hind; rw [if_pos ha] at hstep; rw [hq, pow_one]; linarith
    · have ha' : a'.val = a.val + 1 := by dsimp [a']; omega
      have hq : (a'.val + b) / 17 = (a.val + (b+1)) / 17 := by omega
      have hm : (a'.val + b) % 17 = (a.val + (b+1)) % 17 := by omega
      have he : (⟨(a'.val + b) % 17, by omega⟩ : Fin 17) =
          ⟨(a.val + (b+1)) % 17, by omega⟩ := Fin.ext hm
      rw [if_neg ha, one_mul] at hstep; rw [hq, he] at hind; exact hstep.symm.trans hind
private lemma invariant_reduce_total (p : Tensor 3 17) (hp : p ∈ symSub 3 17) (a b c : Fin 17) : p ![a,b,c] = (-1 : ℝ) ^ ((a.val + b.val + c.val) / 17) * p ![⟨(a.val + b.val + c.val) % 17, by omega⟩,0,0] := by
  let t : Fin 17 := ⟨(a.val + b.val) % 17, by omega⟩
  have h1 := invariant_zero_second p hp b.val b.isLt a c; have h2 := invariant_zero_second p hp c.val c.isLt t 0; have hswap := invariant_swap_last p hp t 0 c; have hq : (a.val + b.val) / 17 + (t.val + c.val) / 17 =
      (a.val + b.val + c.val) / 17 := by dsimp [t]; omega
  have hm : (t.val + c.val) % 17 = (a.val + b.val + c.val) % 17 := by dsimp [t]; omega
  have he : (⟨(t.val + c.val) % 17, by omega⟩ : Fin 17) =
      ⟨(a.val + b.val + c.val) % 17, by omega⟩ := Fin.ext hm
  change p ![a,b,c] = (-1 : ℝ) ^ ((a.val + b.val) / 17) * p ![t,0,c] at h1; rw [← hswap, h2, he, ← mul_assoc, ← pow_add, hq] at h1; exact h1
private lemma invariant_total (p : Tensor 3 17) (hp : p ∈ symSub 3 17) (x : Fin 3 → Fin 17) : p x = (-1 : ℝ) ^ (total x / 17) * p ![⟨total x % 17, by omega⟩,0,0] := by
  have hx : ![x 0,x 1,x 2] = x := by funext n; fin_cases n <;> simp
  have ht : total x = (x 0).val + (x 1).val + (x 2).val := by simp [total, Fin.sum_univ_succ]; omega
  have h := invariant_reduce_total p hp (x 0) (x 1) (x 2)
  simpa only [hx, ← ht] using h
private lemma reduceIdx_reflect (r : Fin 17) : reduceIdx r (17 - (r : ℤ)) = (if r.val = 0 then -1 else 1, ⟨(17 - r.val) % 17, by omega⟩) := by
  apply Prod.ext
  · by_cases h : r.val = 0
    · have hz : (r : ℤ) = 0 := by exact_mod_cast h
      norm_num [reduceIdx, normIdx, hz, h]
    · have hq : (17 - (r : ℤ)) / 17 = 0 := by omega
      simp [reduceIdx, normIdx, hq, h]
  · apply Fin.ext; simp only [reduceIdx, normIdx]; omega
private lemma gen4_zero_tuple (r : Fin 17) : gen4 ![r,0,0] = (if r.val = 0 then 1 else -1, ![⟨(17-r.val) % 17, by omega⟩,0,0]) := by
  have hr := reduceIdx_reflect r; have hz : reduceIdx (0 : Fin 17) 17 = (-1,0) := by convert reduceIdx_reflect (0 : Fin 17) using 1 <;> rfl
  apply Prod.ext
  · simp [gen4, Fin.prod_univ_succ, hr, hz] <;> split_ifs <;> norm_num
  · funext n
    fin_cases n <;> simp [gen4, hr, hz]
private lemma invariant_reflect (p : Tensor 3 17) (hp : p ∈ symSub 3 17) (r : Fin 17) (hr : r.val ≠ 0) : p ![⟨17-r.val, by omega⟩,0,0] = -p ![r,0,0] := by
  have hfix := hp (3 : Fin 4); change act gen4 p = p at hfix; have h := congrArg (fun q : Tensor 3 17 => q (gen4 ![r,0,0]).2) hfix; rw [act_at_image _ gen4_index_injective] at h; rw [gen4_zero_tuple] at h; have hm : (17-r.val) % 17 = 17-r.val := by omega
  simpa [hr, hm] using h.symm
private def shortResidue (x : Fin 3 → Fin 17) : Fin 9 := if h : total x % 17 < 9 then ⟨total x % 17,h⟩ else ⟨17-total x % 17,by omega⟩
private def foldSign (x : Fin 3 → Fin 17) : ℝ := (-1 : ℝ) ^ (total x / 17) * if total x % 17 < 9 then 1 else -1
private lemma basis_sum_apply (q : Fin 9 → ℝ) (x : Fin 3 → Fin 17) : (∑ r : Fin 9, q r • F r) x = foldSign x * q (shortResidue x) := by
  classical
  change (WithLp.ofLp (∑ r : Fin 9, q r • F r)) x = _; rw [WithLp.ofLp_sum]; simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]; rw [Finset.sum_eq_single (shortResidue x)]
  · dsimp [F, shortResidue, foldSign]
    split_ifs with h
    · have hdiff : 17-total x % 17 ≠ total x % 17 := by omega
      simp [basisCoeff, totalCoeff, h, hdiff]; ring
    · have hh : total x % 17 ≠ 17 - total x % 17 := by omega
      have hnz : 17 - total x % 17 ≠ 0 := by omega
      have hmirror : total x % 17 = 17 - (17 - total x % 17) := by omega
      simp only [basisCoeff, totalCoeff, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_ite, if_neg hh, if_pos (And.intro hnz hmirror)]; ring
  · intro r hr hne; have hrv := r.isLt; have hs : r.val ≠ (shortResidue x).val := by intro h; exact hne (Fin.ext h)
    have he : basisCoeff r x = 0 := by
      by_cases hh : total x % 17 < 9
      · have hs' : r.val ≠ total x % 17 := by simpa only [shortResidue, dif_pos hh] using hs
        have hh' : total x % 17 ≠ 17 - r.val := by omega
        simp [basisCoeff, totalCoeff, hs'.symm, hh']
      · have hs' : r.val ≠ 17-total x % 17 := by simpa only [shortResidue, dif_neg hh] using hs
        have hh' : total x % 17 ≠ r.val := by omega
        have hh'' : total x % 17 ≠ 17-r.val := by omega
        simp [basisCoeff, totalCoeff, hh', hh'']
    simp [F, he]
  · simp
private lemma invariant_basis_expansion (p : Tensor 3 17) (hp : p ∈ symSub 3 17) : p = ∑ r : Fin 9, (p ![⟨(r).val, by omega⟩, 0, 0]) • F r := by
  apply PiLp.ext; intro x; rw [basis_sum_apply]; have h := invariant_total p hp x; dsimp [foldSign, shortResidue]
  split_ifs with hs
  · simpa only [mul_one] using h
  · let r : Fin 17 := ⟨total x % 17,by omega⟩
    have hr : r.val ≠ 0 := by dsimp [r]; omega
    have href := invariant_reflect p hp r hr; change p ![⟨17-total x % 17,by omega⟩,0,0] = -p ![⟨total x % 17,by omega⟩,0,0] at href; rw [href]
    simpa only [mul_neg_one, neg_mul_neg] using h
private def intNormIdx (v : ℤ) : ℤ × Fin 17 := ((-1 : ℤ) ^ (v / 17).natAbs, ⟨(v % 17).toNat, by omega⟩)
private def intGen3 (x : Fin 3 → Fin 17) : ℤ × (Fin 3 → Fin 17) := ((intNormIdx ((x 0 : ℤ) + 1)).1 * (intNormIdx ((x 1 : ℤ) - 1)).1, ![(intNormIdx ((x 0 : ℤ) + 1)).2, (intNormIdx ((x 1 : ℤ) - 1)).2, x 2])
private def intGen4 (x : Fin 3 → Fin 17) : ℤ × (Fin 3 → Fin 17) := (∏ n, -(intNormIdx (17-(x n : ℤ))).1, fun n => (intNormIdx (17-(x n : ℤ))).2)

private lemma basisCoeff_tuple (r : Fin 9) (a b c : Fin 17) : basisCoeff r ![a,b,c] = totalCoeff r (a.val+b.val+c.val) := by simp [basisCoeff, totalCoeff, totalCoeff, total, Fin.sum_univ_succ, add_assoc]
private lemma totalCoeff_add17 (r : Fin 9) (t : ℕ) : totalCoeff r (t+17) = -totalCoeff r t := by
  have hq : (t+17)/17 = t/17+1 := by omega
  have hm : (t+17)%17 = t%17 := by omega
  simp only [totalCoeff, hq, hm, pow_succ]; ring
private lemma intNorm_incr (a : Fin 17) : intNormIdx ((a : ℤ)+1) = (if a.val = 16 then -1 else 1, ⟨(a.val+1)%17,by omega⟩) := by
  apply Prod.ext
  · by_cases h : a.val = 16
    · have ha : (a : ℤ) = 16 := by exact_mod_cast h
      norm_num [intNormIdx,ha,h]
    · have hq : ((a : ℤ)+1)/17 = 0 := by omega
      simp [intNormIdx,hq,h]
  · apply Fin.ext; dsimp [intNormIdx]; omega
private lemma intNorm_decr (a : Fin 17) : intNormIdx ((a : ℤ)-1) = (if a.val = 0 then -1 else 1, ⟨(a.val+16)%17,by omega⟩) := by
  apply Prod.ext
  · by_cases h : a.val = 0
    · have ha : (a : ℤ) = 0 := by exact_mod_cast h
      norm_num [intNormIdx,ha,h]
    · have hq : ((a : ℤ)-1)/17 = 0 := by omega
      simp [intNormIdx,hq,h]
  · apply Fin.ext; dsimp [intNormIdx]; omega
private lemma intGen3_tuple (a b c : Fin 17) : intGen3 ![a,b,c] = ((if a.val = 16 then -1 else 1) * (if b.val = 0 then -1 else 1), ![⟨(a.val+1)%17,by omega⟩,⟨(b.val+16)%17,by omega⟩,c]) := by simp [intGen3, intNorm_incr, intNorm_decr]
private lemma intGen3_coeff (r : Fin 9) (x : Fin 3 → Fin 17) : basisCoeff r (intGen3 x).2 = (intGen3 x).1 * basisCoeff r x := by
  have hx : ![x 0,x 1,x 2] = x := by funext n; fin_cases n <;> simp
  rw [← hx, intGen3_tuple]; simp only [basisCoeff_tuple, Prod.fst, Prod.snd]; let a := (x 0).val; let b := (x 1).val; let c := (x 2).val; have ha0 : a < 17 := (x 0).isLt; have hb0 : b < 17 := (x 1).isLt; change totalCoeff r ((a+1)%17+(b+16)%17+c) =
    (if a = 16 then -1 else 1) * (if b = 0 then -1 else 1) * totalCoeff r (a+b+c)
  by_cases ha : a = 16 <;> by_cases hb : b = 0
  · have ht : (a+1)%17+(b+16)%17+c = a+b+c := by omega
    simp [ha,hb,ht]
  · have ht : a+b+c = ((a+1)%17+(b+16)%17+c)+17 := by omega
    rw [ht,totalCoeff_add17]; simp [ha,hb]
  · have ht : (a+1)%17+(b+16)%17+c = a+b+c+17 := by omega
    rw [ht,totalCoeff_add17]; simp [ha,hb]
  · have ht : (a+1)%17+(b+16)%17+c = a+b+c := by omega
    simp [ha,hb,ht]
private lemma totalCoeff_sq (r : Fin 9) (t : ℕ) : totalCoeff r t ^ 2 = if t % 17 = r.val then 1 else if r.val ≠ 0 ∧ t % 17 = 17-r.val then 1 else 0 := by
  have hp : ((-1 : ℤ) ^ (t / 17)) ^ 2 = 1 := by rcases neg_one_pow_eq_or ℤ (t/17) with h | h <;> norm_num [h]
  simp only [totalCoeff, mul_pow, hp, one_mul]
  split_ifs <;> norm_num
private lemma totalCoeff_sq_sum (r : Fin 9) (a b : Fin 17) : ∑ c : Fin 17, basisCoeff r ![a,b,c] ^ 2 = if r.val = 0 then 1 else 2 := by
  classical
  let e : Fin 17 ≃ Fin 17 := Equiv.ofBijective (fun c => ⟨(a.val+b.val+c.val)%17,by omega⟩)
    ⟨residue_sum_injective (a.val+b.val), Finite.surjective_of_injective (residue_sum_injective (a.val+b.val))⟩
  let f : Fin 17 → ℤ := fun i =>
    if i.val = r.val then 1 else if r.val ≠ 0 ∧ i.val = 17-r.val then 1 else 0
  have he : (∑ c : Fin 17, basisCoeff r ![a,b,c] ^ 2) = ∑ c : Fin 17, f (e c) := by apply Finset.sum_congr rfl; intro c hc; rw [basisCoeff_tuple,totalCoeff_sq]; rfl
  rw [he, Equiv.sum_comp e f]
  by_cases hr : r.val = 0
  · simp [f,hr]
  · let u : Fin 17 := ⟨r.val,by omega⟩
    let v : Fin 17 := ⟨17-r.val,by omega⟩; have huv : u ≠ v := by intro h; have h' := congrArg Fin.val h; dsimp [u,v] at h'; omega
    have hf : f = fun i => (if i = u then 1 else 0) + (if i = v then 1 else 0) := by
      funext i; have hiu : i.val = r.val ↔ i = u := by
        constructor
        · intro h; exact Fin.ext h
        · intro h; exact congrArg Fin.val h
      have hiv : i.val = 17-r.val ↔ i = v := by
        constructor
        · intro h; exact Fin.ext h
        · intro h; exact congrArg Fin.val h
      dsimp [f]; simp only [hiu,hiv,hr,true_and]
      split_ifs <;> simp_all
    rw [hf, Finset.sum_add_distrib]; simp [hr]
private def residueCoeff (r : Fin 9) (t : ℕ) : ℤ := if t = r.val then 1 else if r.val ≠ 0 ∧ t = 17-r.val then -1 else 0
private lemma residueCoeff_reflect (r : Fin 9) (t : ℕ) (ht0 : 0 < t) (ht : t < 17) : residueCoeff r (17-t) = -residueCoeff r t := by
  have hr := r.isLt; dsimp [residueCoeff]
  split_ifs <;> simp_all <;> omega
private lemma neg_pow_cancel (a b : ℕ) : (-1 : ℤ) ^ (a+b) * (-1) ^ a = (-1) ^ b := by
  have hs : ((-1 : ℤ) ^ a) ^ 2 = 1 := by rcases neg_one_pow_eq_or ℤ a with h | h <;> norm_num [h]
  rw [pow_add]
  calc
    (-1 : ℤ) ^ a * (-1) ^ b * (-1) ^ a = ((-1 : ℤ) ^ a) ^ 2 * (-1) ^ b := by ring
    _ = _ := by rw [hs,one_mul]
private lemma totalCoeff_reflect (r : Fin 9) (t u k : ℕ) (h : t+u = 17*k) : totalCoeff r u = (-1) ^ k * totalCoeff r t := by
  change (-1 : ℤ) ^ (u/17) * residueCoeff r (u%17) =
    (-1 : ℤ) ^ k * ((-1) ^ (t/17) * residueCoeff r (t%17))
  by_cases ht : t%17 = 0
  · have hu : u%17 = 0 := by omega
    have hk : t/17 + u/17 = k := by omega
    rw [ht,hu,← hk,← mul_assoc,neg_pow_cancel]
  · have hu : u%17 = 17-t%17 := by omega
    have hk : t/17 + (u/17+1) = k := by omega
    rw [hu,residueCoeff_reflect r (t%17) (by omega) (by omega),← hk, ← mul_assoc,neg_pow_cancel,pow_succ]; ring
private lemma intNorm_reflect (a : Fin 17) : intNormIdx (17-(a : ℤ)) = (if a.val = 0 then -1 else 1,⟨(17-a.val)%17,by omega⟩) := by
  apply Prod.ext
  · by_cases ha : a.val = 0
    · have hz : (a : ℤ) = 0 := by exact_mod_cast ha
      norm_num [intNormIdx,hz,ha]
    · have hq : (17-(a : ℤ))/17 = 0 := by omega
      simp [intNormIdx,hq,ha]
  · apply Fin.ext; dsimp [intNormIdx]; omega
private lemma intGen4_coeff (r : Fin 9) (x : Fin 3 → Fin 17) : basisCoeff r (intGen4 x).2 = (intGen4 x).1 * basisCoeff r x := by
  let k : ℕ := ∑ n : Fin 3, if (x n).val = 0 then 0 else 1; have hs : (intGen4 x).1 = (-1 : ℤ) ^ k := by
    simp [intGen4,intNorm_reflect,k,Fin.prod_univ_succ,Fin.sum_univ_succ]
    split_ifs <;> norm_num
  have ht : total x + total (intGen4 x).2 = 17*k := by
    have hterm (n : Fin 3) : (x n).val + ((intGen4 x).2 n).val =
        17 * (if (x n).val = 0 then 0 else 1) := by
      simp only [intGen4,intNorm_reflect]
      by_cases h : (x n).val = 0 <;> simp [h] <;> omega
    dsimp [total,k]; rw [← Finset.sum_add_distrib,Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => hterm n)
  rw [hs]; change totalCoeff r (total (intGen4 x).2) = (-1 : ℤ) ^ k * totalCoeff r (total x); exact totalCoeff_reflect r _ _ _ ht
private lemma basisCoeff_sq_sum (r : Fin 9) : ∑ x : Fin 3 → Fin 17, basisCoeff r x ^ 2 = if r.val = 0 then 289 else 578 := by
  let e : (Fin 3 → Fin 17) ≃ Fin 17 × Fin 17 × Fin 17 :=
    (D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry.tensorTowerTupleEquiv (Fin 17) 2).symm
  have he : (∑ x : Fin 3 → Fin 17, basisCoeff r x ^ 2) =
      ∑ t : Fin 17 × Fin 17 × Fin 17, basisCoeff r ![t.1,t.2.1,t.2.2] ^ 2 := by
    apply Fintype.sum_equiv e; intro x; congr 2; funext n; fin_cases n <;> rfl
  rw [he,Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type,totalCoeff_sq_sum]
  by_cases hr : r.val = 0 <;> simp [hr]
private lemma basis_inner_self (r : Fin 9) : ⟪F r,F r⟫_ℝ = if r.val = 0 then 289 else 578 := by
  rw [PiLp.inner_apply]; simp only [F,PiLp.toLp_apply,RCLike.inner_apply,conj_trivial]; have h := basisCoeff_sq_sum r; have hh : (∑ x : Fin 3 → Fin 17, (basisCoeff r x : ℝ) ^ 2) =
      if r.val = 0 then 289 else 578 := by exact_mod_cast h
  simpa only [pow_two] using hh
private lemma cast_intNorm_sign (v : ℤ) : ((intNormIdx v).1 : ℝ) = (normIdx 17 v).1 := by simp only [intNormIdx,normIdx,Int.cast_pow,Int.cast_neg,Int.cast_one]; change (-1 : ℝ) ^ (v/17).natAbs = (-1 : ℝ) ^ (v/17); simp only [neg_one_pow_eq_ite,neg_one_zpow_eq_ite,Int.natAbs_even]
private lemma cast_intNorm_idx (x : Fin 17) (v : ℤ) : (intNormIdx v).2 = (reduceIdx x v).2 := by apply Fin.ext; rfl
private lemma gen3_int_bridge (x : Fin 3 → Fin 17) : gen3 x = (((intGen3 x).1 : ℝ), (intGen3 x).2) := by
  apply Prod.ext
  · simp only [gen3,Prod.fst,Fin.prod_univ_three]; change (reduceIdx (x 0) ((x 0:ℤ)+1)).1 *
      (reduceIdx (x 1) ((x 1:ℤ)-1)).1 * (reduceIdx (x 2) (x 2:ℤ)).1 = _
    rw [reduceIdx_self]; simp only [Prod.fst,mul_one,intGen3,Int.cast_mul,cast_intNorm_sign]; rfl
  · funext n
    fin_cases n
    · exact (cast_intNorm_idx (x 0) ((x 0:ℤ)+1)).symm
    · exact (cast_intNorm_idx (x 1) ((x 1:ℤ)-1)).symm
    · change (reduceIdx (x 2) (x 2:ℤ)).2 = x 2; rw [reduceIdx_self]
private lemma gen4_int_bridge (x : Fin 3 → Fin 17) : gen4 x = (((intGen4 x).1 : ℝ), (intGen4 x).2) := by
  apply Prod.ext
  · simp [gen4,intGen4,Int.cast_prod,cast_intNorm_sign,reduceIdx]
  · funext n; exact (cast_intNorm_idx (x n) (17-(x n:ℤ))).symm
private lemma basis_fixed (r : Fin 9) : F r ∈ symSub 3 17 := by
  intro i; fin_cases i
  · change act gen1 (F r) = F r; apply PiLp.ext; intro y; obtain ⟨x,rfl⟩ := Finite.surjective_of_injective gen1_index_injective y; rw [act_at_image _ gen1_index_injective]; have ht : total (gen1 x).2 = total x := by
      simp [total,gen1,Fin.sum_univ_succ,show Equiv.swap (0:Fin 3) 1 2 = 2 by decide]
      ring
    change (gen1 x).1 * (basisCoeff r x : ℝ) = (basisCoeff r (gen1 x).2 : ℝ); rw [show (gen1 x).1 = 1 by rfl,one_mul]
    congr 1; simp only [basisCoeff, totalCoeff,ht]
  · change act gen2 (F r) = F r; apply PiLp.ext; intro y; obtain ⟨x,rfl⟩ := Finite.surjective_of_injective gen2_index_injective y; rw [act_at_image _ gen2_index_injective]; have ht : total (gen2 x).2 = total x := by
      exact Equiv.sum_comp (finRotate 3).symm (fun n : Fin 3 => (x n).val)
    change (gen2 x).1 * (basisCoeff r x : ℝ) = (basisCoeff r (gen2 x).2 : ℝ); rw [show (gen2 x).1 = 1 by rfl,one_mul]
    congr 1; simp only [basisCoeff, totalCoeff,ht]
  · change act gen3 (F r) = F r; apply PiLp.ext; intro y; obtain ⟨x,rfl⟩ := Finite.surjective_of_injective gen3_index_injective y; rw [act_at_image _ gen3_index_injective]; simp only [gen3_int_bridge,Prod.fst,Prod.snd]
    simpa [F] using congrArg (fun z : ℤ => (z : ℝ)) (intGen3_coeff r x).symm
  · change act gen4 (F r) = F r; apply PiLp.ext; intro y; obtain ⟨x,rfl⟩ := Finite.surjective_of_injective gen4_index_injective y; rw [act_at_image _ gen4_index_injective]; simp only [gen4_int_bridge,Prod.fst,Prod.snd]
    simpa [F] using congrArg (fun z : ℤ => (z : ℝ)) (intGen4_coeff r x).symm
private lemma Gamma_inner_basis (p : Tensor 3 17) (r : Fin 9) : ⟪F r,Gamma 3 17 p⟫_ℝ = ⟪F r,p⟫_ℝ := by have h := (symSub 3 17).starProjection_inner_eq_zero p (F r) (basis_fixed r); rw [inner_sub_left] at h; dsimp [Gamma]; rw [real_inner_comm] at h; rw [real_inner_comm (F r) ((symSub 3 17).starProjection p)] at h; linarith
private lemma basis_inner_expansion (v : Fin 9 → ℝ) (r : Fin 9) : ⟪F r,∑ s : Fin 9,v s • F s⟫_ℝ = v r * (if r.val = 0 then 289 else 578) := by
  rw [inner_sum]; rw [Finset.sum_eq_single r]
  · simp only [Finset.mem_univ,inner_smul_right,basis_inner_self]
  · intro s hs hne; rw [inner_smul_right,basis_orthogonal r s hne.symm,mul_zero]
  · simp
private lemma projection_formula (a b c : Fin 17 → ℝ) : Gamma 3 17 (d a b c) = ∑ r : Fin 9,(P a b c r / 289) • F r := by
  let q := Gamma 3 17 (d a b c); have hq : q ∈ symSub 3 17 := (symSub 3 17).starProjection_apply_mem _; have he := invariant_basis_expansion q hq; have hc (r : Fin 9) : (q ![⟨(r).val, by omega⟩, 0, 0]) = P a b c r / 289 := by
    have hinner := Gamma_inner_basis (d a b c) r; change ⟪F r,q⟫_ℝ = _ at hinner; rw [he,basis_inner_expansion,basis_inner_strategy] at hinner
    by_cases hr : r.val = 0 <;> simp only [hr,ite_true,ite_false] at hinner ⊢ <;> linarith
  simpa only [hc] using he
private def a : Fin 17 → ℤ := ![1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1]
private def b : Fin 17 → ℤ := ![-1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, 1, -1, 1, 1, -1]
private def c : Fin 17 → ℤ := ![1, -1, 1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1]
private def abc : Fin 17 → ℤ := ![-141, 133, -109, 69, -13, -43, 91, -123, 139, -139, 123, -91, 43, 13, -69, 109, -133]
private def w : Fin 9 → ℤ := ![-15, 27, -21, 8, 59, 24, -5, -6, 10]
private def V : Fin 9 → Fin 9 → ℤ := ![![145, 145, 145, 145, 145, 145, 145, 145, 289], ![143, 127, 95, 47, -17, -73, -113, -137, -289], ![137, 73, -47, -127, -143, -95, 17, 113, 289], ![127, -17, -137, -113, 47, 143, 95, -73, -289], ![113, -95, -127, 73, 137, -47, -143, 17, 289], ![95, -137, -17, 143, -73, -113, 127, 47, -289], ![73, -143, 113, 17, -127, 137, -47, -95, 289], ![47, -113, 143, -137, 95, -17, -73, 127, -289], ![17, -47, 73, -95, 113, -127, 137, -143, 289]]
private theorem dot_wp : dotProduct w (fun r => abc (Fin.castLE (by decide) r)) = 8421 := by norm_num [dotProduct, w, abc, Fin.sum_univ_succ]
private theorem dot_wV : (fun j => dotProduct w (fun r => V r j)) = ![8295, -8385, -8313, 8383, 8271, -8345, -8169, -8417, -7225] := by funext j; fin_cases j <;> norm_num [dotProduct, w, V, Fin.sum_univ_succ]
private theorem dot_wV_le (j : Fin 9) : |dotProduct w (fun r => V r j)| ≤ 8417 := by have h := congrFun dot_wV j; rw [h]; fin_cases j <;> norm_num
private theorem strategies_are_signs : (∀ x, a x = 1 ∨ a x = -1) ∧ (∀ x, b x = 1 ∨ b x = -1) ∧ (∀ x, c x = 1 ∨ c x = -1) := by refine ⟨?_, ?_, ?_⟩ <;> intro x <;> fin_cases x <;> norm_num [a, b, c]
private def realPoint : EuclideanSpace ℝ (Fin 9) := WithLp.toLp 2 (fun r => (abc (Fin.castLE (by decide) r) : ℝ))
private def realVertex (j : Fin 9) : EuclideanSpace ℝ (Fin 9) := WithLp.toLp 2 (fun r => (V r j : ℝ))
private def ell : EuclideanSpace ℝ (Fin 9) →ₗ[ℝ] ℝ := ∑ r : Fin 9, (w r : ℝ) • (EuclideanSpace.proj r).toLinearMap
private lemma ell_realPoint : ell realPoint = 8421 := by
  have h := dot_wp; change (∑ r : Fin 9, (w r : ℝ) * (abc (Fin.castLE (by decide) r) : ℝ)) = 8421; dsimp [dotProduct] at h
  exact_mod_cast h
private lemma ell_realVertex (j : Fin 9) : |ell (realVertex j)| ≤ 8417 := by
  have h := dot_wV_le j; change |∑ r : Fin 9, (w r : ℝ) * (V r j : ℝ)| ≤ 8417; dsimp [dotProduct] at h
  exact_mod_cast h
private lemma realPoint_outside : realPoint ∉ convexHull ℝ (Set.range realVertex ∪ Set.range (fun j => -realVertex j)) := by
  intro hp; have hb : convexHull ℝ (Set.range realVertex ∪ Set.range (fun j => -realVertex j)) ⊆
      {x | ell x ≤ 8417} := by
    apply convexHull_min ?_ (convex_halfSpace_le ell.isLinear 8417)
    rintro x (⟨j,rfl⟩ | ⟨j,rfl⟩)
    · exact (le_abs_self _).trans (ell_realVertex j)
    · change ell (-realVertex j) ≤ 8417; rw [map_neg]; exact (neg_le_abs _).trans (ell_realVertex j)
  have h := hb hp; change ell realPoint ≤ 8417 at h; rw [ell_realPoint] at h; norm_num at h
private lemma strategySet_finite (N m : ℕ) : (strategySet N m).Finite := by
  classical
  let f : (Fin N → Fin m → Bool) → Tensor N m := fun b =>
    WithLp.toLp 2 (fun x => ∏ n, if b n (x n) then (1 : ℝ) else -1)
  apply (Set.finite_range f).subset
  rintro v ⟨a,ha,hv⟩
  refine ⟨fun n x => decide (a n x = 1),?_⟩
  apply PiLp.ext; intro x; rw [hv x]; change (∏ n,if decide (a n (x n)=1) then (1:ℝ) else -1) = ∏ n,a n (x n); apply Finset.prod_congr rfl; intro n hn; rcases ha n (x n) with h | h <;> norm_num [h]
private lemma d_mem_strategySet (a b c : Fin 17 → ℝ) (ha : ∀ x,a x=1 ∨ a x= -1) (hb : ∀ x,b x=1 ∨ b x= -1) (hc : ∀ x,c x=1 ∨ c x= -1) : d a b c ∈ strategySet 3 17 := by
  refine ⟨![a,b,c],?_,?_⟩
  · intro n x
    fin_cases n <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    · exact ha x
    · exact hb x
    · exact hc x
  · intro x; simp [d,Fin.prod_univ_three]
private lemma Gamma_hull (N m : ℕ) : Gamma N m '' localPolytope N m = convexHull ℝ (Gamma N m '' strategySet N m) := (Gamma N m).toLinearMap.image_convexHull _
private lemma Gamma_d_mem (a b c : Fin 17 → ℝ) (ha : ∀ x,a x=1 ∨ a x= -1) (hb : ∀ x,b x=1 ∨ b x= -1) (hc : ∀ x,c x=1 ∨ c x= -1) : Gamma 3 17 (d a b c) ∈ Gamma 3 17 '' localPolytope 3 17 := by exact ⟨_,subset_convexHull ℝ _ (d_mem_strategySet a b c ha hb hc),rfl⟩
private lemma totalCoeff_add17_mul (r : Fin 9) (t k : ℕ) : totalCoeff r (t+17*k)=(-1 : ℤ)^k*totalCoeff r t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,← Nat.add_assoc,totalCoeff_add17,ih,pow_succ]; ring
private lemma totalCoeff_add34_mul (r : Fin 9) (t k : ℕ) : totalCoeff r (t+34*k)=totalCoeff r t := by
  rw [show 34*k=17*(2*k) by ring,totalCoeff_add17_mul,pow_mul]
  norm_num
private def shiftIndex (k : Fin 3 → ℕ) (x : Fin 3 → Fin 17) : Fin 3 → Fin 17 := fun n => x n + Fin.ofNat 17 (k n)
private def shiftSign (k : Fin 3 → ℕ) (x : Fin 3 → Fin 17) : ℤ := ∏ n,(-1)^(((x n).val+k n)/17)
private lemma shiftIndex_injective (k : Fin 3 → ℕ) : Function.Injective (shiftIndex k) := by
  intro x y h; funext n
  exact add_right_cancel (congrFun h n)
private lemma shift_basis (r : Fin 9) (k : Fin 3 → ℕ) (hk : 34 ∣ ∑ n,k n) (x : Fin 3 → Fin 17) : basisCoeff r (shiftIndex k x) = shiftSign k x * basisCoeff r x := by
  let q : ℕ := ∑ n,((x n).val+k n)/17; have he : total (shiftIndex k x)+17*q = total x+ ∑ n,k n := by simp only [total,q,shiftIndex,Fin.val_add,Fin.val_ofNat,Nat.add_mod_mod]; rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro n hn; exact Nat.mod_add_div ((x n).val+k n) 17
  obtain ⟨v,hv⟩ := hk; have hs : shiftSign k x = (-1 : ℤ)^q := by exact Finset.prod_pow_eq_pow_sum _ _ _
  have hh : (-1 : ℤ)^q*totalCoeff r (total (shiftIndex k x)) = totalCoeff r (total x) := by rw [← totalCoeff_add17_mul,he,hv,totalCoeff_add34_mul]
  have hs2 : ((-1 : ℤ)^q)^2=1 := by rcases neg_one_pow_eq_or ℤ q with h | h <;> norm_num [h]
  change totalCoeff r (total (shiftIndex k x)) = shiftSign k x*totalCoeff r (total x); rw [hs,← hh]
  calc
    _ = ((-1 : ℤ)^q)^2*totalCoeff r (total (shiftIndex k x)) := by rw [hs2,one_mul]
    _ = _ := by ring
private lemma Gamma_ext {u v : Tensor 3 17} (h : ∀ r : Fin 9,⟪F r,u⟫_ℝ = ⟪F r,v⟫_ℝ) : Gamma 3 17 u=Gamma 3 17 v := by
  have hu := invariant_basis_expansion (Gamma 3 17 u) ((symSub 3 17).starProjection_apply_mem u); have hv := invariant_basis_expansion (Gamma 3 17 v) ((symSub 3 17).starProjection_apply_mem v); have hc (r : Fin 9) : ((Gamma 3 17 u) ![⟨(r).val, by omega⟩, 0, 0])=((Gamma 3 17 v) ![⟨(r).val, by omega⟩, 0, 0]) := by
    have hh := h r; rw [← Gamma_inner_basis u r,← Gamma_inner_basis v r,hu,hv,basis_inner_expansion,basis_inner_expansion] at hh
    by_cases hr : r.val=0 <;> simp only [hr,ite_true,ite_false] at hh ⊢ <;> linarith
  rw [hu,hv]; simp only [hc]
private lemma Gamma_shift (t u v : ℕ) (hsum : 34 ∣ t+u+v) (a b c : Fin 17 → ℝ) : Gamma 3 17 (d (shiftStrategy t a) (shiftStrategy u b) (shiftStrategy v c)) = Gamma 3 17 (d a b c) := by
  classical
  let k : Fin 3 → ℕ := ![t,u,v]; have hk : 34 ∣ ∑ n,k n := by simpa [k,Fin.sum_univ_three] using hsum
  let e : (Fin 3 → Fin 17) ≃ (Fin 3 → Fin 17) := Equiv.ofBijective (shiftIndex k)
    ⟨shiftIndex_injective k,Finite.surjective_of_injective (shiftIndex_injective k)⟩
  apply Gamma_ext; intro r; rw [PiLp.inner_apply,PiLp.inner_apply]; simp only [F,PiLp.toLp_apply,RCLike.inner_apply,conj_trivial]; have hterm (x : Fin 3 → Fin 17) :
      d (shiftStrategy t a) (shiftStrategy u b) (shiftStrategy v c) x * (basisCoeff r x : ℝ) =
        d a b c (e x) * (basisCoeff r (e x) : ℝ) := by
    have hb := shift_basis r k hk x; have hd : d (shiftStrategy t a) (shiftStrategy u b) (shiftStrategy v c) x =
        (shiftSign k x : ℝ)*d a b c (e x) := by
      have he : e x = fun n => ⟨((x n).val+k n)%17,by omega⟩ := by
        funext n; apply Fin.ext
        change (x n + Fin.ofNat 17 (k n)).val = _
        simp [Fin.val_add,Fin.val_ofNat,Nat.add_mod_mod]
      rw [he]
      simp only [d,PiLp.toLp_apply,shiftStrategy,shiftSign,Fin.prod_univ_three, Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one]; change _ = (-1 : ℝ)^(((x 0).val+t)/17) * (-1)^(((x 1).val+u)/17) *
        (-1)^(((x 2).val+v)/17) *
        (a ⟨((x 0).val+t)%17,by omega⟩ * b ⟨((x 1).val+u)%17,by omega⟩ * c ⟨((x 2).val+v)%17,by omega⟩)
      ring
    rw [hd]; have hbr : (basisCoeff r (e x) : ℝ)=(shiftSign k x : ℝ)*(basisCoeff r x : ℝ) := by exact_mod_cast hb
    rw [hbr]; ring
  simp_rw [hterm]; exact Equiv.sum_comp e (fun x => d a b c x*(basisCoeff r x : ℝ))
private lemma evalAt_product (z : ℂ) (a b c : Fin 17 → ℝ) : (finiteSignal (fun x => (a x : ℂ)) z)*(finiteSignal (fun x => (b x : ℂ)) z)*(finiteSignal (fun x => (c x : ℂ)) z) = ∑ x : Fin 3 → Fin 17,(d a b c x : ℂ)*z^(total x) := by
  have he : (∑ x : Fin 3 → Fin 17,(d a b c x : ℂ)*z^(total x)) =
      ∑ t : Fin 17 × Fin 17 × Fin 17,
        ((a t.1*b t.2.1*c t.2.2 : ℝ) : ℂ)*z^(t.1.val+t.2.1.val+t.2.2.val) := by
    let e : (Fin 3 → Fin 17) ≃ Fin 17 × Fin 17 × Fin 17 := (D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry.tensorTowerTupleEquiv (Fin 17) 2).symm
    apply Fintype.sum_equiv e; intro x
    have he : e x = (x 0, x 1, x 2) := rfl
    simp [d,total,he,Fin.sum_univ_three]
  rw [he,Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; dsimp [finiteSignal]; rw [Finset.sum_mul_sum,Finset.sum_mul]; simp_rw [Finset.sum_mul_sum]; apply Finset.sum_congr rfl; intro x hx; apply Finset.sum_congr rfl; intro y hy; apply Finset.sum_congr rfl; intro u hu; push_cast; rw [pow_add,pow_add]; ring
private lemma productCoeff_eval (z : ℂ) (hz : z^17= -1) (a b c : Fin 17 → ℝ) : (∑ r : Fin 17,productCoeff a b c r*(z^r.val).re) = ((finiteSignal (fun x => (a x : ℂ)) z)*(finiteSignal (fun x => (b x : ℂ)) z)*(finiteSignal (fun x => (c x : ℂ)) z)).re := by
  rw [evalAt_product,Complex.re_sum]; simp only [productCoeff]; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x hx; let r : Fin 17 := ⟨total x%17,by omega⟩; rw [Finset.sum_eq_single r]
  · simp only [r,if_pos rfl]; have he : (-1 : ℂ)^(total x/17)=Complex.ofReal ((-1 : ℝ)^(total x/17)) := by norm_cast
    simp only [ite_true]; rw [root_reduce z hz (total x),he,← mul_assoc,← Complex.ofReal_mul,Complex.re_ofReal_mul]; ring
  · intro s hs hne; have hres : total x%17≠s.val := by
      intro he; exact hne (Fin.ext he.symm)
    simp [hres]
  · simp
private lemma P_eval (z : ℂ) (hz : z^17= -1) (hn : ‖z‖=1) (a b c : Fin 17 → ℝ) : (∑ r : Fin 9,(z^r.val).re*(if r.val=0 then P a b c r else 2*P a b c r)) = ((finiteSignal (fun x => (a x : ℂ)) z)*(finiteSignal (fun x => (b x : ℂ)) z)*(finiteSignal (fun x => (c x : ℂ)) z)).re := by
  rw [← productCoeff_eval z hz]; have h1 := root_reflect z hz hn 1 (by decide); have h2 := root_reflect z hz hn 2 (by decide); have h3 := root_reflect z hz hn 3 (by decide); have h4 := root_reflect z hz hn 4 (by decide); have h5 := root_reflect z hz hn 5 (by decide); have h6 := root_reflect z hz hn 6 (by decide); have h7 := root_reflect z hz hn 7 (by decide); have h8 := root_reflect z hz hn 8 (by decide); norm_num at h1 h2 h3 h4 h5 h6 h7 h8; norm_num [P,Fin.sum_univ_succ,h1,h2,h3,h4,h5,h6,h7,h8]; let g : ℕ → ℝ := fun n => productCoeff a b c ⟨n%17,by omega⟩; have hpc (r : Fin 17) : productCoeff a b c r=g r.val := by congr 1; apply Fin.ext; exact (Nat.mod_eq_of_lt r.isLt).symm
  simp_rw [hpc]; norm_num; ring
private def ellTensor (z : ℂ) : Tensor 3 17 →L[ℝ] ℝ := ∑ r : Fin 9,(z^r.val).re • innerSL ℝ (F r)
private lemma ellTensor_Gamma (z : ℂ) (hz : z^17= -1) (hn : ‖z‖=1) (a b c : Fin 17 → ℝ) : ellTensor z (Gamma 3 17 (d a b c)) = ((finiteSignal (fun x => (a x : ℂ)) z)*(finiteSignal (fun x => (b x : ℂ)) z)*(finiteSignal (fun x => (c x : ℂ)) z)).re := by simp only [ellTensor,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply, smul_eq_mul,innerSL_apply_apply,Gamma_inner_basis,basis_inner_strategy]; exact P_eval z hz hn a b c
private lemma bellRoot_anti (j : Fin 8) : (freqPhase (2*j.val+1) 1)^17= -1 := by simp only [freqPhase, Fin.val_one, Nat.mul_one]; rw [← pow_mul,Nat.mul_comm,pow_mul,zeta_pow_card (by norm_num)]; exact (show Odd (2*j.val+1) from ⟨j.val,by omega⟩).neg_one_pow
private lemma bellRoot_norm (j : Fin 8) : ‖(freqPhase (2*j.val+1) 1)‖=1 := by
  have hz : zeta 17 = Complex.exp (((Real.pi / 17 : ℝ) : ℂ) * Complex.I) := by unfold zeta; congr 1; push_cast; ring
  simp only [freqPhase, Fin.val_one, Nat.mul_one]; change ‖zeta 17^(2*j.val+1)‖=1; rw [norm_pow, hz, Complex.norm_exp_ofReal_mul_I, one_pow]
private lemma evalAt_freq (j : Fin 8) (a : Fin 17 → ℝ) : (finiteSignal (fun x => (a x : ℂ)) ((freqPhase (2*j.val+1) 1)))=dotProduct (fun i => (a i : ℂ)) (freqPhase (2*j.val+1)) := by simp only [finiteSignal,dotProduct,freqPhase,Fin.val_one,Nat.mul_one,Nat.one_mul,← pow_mul,Nat.mul_comm]
private lemma baseSigns_formula (j : Fin 8) (x : Fin 17) :
    (sourceStrategy (Fin.castLE (by decide) j)) x = freqSign (2*j.val+1) x *
      (if (freqIndex (2*j.val+1) x).val<9 then (1:ℝ) else -1) := by
  rw [baseSigns_eq_integerBaseSigns]
  by_cases hlt : ((2*j.val+1)*x.val)%17 < 9 <;>
    simp [integerBaseSigns, freqSign, freqIndex_val, hlt]
private lemma baseStrategy_eval (j : Fin 8) : (finiteSignal (fun x => ((fun x => (sourceStrategy (Fin.castLE (by decide) j)) x) x : ℂ)) ((freqPhase (2*j.val+1) 1)))=Complex.ofReal (radius 17) := by rw [evalAt_freq]; exact baseSigns_sum j
private lemma baseStrategy_sign (j : Fin 8) : IsSign (fun x => (sourceStrategy (Fin.castLE (by decide) j)) x) := by intro x; change (sourceStrategy (Fin.castLE (by decide) j)) x = 1 ∨ (sourceStrategy (Fin.castLE (by decide) j)) x = -1; rw [baseSigns_formula]; rcases freqSign_sign (2*j.val+1) x with h | h <;> rw [h] <;> split_ifs <;> norm_num
private lemma freq_unique_max (j : Fin 8) (a b c : Fin 17 → ℝ) (ha : IsSign a) (hb : IsSign b) (hc : IsSign c) : ellTensor ((freqPhase (2*j.val+1) 1)) (Gamma 3 17 (d a b c))≤radius 17^3 ∧ (ellTensor ((freqPhase (2*j.val+1) 1)) (Gamma 3 17 (d a b c))=radius 17^3 → Gamma 3 17 (d a b c)=(fullVertex (Fin.castLE (by decide) j))) := by
  rw [ellTensor_Gamma _ (bellRoot_anti j) (bellRoot_norm j)]; have haN : ‖(finiteSignal (fun x => (a x : ℂ)) ((freqPhase (2*j.val+1) 1)))‖≤radius 17 := by rw [evalAt_freq]; exact odd_frequency_norm_le j a ha
  have hbN : ‖(finiteSignal (fun x => (b x : ℂ)) ((freqPhase (2*j.val+1) 1)))‖≤radius 17 := by rw [evalAt_freq]; exact odd_frequency_norm_le j b hb
  have hcN : ‖(finiteSignal (fun x => (c x : ℂ)) ((freqPhase (2*j.val+1) 1)))‖≤radius 17 := by rw [evalAt_freq]; exact odd_frequency_norm_le j c hc
  refine ⟨triple_bound _ radius17_pos _ _ _ haN hbN hcN,?_⟩
  intro he; obtain ⟨haE,hbE,hcE,hprod⟩ := triple_max_value _ radius17_pos _ _ _ haN hbN hcN he; rw [evalAt_freq] at haE hbE hcE; obtain ⟨t,rfl⟩ := norm_maximizers_are_rotations j a ha haE; obtain ⟨u,rfl⟩ := norm_maximizers_are_rotations j b hb hbE; obtain ⟨v,rfl⟩ := norm_maximizers_are_rotations j c hc hcE; have hphase : zeta 17^((2*j.val+1)*(t.val+u.val+v.val))=1 := by
    have ht := rotation_eval j t; have hu := rotation_eval j u; have hv := rotation_eval j v; rw [← evalAt_freq] at ht hu hv; have hm :
        ((finiteSignal (fun x => ((fun x => ((fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) t x : ℝ)) x : ℂ)) ((freqPhase (2*j.val+1) 1)))* (finiteSignal (fun x => ((fun x => ((fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) u x : ℝ)) x : ℂ)) ((freqPhase (2*j.val+1) 1)))* (finiteSignal (fun x => ((fun x => ((fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) v x : ℝ)) x : ℂ)) ((freqPhase (2*j.val+1) 1))))*
        zeta 17^((2*j.val+1)*(t.val+u.val+v.val))=Complex.ofReal (radius 17^3) := by
      rw [Nat.mul_add,Nat.mul_add,pow_add,pow_add]
      calc
        _ = ((finiteSignal (fun x => ((fun x => ((fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) t x : ℝ)) x : ℂ)) ((freqPhase (2*j.val+1) 1)))*zeta 17^((2*j.val+1)*t.val))*
            ((finiteSignal (fun x => ((fun x => ((fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) u x : ℝ)) x : ℂ)) ((freqPhase (2*j.val+1) 1)))*zeta 17^((2*j.val+1)*u.val))*
            ((finiteSignal (fun x => ((fun x => ((fun (t : Fin 34) => shiftStrategy t.val (sourceStrategy (Fin.castLE (by decide) j))) v x : ℝ)) x : ℂ)) ((freqPhase (2*j.val+1) 1)))*zeta 17^((2*j.val+1)*v.val)) := by ring
        _ = _ := by rw [ht,hu,hv]; push_cast; ring
    rw [hprod] at hm; have hr : (radius 17^3 : ℝ)≠0 := pow_ne_zero 3 (ne_of_gt radius17_pos); have hrC : Complex.ofReal (radius 17^3)≠0 := by exact_mod_cast hr
    exact (mul_left_cancel₀ hrC (by simpa using hm : Complex.ofReal (radius 17^3)*zeta 17^((2*j.val+1)*(t.val+u.val+v.val)) = Complex.ofReal (radius 17^3)*1))
  have hd := frequency_order j _ hphase; exact Gamma_shift t.val u.val v.val hd _ _ _
private lemma strategySet_as_d {q : Tensor 3 17} (hq : q∈strategySet 3 17) : ∃ a b c : Fin 17 → ℝ,IsSign a ∧ IsSign b ∧ IsSign c ∧ q=d a b c := by
  obtain ⟨a,ha,hq⟩ := hq
  refine ⟨a 0,a 1,a 2,ha 0,ha 1,ha 2,?_⟩
  apply PiLp.ext; intro x
  simpa [d,Fin.prod_univ_three] using hq x
private lemma d_neg_first (a b c : Fin 17 → ℝ) : d (-a) b c= -d a b c := by apply PiLp.ext; intro x; simp [d]
private lemma d_neg_second (a b c : Fin 17 → ℝ) : d a (-b) c= -d a b c := by apply PiLp.ext; intro x; simp [d]
private lemma d_neg_third (a b c : Fin 17 → ℝ) : d a b (-c)= -d a b c := by apply PiLp.ext; intro x; simp [d]
private lemma strategySet_neg {q : Tensor 3 17} (hq : q∈strategySet 3 17) : -q∈strategySet 3 17 := by obtain ⟨a,b,c,ha,hb,hc,rfl⟩ := strategySet_as_d hq; rw [← d_neg_first]; apply d_mem_strategySet _ _ _ _ hb hc; intro x; rcases ha x with h | h <;> simp [h]
private lemma projected_strategySet_neg {q : Tensor 3 17} (hq : q∈Gamma 3 17 '' strategySet 3 17) : -q∈Gamma 3 17 '' strategySet 3 17 := by obtain ⟨v,hv,rfl⟩ := hq; exact ⟨-v,strategySet_neg hv,map_neg _ _⟩
private lemma freqVertex_exposed (j : Fin 8) : IsExposed ℝ (Gamma 3 17 '' localPolytope 3 17) {(fullVertex (Fin.castLE (by decide) j))} := by
  have hv : (fullVertex (Fin.castLE (by decide) j))∈Gamma 3 17 '' strategySet 3 17 := ⟨_,d_mem_strategySet _ _ _ (baseStrategy_sign j) (baseStrategy_sign j) (baseStrategy_sign j),rfl⟩; have he : ellTensor ((freqPhase (2*j.val+1) 1)) ((fullVertex (Fin.castLE (by decide) j)))=radius 17^3 := by rw [fullVertex,ellTensor_Gamma _ (bellRoot_anti j) (bellRoot_norm j)]; simp only [baseStrategy_eval,← Complex.ofReal_mul,Complex.ofReal_re]; ring
  rw [Gamma_hull]; apply exposed_hull_of_unique_max _ (ellTensor ((freqPhase (2*j.val+1) 1))) ((fullVertex (Fin.castLE (by decide) j))) hv; intro x hx; obtain ⟨q,hq,rfl⟩ := hx; obtain ⟨a,b,c,ha,hb,hc,rfl⟩ := strategySet_as_d hq; rw [he]; exact freq_unique_max j a b c ha hb hc
private lemma neg_freqVertex_exposed (j : Fin 8) : IsExposed ℝ (Gamma 3 17 '' localPolytope 3 17) {-(fullVertex (Fin.castLE (by decide) j))} := by
  have hv : (fullVertex (Fin.castLE (by decide) j))∈Gamma 3 17 '' strategySet 3 17 := ⟨_,d_mem_strategySet _ _ _ (baseStrategy_sign j) (baseStrategy_sign j) (baseStrategy_sign j),rfl⟩; have hb : ∀ x∈Gamma 3 17 '' strategySet 3 17,
      ellTensor ((freqPhase (2*j.val+1) 1)) x≤ellTensor ((freqPhase (2*j.val+1) 1)) ((fullVertex (Fin.castLE (by decide) j))) ∧
      (ellTensor ((freqPhase (2*j.val+1) 1)) x=ellTensor ((freqPhase (2*j.val+1) 1)) ((fullVertex (Fin.castLE (by decide) j))) → x=(fullVertex (Fin.castLE (by decide) j))) := by
    intro x hx; obtain ⟨q,hq,rfl⟩ := hx; obtain ⟨a,b,c,ha,hb,hc,rfl⟩ := strategySet_as_d hq; have he : ellTensor ((freqPhase (2*j.val+1) 1)) ((fullVertex (Fin.castLE (by decide) j)))=radius 17^3 := by rw [fullVertex,ellTensor_Gamma _ (bellRoot_anti j) (bellRoot_norm j)]; simp only [baseStrategy_eval,← Complex.ofReal_mul,Complex.ofReal_re]; ring
    rw [he]; exact freq_unique_max j a b c ha hb hc
  rw [Gamma_hull]; apply exposed_hull_of_unique_max _ (-ellTensor ((freqPhase (2*j.val+1) 1))) (-(fullVertex (Fin.castLE (by decide) j))) (projected_strategySet_neg hv); exact negative_unique_max _ (fun x hx => projected_strategySet_neg hx) (ellTensor ((freqPhase (2*j.val+1) 1))).toLinearMap _ hb
private lemma sourceStrategy_last : sourceStrategy 8=(fun x : Fin 17 => (-1 : ℝ)^x.val) := by
  funext x; simp only [sourceStrategy]; have hidx : ((8 : Fin 9).val : ℝ)=8 := by norm_num
  rw [hidx]; have he : Real.pi*(2*(8:ℝ)+1)*x.val/17=x.val*Real.pi := by ring
  rw [he,Real.cos_nat_mul_pi]; rcases neg_one_pow_eq_or ℝ x.val with h | h <;> norm_num [h,Real.sign]
private def altSum (a : Fin 17 → ℝ) : ℝ := ∑ x,a x*(-1 : ℝ)^x.val
private lemma altStrategy_sign : IsSign (fun x : Fin 17 => (-1 : ℝ)^x.val) := by intro x; exact neg_one_pow_eq_or ℝ _
private lemma alt_terms_sign (a : Fin 17 → ℝ) (ha : IsSign a) (x : Fin 17) : a x*(-1 : ℝ)^x.val=1 ∨ a x*(-1 : ℝ)^x.val= -1 := by rcases ha x with h | h <;> rcases altStrategy_sign x with hs | hs <;> simp [h,hs]
private lemma altSum_bound (a : Fin 17 → ℝ) (ha : IsSign a) : |altSum a|≤17 := by
  apply abs_le.mpr; constructor
  · have hh : (∑ x : Fin 17,(-1 : ℝ))≤altSum a := by
      apply Finset.sum_le_sum; intro x hx; rcases alt_terms_sign a ha x with h | h <;> linarith
    norm_num at hh; exact hh
  · have hh : altSum a≤∑ x : Fin 17,(1 : ℝ) := by
      apply Finset.sum_le_sum; intro x hx; rcases alt_terms_sign a ha x with h | h <;> linarith
    norm_num at hh; exact hh
private lemma altSum_eq_pos (a : Fin 17 → ℝ) (ha : IsSign a) (he : altSum a=17) : a=(fun x : Fin 17 => (-1 : ℝ)^x.val) := by
  have hz : (∑ x : Fin 17,(1-a x*(-1 : ℝ)^x.val))=0 := by rw [Finset.sum_sub_distrib]; change (∑ x : Fin 17,(1:ℝ))-altSum a=0; rw [he]; norm_num
  have hnon : ∀ x∈(Finset.univ : Finset (Fin 17)),0≤1-a x*(-1 : ℝ)^x.val := by intro x hx; rcases alt_terms_sign a ha x with h | h <;> linarith
  have ht := (Finset.sum_eq_zero_iff_of_nonneg hnon).mp hz; funext x; have h := ht x (Finset.mem_univ x); rcases altStrategy_sign x with hs | hs <;> change (-1 : ℝ)^x.val = _ at hs <;> rw [hs] at h ⊢ <;> linarith
private lemma altSum_neg (a : Fin 17 → ℝ) : altSum (-a)= -altSum a := by simp [altSum,Finset.sum_neg_distrib]
private lemma altSum_eq_neg (a : Fin 17 → ℝ) (ha : IsSign a) (he : altSum a= -17) : a= -(fun x : Fin 17 => (-1 : ℝ)^x.val) := by
  have hn : IsSign (-a) := by intro x; rcases ha x with h | h <;> simp [h]
  have hp := altSum_eq_pos (-a) hn (by rw [altSum_neg,he]; norm_num); have heq := congrArg Neg.neg hp
  simpa using heq
private lemma evalAt_alt (a : Fin 17 → ℝ) : (finiteSignal (fun x => (a x : ℂ)) (-1))=Complex.ofReal (altSum a) := by simp only [altSum,Complex.ofReal_sum,finiteSignal]; apply Finset.sum_congr rfl; intro x hx; simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
private lemma alt_norm_max (a : Fin 17 → ℝ) (ha : IsSign a) (he : ‖(finiteSignal (fun x => (a x : ℂ)) (-1))‖=17) : a=(fun x : Fin 17 => (-1 : ℝ)^x.val) ∨ a= -(fun x : Fin 17 => (-1 : ℝ)^x.val) := by
  rw [evalAt_alt,Complex.norm_real,Real.norm_eq_abs] at he
  by_cases hs : 0≤altSum a
  · rw [abs_of_nonneg hs] at he; exact Or.inl (altSum_eq_pos a ha he)
  · rw [abs_of_neg (lt_of_not_ge hs)] at he; exact Or.inr (altSum_eq_neg a ha (by linarith))
private lemma alt_eval_norm_le (a : Fin 17 → ℝ) (ha : IsSign a) : ‖(finiteSignal (fun x => (a x : ℂ)) (-1))‖≤17 := by rw [evalAt_alt,Complex.norm_real,Real.norm_eq_abs]; exact altSum_bound a ha
private lemma alt_unique_max (a b c : Fin 17 → ℝ) (ha : IsSign a) (hb : IsSign b) (hc : IsSign c) : ellTensor (-1) (Gamma 3 17 (d a b c))≤17^3 ∧ (ellTensor (-1) (Gamma 3 17 (d a b c))=17^3 → Gamma 3 17 (d a b c)=(fullVertex 8)) := by
  rw [ellTensor_Gamma _ (by norm_num) (by norm_num)]; have haN := alt_eval_norm_le a ha; have hbN := alt_eval_norm_le b hb; have hcN := alt_eval_norm_le c hc
  refine ⟨triple_bound 17 (by norm_num) _ _ _ haN hbN hcN,?_⟩
  intro he; obtain ⟨haE,hbE,hcE,_⟩ := triple_max_value 17 (by norm_num) _ _ _ haN hbN hcN he; rcases alt_norm_max a ha haE with rfl | rfl <;>
    rcases alt_norm_max b hb hbE with rfl | rfl <;>
    rcases alt_norm_max c hc hcE with rfl | rfl
  all_goals norm_num [finiteSignal,Fin.sum_univ_succ] at he
  all_goals simp [fullVertex,sourceStrategy_last,d_neg_first,d_neg_second,d_neg_third]
private lemma altVertex_generator : (fullVertex 8)∈Gamma 3 17 '' strategySet 3 17  := by rw [fullVertex,sourceStrategy_last]; exact ⟨_,d_mem_strategySet _ _ _ altStrategy_sign altStrategy_sign altStrategy_sign,rfl⟩
private lemma altVertex_value : ellTensor (-1) (fullVertex 8)=17^3 := by rw [fullVertex,sourceStrategy_last,ellTensor_Gamma _ (by norm_num) (by norm_num)]; norm_num [finiteSignal, Fin.sum_univ_succ]
private lemma altVertex_exposed : IsExposed ℝ (Gamma 3 17 '' localPolytope 3 17) {(fullVertex 8)} := by rw [Gamma_hull]; apply exposed_hull_of_unique_max _ (ellTensor (-1)) (fullVertex 8) altVertex_generator; intro x hx; obtain ⟨q,hq,rfl⟩ := hx; obtain ⟨a,b,c,ha,hb,hc,rfl⟩ := strategySet_as_d hq; rw [altVertex_value]; exact alt_unique_max a b c ha hb hc
private lemma neg_altVertex_exposed : IsExposed ℝ (Gamma 3 17 '' localPolytope 3 17) {-(fullVertex 8)} := by
  have hb : ∀ x∈Gamma 3 17 '' strategySet 3 17,
      ellTensor (-1) x≤ellTensor (-1) (fullVertex 8) ∧ (ellTensor (-1) x=ellTensor (-1) (fullVertex 8) → x=(fullVertex 8)) := by
    intro x hx; obtain ⟨q,hq,rfl⟩ := hx; obtain ⟨a,b,c,ha,hb,hc,rfl⟩ := strategySet_as_d hq; rw [altVertex_value]; exact alt_unique_max a b c ha hb hc
  rw [Gamma_hull]; apply exposed_hull_of_unique_max _ (-ellTensor (-1)) (-(fullVertex 8)) (projected_strategySet_neg altVertex_generator); exact negative_unique_max _ (fun x hx => projected_strategySet_neg hx) (ellTensor (-1)).toLinearMap _ hb
private lemma tensorCoords_basis (r s : Fin 9) : ((F r) ![⟨(s).val, by omega⟩, 0, 0])=if r=s then 1 else 0 := by
  have hr := r.isLt; have hs := s.isLt; have ht : total ![(⟨s.val,by omega⟩ : Fin 17),0,0]=s.val := by simp [total,Fin.sum_univ_three]
  have hsm : s.val%17=s.val := Nat.mod_eq_of_lt (by omega); have hsd : s.val/17=0 := Nat.div_eq_of_lt (by omega); have hne : s.val≠17-r.val := by omega
  dsimp [F]; simp only [basisCoeff, totalCoeff,ht,hsm,hsd,pow_zero,one_mul,hne,false_and,ite_false,Int.cast_ite,Int.cast_one,Int.cast_zero]
  by_cases h : r=s
  · subst s
    simp
  · have hval : s.val≠r.val := by intro he; exact h (Fin.ext he.symm)
    simp [h,hval]
private lemma tensorCoords_expansion (v : Fin 9 → ℝ) (r : Fin 9) : ((∑ s : Fin 9,v s • F s) ![⟨(r).val, by omega⟩, 0, 0])=v r := by change (WithLp.ofLp (∑ s : Fin 9,v s • F s)) ![⟨r.val,by omega⟩,0,0]=_; rw [WithLp.ofLp_sum]; simp only [Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul]; change (∑ s : Fin 9,v s*((F s) ![⟨(r).val, by omega⟩, 0, 0]))=v r; simp [tensorCoords_basis]
private lemma projection_coords (a b c : Fin 17 → ℝ) (r : Fin 9) : ((Gamma 3 17 (d a b c)) ![⟨(r).val, by omega⟩, 0, 0])=P a b c r/289 := by rw [projection_formula,tensorCoords_expansion]
private def thirdIndex (r a b : Fin 17) : Fin 17 := r-a-b
private lemma thirdIndex_total (r a b : Fin 17) : (a.val+b.val+(thirdIndex r a b).val)%17=r.val := by simp only [thirdIndex,Fin.sub_def]; have hr := r.isLt; have ha := a.isLt; have hb := b.isLt; omega
private lemma productCoeff_double (a b c : Fin 17 → ℝ) (r : Fin 17) : productCoeff a b c r = ∑ x : Fin 17,∑ y : Fin 17, (-1 : ℝ)^((x.val+y.val+(thirdIndex r x y).val)/17)*a x*b y*c (thirdIndex r x y) := by
  classical
  have he : productCoeff a b c r = ∑ t : Fin 17 × Fin 17 × Fin 17,
      if (t.1.val+t.2.1.val+t.2.2.val)%17=r.val then
        (-1 : ℝ)^((t.1.val+t.2.1.val+t.2.2.val)/17)*a t.1*b t.2.1*c t.2.2 else 0 := by
    let e : (Fin 3 → Fin 17) ≃ Fin 17 × Fin 17 × Fin 17 := (D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry.tensorTowerTupleEquiv (Fin 17) 2).symm
    apply Fintype.sum_equiv e; intro x
    have he : e x = (x 0, x 1, x 2) := rfl
    simp [productCoeff,total,d,he,Fin.sum_univ_three]; ring
  rw [he,Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro x hx; apply Finset.sum_congr rfl; intro y hy; rw [Finset.sum_eq_single (thirdIndex r x y)]
  · rw [if_pos (thirdIndex_total r x y)]
  · intro z hz hne; have hres : (x.val+y.val+z.val)%17≠r.val := by
      intro hh; have hh' := thirdIndex_total r x y; have hez : z=thirdIndex r x y := by apply Fin.ext; omega
      exact hne hez
    simp [hres]
  · simp
private def intProductCoeff (a b c : Fin 17 → ℤ) (r : Fin 17) : ℤ := ∑ x : Fin 17,∑ y : Fin 17,
    (-1 : ℤ)^((x.val+y.val+(thirdIndex r x y).val)/17)*a x*b y*c (thirdIndex r x y)
private lemma productCoeff_cast (a b c : Fin 17 → ℤ) (r : Fin 17) : productCoeff (fun x => (a x : ℝ)) (fun x => (b x : ℝ)) (fun x => (c x : ℝ)) r = (intProductCoeff a b c r : ℝ) := by rw [productCoeff_double]; simp only [intProductCoeff,Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one]
private lemma certificate_productCoeff : intProductCoeff a b c = abc := by funext r; fin_cases r <;> decide
private lemma certificate_P : P (fun x => (a x : ℝ)) (fun x => (b x : ℝ)) (fun x => (c x : ℝ)) = fun r => (abc (Fin.castLE (by decide) r) : ℝ) := by funext r; simp only [P,productCoeff_cast,certificate_productCoeff]; fin_cases r <;> norm_num [abc, Fin.castLE]
private def fullBaseSigns (j : Fin 9) (x : Fin 17) : ℤ := if h : j.val<8 then integerBaseSigns ⟨j.val,h⟩ x
  else (-1)^x.val
private lemma baseSigns_eq_fullBaseSigns (j : Fin 8) (x : Fin 17) :
    (sourceStrategy (Fin.castLE (by decide) j)) x = (fullBaseSigns ⟨j.val, by omega⟩ x : ℝ) := by
  simpa only [fullBaseSigns, dif_pos j.isLt] using baseSigns_eq_integerBaseSigns j x
private def intP2 (a b c : Fin 17 → ℤ) (r : Fin 9) : ℤ := if h : r.val=0 then 2*intProductCoeff a b c 0 else
    intProductCoeff a b c ⟨r.val,by omega⟩-intProductCoeff a b c ⟨17-r.val,by omega⟩
private lemma P_cast_intP2 (a b c : Fin 17 → ℤ) (r : Fin 9) : P (fun x => (a x : ℝ)) (fun x => (b x : ℝ)) (fun x => (c x : ℝ)) r=(intP2 a b c r : ℝ)/2 := by
  simp only [P,productCoeff_cast,intP2]
  split_ifs <;> push_cast <;> ring
private lemma full_vertices_data_0 (r : Fin 9) : intP2 (fullBaseSigns 0) (fullBaseSigns 0) (fullBaseSigns 0) r = 2*V r 0 := by fin_cases r <;> decide
private lemma full_vertices_data_1 (r : Fin 9) : intP2 (fullBaseSigns 1) (fullBaseSigns 1) (fullBaseSigns 1) r = 2*V r 1 := by fin_cases r <;> decide
private lemma full_vertices_data_2 (r : Fin 9) : intP2 (fullBaseSigns 2) (fullBaseSigns 2) (fullBaseSigns 2) r = 2*V r 2 := by fin_cases r <;> decide
private lemma full_vertices_data_3 (r : Fin 9) : intP2 (fullBaseSigns 3) (fullBaseSigns 3) (fullBaseSigns 3) r = 2*V r 3 := by fin_cases r <;> decide
private lemma full_vertices_data_4 (r : Fin 9) : intP2 (fullBaseSigns 4) (fullBaseSigns 4) (fullBaseSigns 4) r = 2*V r 4 := by fin_cases r <;> decide
private lemma full_vertices_data_5 (r : Fin 9) : intP2 (fullBaseSigns 5) (fullBaseSigns 5) (fullBaseSigns 5) r = 2*V r 5 := by fin_cases r <;> decide
private lemma full_vertices_data_6 (r : Fin 9) : intP2 (fullBaseSigns 6) (fullBaseSigns 6) (fullBaseSigns 6) r = 2*V r 6 := by fin_cases r <;> decide
private lemma full_vertices_data_7 (r : Fin 9) : intP2 (fullBaseSigns 7) (fullBaseSigns 7) (fullBaseSigns 7) r = 2*V r 7 := by fin_cases r <;> decide
private lemma full_vertices_data_8 (r : Fin 9) : intP2 (fullBaseSigns 8) (fullBaseSigns 8) (fullBaseSigns 8) r = 2*V r 8 := by fin_cases r <;> decide
private lemma full_vertices_data (j : Fin 9) (r : Fin 9) : intP2 (fullBaseSigns j) (fullBaseSigns j) (fullBaseSigns j) r = 2*V r j := by
  fin_cases j
  · exact full_vertices_data_0 r
  · exact full_vertices_data_1 r
  · exact full_vertices_data_2 r
  · exact full_vertices_data_3 r
  · exact full_vertices_data_4 r
  · exact full_vertices_data_5 r
  · exact full_vertices_data_6 r
  · exact full_vertices_data_7 r
  · exact full_vertices_data_8 r
private lemma full_vertices_P (j : Fin 9) : P (fun x => (fullBaseSigns j x : ℝ)) (fun x => (fullBaseSigns j x : ℝ)) (fun x => (fullBaseSigns j x : ℝ))=fun r => (V r j : ℝ) := by funext r; rw [P_cast_intP2,full_vertices_data]; push_cast; ring
private lemma sourceStrategy_full (j : Fin 9) : sourceStrategy j=fun x => (fullBaseSigns j x : ℝ) := by
  by_cases hj : j.val<8
  · have h : sourceStrategy j = fun x => (sourceStrategy (Fin.castLE (by decide) (⟨j.val,hj⟩ : Fin 8))) x := rfl
    let j9 : Fin 9 := ⟨j.val, by omega⟩
    calc
      sourceStrategy j = sourceStrategy j9 := by congr
      _ = fun x => (sourceStrategy (Fin.castLE (by decide) (⟨j.val,hj⟩ : Fin 8))) x := h
      _ = fun x => (fullBaseSigns j x : ℝ) := by funext x; exact baseSigns_eq_fullBaseSigns ⟨j.val,hj⟩ x
  · have he : j=8 := Fin.ext (by omega); subst j; rw [sourceStrategy_last]; funext x; simp [fullBaseSigns]
private def coordMap : Tensor 3 17 →ₗ[ℝ] EuclideanSpace ℝ (Fin 9) := (EuclideanSpace.equiv (Fin 9) ℝ).symm.toLinearMap.comp
    (LinearMap.pi fun r : Fin 9 =>
      (289 : ℝ) • (EuclideanSpace.proj (![⟨r.val, by omega⟩, 0, 0] : Fin 3 → Fin 17)).toLinearMap)
private lemma coord_fullVertex (j : Fin 9) : coordMap (fullVertex j)=realVertex j := by apply PiLp.ext; intro r; change 289*((Gamma 3 17 (d _ _ _)) ![⟨(r).val, by omega⟩, 0, 0])=(V r j : ℝ); rw [projection_coords]; simp only [sourceStrategy_full,full_vertices_P]; ring
private lemma fullVertex_exposed (j : Fin 9) : IsExposed ℝ (Gamma 3 17 '' localPolytope 3 17) {fullVertex j} := by
  by_cases hj : j.val<8
  · let k : Fin 8 := ⟨j.val,hj⟩
    have he : fullVertex j=(fullVertex (Fin.castLE (by decide) k)) := rfl; rw [he]; exact freqVertex_exposed k
  · have he : j=8 := Fin.ext (by omega); subst j; exact altVertex_exposed
private lemma neg_fullVertex_exposed (j : Fin 9) : IsExposed ℝ (Gamma 3 17 '' localPolytope 3 17) {-fullVertex j} := by
  by_cases hj : j.val<8
  · let k : Fin 8 := ⟨j.val,hj⟩
    have he : fullVertex j=(fullVertex (Fin.castLE (by decide) k)) := rfl; rw [he]; exact neg_freqVertex_exposed k
  · have he : j=8 := Fin.ext (by omega); subst j; exact neg_altVertex_exposed
private def signedVertex (i : Fin 18) : Tensor 3 17 := if h : i.val<9 then fullVertex ⟨i.val,h⟩ else -fullVertex ⟨i.val-9,by omega⟩
private def signedIntVertex (i : Fin 18) (r : Fin 9) : ℤ := if h : i.val<9 then V r ⟨i.val,h⟩ else -V r ⟨i.val-9,by omega⟩
private def candidateSet : Set (Tensor 3 17) := Set.range fullVertex ∪ Set.range (fun j => -fullVertex j)
private lemma signedInt_pair_injective : Function.Injective (fun i : Fin 18 => (signedIntVertex i 0,signedIntVertex i 1)) := by decide
private lemma coord_signedVertex (i : Fin 18) : coordMap (signedVertex i)= WithLp.toLp 2 (fun r => (signedIntVertex i r : ℝ)) := by
  by_cases hi : i.val<9
  · simp only [signedVertex,signedIntVertex,dif_pos hi,coord_fullVertex]
    rfl
  · simp only [signedVertex,signedIntVertex,dif_neg hi,map_neg,coord_fullVertex]; apply PiLp.ext; intro r; simp [realVertex]
private lemma signedVertex_injective : Function.Injective signedVertex := by
  intro i j hij; have hh := congrArg coordMap hij; rw [coord_signedVertex,coord_signedVertex] at hh; have h0 := congrArg (fun q : EuclideanSpace ℝ (Fin 9) => q 0) hh; have h1 := congrArg (fun q : EuclideanSpace ℝ (Fin 9) => q 1) hh; change (signedIntVertex i 0 : ℝ)=(signedIntVertex j 0 : ℝ) at h0; change (signedIntVertex i 1 : ℝ)=(signedIntVertex j 1 : ℝ) at h1; have hz0 : signedIntVertex i 0=signedIntVertex j 0 := by exact_mod_cast h0
  have hz1 : signedIntVertex i 1=signedIntVertex j 1 := by exact_mod_cast h1
  exact signedInt_pair_injective (Prod.ext hz0 hz1)
private lemma signedVertex_mem (i : Fin 18) : signedVertex i∈candidateSet := by
  by_cases hi : i.val<9
  · simp only [signedVertex,dif_pos hi,candidateSet]; exact Or.inl ⟨⟨i.val,hi⟩,rfl⟩
  · simp only [signedVertex,dif_neg hi,candidateSet]; exact Or.inr ⟨⟨i.val-9,by omega⟩,rfl⟩
private lemma signedVertex_extreme (i : Fin 18) : signedVertex i∈ (Gamma 3 17 '' localPolytope 3 17).extremePoints ℝ := by
  by_cases hi : i.val<9
  · simp only [signedVertex,dif_pos hi]; exact (fullVertex_exposed ⟨i.val,hi⟩).isExtreme.mem_extremePoints
  · simp only [signedVertex,dif_neg hi]; exact (neg_fullVertex_exposed ⟨i.val-9,by omega⟩).isExtreme.mem_extremePoints
private def extraPoint : Tensor 3 17 := Gamma 3 17 (d (fun x => (a x : ℝ)) (fun x => (b x : ℝ)) (fun x => (c x : ℝ)))
private lemma extraPoint_mem : extraPoint∈Gamma 3 17 '' localPolytope 3 17 := by
  obtain ⟨ha,hb,hc⟩ := strategies_are_signs; apply Gamma_d_mem
  · intro x
    exact_mod_cast ha x
  · intro x
    exact_mod_cast hb x
  · intro x
    exact_mod_cast hc x
private lemma coord_extraPoint : coordMap extraPoint=realPoint := by apply PiLp.ext; intro r; change 289*((Gamma 3 17 (d _ _ _)) ![⟨(r).val, by omega⟩, 0, 0])=(abc (Fin.castLE (by decide) r) : ℝ); rw [projection_coords,certificate_P]; ring
private lemma coord_candidateSet : coordMap '' candidateSet = Set.range realVertex ∪ Set.range (fun j => -realVertex j) := by simp only [candidateSet,Set.image_union,← Set.range_comp,Function.comp_def,map_neg,coord_fullVertex]
private lemma extraPoint_outside : extraPoint∉convexHull ℝ candidateSet := by intro hh; have him : coordMap extraPoint∈coordMap '' convexHull ℝ candidateSet := Set.mem_image_of_mem coordMap hh; rw [coordMap.image_convexHull,coord_candidateSet,coord_extraPoint] at him; exact realPoint_outside him
private lemma nineteen_extreme : ∃ g : Fin 19 → Tensor 3 17,Function.Injective g ∧ ∀ i,g i∈(Gamma 3 17 '' localPolytope 3 17).extremePoints ℝ := by
  let T := Gamma 3 17 '' strategySet 3 17; have hT : T.Finite := (strategySet_finite 3 17).image (Gamma 3 17); have hp : extraPoint∈convexHull ℝ T := by rw [← Gamma_hull]; exact extraPoint_mem
  obtain ⟨q,hq,hout⟩ := extra_extreme_of_separation T candidateSet hT hp extraPoint_outside; have hqext : q∈(Gamma 3 17 '' localPolytope 3 17).extremePoints ℝ := by rw [Gamma_hull]; exact hq
  let g : Fin 19 → Tensor 3 17 := fun i => if h : i.val<18 then signedVertex ⟨i.val,h⟩ else q
  refine ⟨g,?_,?_⟩
  · intro i j hij
    by_cases hi : i.val<18 <;> by_cases hj : j.val<18
    · have he := signedVertex_injective (by simpa only [g,dif_pos hi,dif_pos hj] using hij); apply Fin.ext; exact congrArg (fun x : Fin 18 => x.val) he
    · have he : signedVertex ⟨i.val,hi⟩=q := by simpa only [g,dif_pos hi,dif_neg hj] using hij
      exact False.elim (hout (he ▸ signedVertex_mem ⟨i.val,hi⟩))
    · have he : q=signedVertex ⟨j.val,hj⟩ := by simpa only [g,dif_neg hi,dif_pos hj] using hij
      exact False.elim (hout (he.symm ▸ signedVertex_mem ⟨j.val,hj⟩))
    · apply Fin.ext; omega
  · intro i
    by_cases hi : i.val<18
    · simpa only [g,dif_pos hi] using signedVertex_extreme ⟨i.val,hi⟩
    · simpa only [g,dif_neg hi] using hqext
theorem result : ¬ claim := by
  intro hclaim; obtain ⟨g,hg,hext⟩ := nineteen_extreme; have hconv : Convex ℝ (Gamma 3 17 '' localPolytope 3 17) := by rw [Gamma_hull]; exact convex_convexHull ℝ _
  have htransport : crossPolytope 9 = convexHull ℝ
      (Set.range (fun i : Fin 9 => EuclideanSpace.single i (1 : ℝ)) ∪ Set.range (fun i : Fin 9 => -EuclideanSpace.single i (1 : ℝ))) := by
    unfold crossPolytope D5.S3.Combinatorics.Geometry.CrossPolytopeFaceCounts.crossHull; change ((EuclideanSpace.equiv (Fin 9) ℝ).symm.toLinearMap : (Fin 9 → ℝ) → EuclideanSpace ℝ (Fin 9)) '' convexHull ℝ _ = _; rw [LinearMap.image_convexHull]; congr 1
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_univ, true_and, Set.mem_union, Set.mem_range]
    constructor
    · rintro ⟨y, ⟨i, rfl | rfl⟩, rfl⟩
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr ⟨i, by simp only [map_neg]; rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Pi.single i 1, ⟨i, Or.inl rfl⟩, rfl⟩
      · exact ⟨-Pi.single i 1, ⟨i, Or.inr rfl⟩, by simp only [map_neg]; rfl⟩
  have hno := not_affine_cross_of_many_extreme _ hconv g hg hext; obtain ⟨f, hf, him⟩ := hclaim 3 17 (by norm_num) (by norm_num); exact hno ⟨f, hf, him.trans htransport⟩
end D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope
