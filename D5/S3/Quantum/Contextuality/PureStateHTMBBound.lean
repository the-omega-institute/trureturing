/- GID: D5/S3/Quantum/Contextuality/PureStateHTMBBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Contextuality/PureStateHTMBBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Pure preparations obey the two-trit HTMB noncontextuality bound. -/

import D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
The HTMB scenario and pure-state conjecture of Tavakoli, Zambrini Cruzeiro, Uola and Abbott,
arXiv:2010.04751v3, equations (32)–(33). Both trit parity equivalences are imposed.
The resulting additive projector grid either has a constant axis or has both axes in one plane.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
open D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity (projector)

namespace D5.S3.Quantum.Contextuality.PureStateHTMBBound

/-- The average probability of correctly guessing one of the two uniformly chosen trits. -/
def htmbValue {d : ℕ} (ψ : ZMod 3 × ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m n : ZMod 3 → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (1 / 18) * ∑ x, ((projector (ψ x) * m x.1).trace.re +
    (projector (ψ x) * n x.2).trace.re)

/-- Pure preparations satisfying both parity equivalences cannot violate the HTMB inequality. -/
def claim : Prop :=
  ∀ (d : ℕ) (ψ : ZMod 3 × ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m n : ZMod 3 → Matrix (Fin d) (Fin d) ℂ),
    (∀ x, ‖ψ x‖ = 1) →
    ((∀ b, (m b).PosSemidef) ∧ ∑ b, m b = 1) →
    ((∀ b, (n b).PosSemidef) ∧ ∑ b, n b = 1) →
    (∀ a ∈ ({1, 2} : Finset (ZMod 3)), ∀ k : ZMod 3,
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = k),
        projector (ψ x) =
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = 0),
        projector (ψ x)) →
    htmbValue ψ m n ≤ 2 / 3

private theorem sum_trit {α : Type*} [AddCommMonoid α] (f : ZMod 3 → α) :
    ∑ i, f i = f 0 + f 1 + f 2 := by
  exact Fin.sum_univ_three f

private theorem additive_form {d : ℕ}
    (p : ZMod 3 × ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ a ∈ ({1, 2} : Finset (ZMod 3)), ∀ k : ZMod 3,
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = k), p x =
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = 0), p x)
    (i j : ZMod 3) : p (i, j) = p (i, 0) + p (0, j) - p (0, 0) := by
  apply Matrix.ext
  intro u v
  have hs (a : ZMod 3) (ha : a ∈ ({1, 2} : Finset (ZMod 3))) (k : ZMod 3) :
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = k),
        (p x) u v =
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = 0),
        (p x) u v := by
    simpa only [Matrix.sum_apply] using
      congrArg (fun q : Matrix (Fin d) (Fin d) ℂ => q u v) (h a ha k)
  have e11 := hs 1 (by simp) 1
  have e12 := hs 1 (by simp) 2
  have e21 := hs 2 (by simp) 1
  have e22 := hs 2 (by simp) 2
  simp only [Finset.sum_filter, Fintype.sum_prod_type, sum_trit] at e11 e12 e21 e22
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  have h30 : (3 : ZMod 3) = 0 := rfl
  have h41 : (4 : ZMod 3) = 1 := rfl
  have h52 : (5 : ZMod 3) = 2 := rfl
  have h60 : (6 : ZMod 3) = 0 := rfl
  norm_num at e11 e12 e21 e22
  simp only [h30, h41, h52, h60, h01, h02, h12, Ne.symm h01, Ne.symm h02,
    Ne.symm h12, ite_true, ite_false, add_zero, zero_add] at e11 e12 e21 e22
  change (p (i, j)) u v = (p (i, 0)) u v + (p (0, j)) u v - (p (0, 0)) u v
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  all_goals first
    | (solve | ring)
    | linear_combination (-2 / 3 : ℂ) * e11 + (1 / 3 : ℂ) * e12 -
        (1 / 3 : ℂ) * e21 - (1 / 3 : ℂ) * e22
    | linear_combination -(1 / 3 : ℂ) * e11 - (1 / 3 : ℂ) * e12 -
        (2 / 3 : ℂ) * e21 + (1 / 3 : ℂ) * e22
    | linear_combination -(1 / 3 : ℂ) * e11 - (1 / 3 : ℂ) * e12 +
        (1 / 3 : ℂ) * e21 - (2 / 3 : ℂ) * e22
    | linear_combination (1 / 3 : ℂ) * e11 - (2 / 3 : ℂ) * e12 -
        (1 / 3 : ℂ) * e21 - (1 / 3 : ℂ) * e22

private theorem projector_difference_span {d : ℕ}
    (a b c e : EuclideanSpace ℂ (Fin d))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (_hc : ‖c‖ = 1) (_he : ‖e‖ = 1)
    (h : projector a - projector b = projector c - projector e)
    (hne : projector c - projector e ≠ 0) :
    a ∈ Submodule.span ℂ ({c, e} : Set (EuclideanSpace ℂ (Fin d))) ∧
    b ∈ Submodule.span ℂ ({c, e} : Set (EuclideanSpace ℂ (Fin d))) := by
  classical
  have ha0 : a ≠ 0 := by
    intro hz
    simp [hz] at ha
  have hab : LinearIndependent ℂ ![a, b] := by
    apply (LinearIndependent.pair_iff' ha0).2
    intro z hz
    have hz1 : ‖z‖ = 1 := by
      have hn := hb
      rw [← hz, norm_smul, ha, mul_one] at hn
      exact hn
    have hp : projector b = projector a := by
      rw [← hz]
      ext r t
      change (z * a r) * star (z * a t) = a r * star (a t)
      rw [star_mul]
      calc
        _ = (z * star z) * (a r * star (a t)) := by ring
        _ = _ := by simp only [RCLike.star_def, Complex.mul_conj', hz1, one_pow, Complex.ofReal_one,
          one_mul]
    apply hne
    rw [← h, hp, sub_self]
  let s := Submodule.span ℂ ({c, e} : Set (EuclideanSpace ℂ (Fin d)))
  have hc_mem : c ∈ s := Submodule.subset_span (by simp)
  have he_mem : e ∈ s := Submodule.subset_span (by simp)
  have hw (w : EuclideanSpace ℂ (Fin d)) (hw : w ∈ sᗮ) :
      ⟪a, w⟫_ℂ = 0 ∧ ⟪b, w⟫_ℂ = 0 := by
    have hcw := Submodule.inner_right_of_mem_orthogonal hc_mem hw
    have hew := Submodule.inner_right_of_mem_orthogonal he_mem hw
    have heq : ⟪a, w⟫_ℂ • a = ⟪b, w⟫_ℂ • b := by
      have hh := congrArg (fun q : Matrix (Fin d) (Fin d) ℂ => q *ᵥ w.ofLp) h
      have hh0 : (projector c - projector e) *ᵥ w.ofLp = 0 := by
        rw [Matrix.sub_mulVec, projector, projector, vecMulVec_mulVec, vecMulVec_mulVec]
        rw [dotProduct_comm (fun k => star (c k)), dotProduct_comm (fun k => star (e k))]
        change MulOpposite.op ⟪c, w⟫_ℂ • c.ofLp -
          MulOpposite.op ⟪e, w⟫_ℂ • e.ofLp = 0
        rw [hcw, hew]
        simp
      rw [hh0, Matrix.sub_mulVec, sub_eq_zero] at hh
      rw [projector, projector, vecMulVec_mulVec, vecMulVec_mulVec] at hh
      rw [dotProduct_comm (fun k => star (a k)), dotProduct_comm (fun k => star (b k))] at hh
      simp only [op_smul_eq_smul] at hh
      apply WithLp.ofLp_injective 2
      change (⟪a, w⟫_ℂ • a).ofLp = (⟪b, w⟫_ℂ • b).ofLp at hh
      exact hh
    exact hab.eq_zero_of_pair' heq
  constructor
  · change a ∈ s
    rw [← s.orthogonal_orthogonal]
    exact (sᗮ.mem_orthogonal' a).2 fun w hw_mem => (hw w hw_mem).1
  · change b ∈ s
    rw [← s.orthogonal_orthogonal]
    exact (sᗮ.mem_orthogonal' b).2 fun w hw_mem => (hw w hw_mem).2

private theorem overlap_le_basis {d : ℕ}
    (s : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (v w : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1) (hvs : v ∈ s) :
    ‖⟪v, w⟫_ℂ‖ ^ 2 ≤ ∑ k,
      ‖⟪((stdOrthonormalBasis ℂ s) k : EuclideanSpace ℂ (Fin d)), w⟫_ℂ‖ ^ 2 := by
  let u : s := ⟨v, hvs⟩
  have hu : ‖u‖ = 1 := hv
  have hi := norm_inner_le_norm (𝕜 := ℂ) u (s.orthogonalProjectionOnto w)
  rw [hu, one_mul] at hi
  calc
    ‖⟪v, w⟫_ℂ‖ ^ 2 = ‖⟪u, s.orthogonalProjectionOnto w⟫_ℂ‖ ^ 2 := by
      rw [s.inner_orthogonalProjectionOnto_eq_of_mem_left]
    _ ≤ ‖s.orthogonalProjectionOnto w‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hi 2
    _ = _ := by
      rw [← (stdOrthonormalBasis ℂ s).sum_sq_norm_inner_right]
      simp only [s.inner_orthogonalProjectionOnto_eq_of_mem_left]

private theorem expectation_le_basis {d : ℕ}
    (s : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1) (hvs : v ∈ s)
    (m : Matrix (Fin d) (Fin d) ℂ) (hm : m.PosSemidef) :
    (projector v * m).trace.re ≤ ∑ k,
      (projector ((stdOrthonormalBasis ℂ s) k : EuclideanSpace ℂ (Fin d)) * m).trace.re := by
  classical
  obtain ⟨r, z, hz⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hm
  rw [hz]
  simp only [Matrix.mul_sum, trace_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro k _
  have h := overlap_le_basis s v (WithLp.toLp 2 (z k)) hv hvs
  convert h using 1 <;>
    simp only [projector, vecMulVec_mul_vecMulVec, trace_vecMulVec, dotProduct_smul,
      EuclideanSpace.inner_eq_star_dotProduct]
  · rw [smul_eq_mul, dotProduct_comm (fun i => star (v i))]
    change (⟪v, WithLp.toLp 2 (z k)⟫_ℂ * ⟪WithLp.toLp 2 (z k), v⟫_ℂ).re =
      ‖⟪v, WithLp.toLp 2 (z k)⟫_ℂ‖ ^ 2
    rw [← inner_conj_symm (WithLp.toLp 2 (z k)) v, Complex.mul_conj']
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  · apply Finset.sum_congr rfl
    intro l _
    rw [smul_eq_mul, dotProduct_comm (fun i =>
      star (((stdOrthonormalBasis ℂ s) l : EuclideanSpace ℂ (Fin d)) i))]
    change (⟪((stdOrthonormalBasis ℂ s) l : EuclideanSpace ℂ (Fin d)),
      WithLp.toLp 2 (z k)⟫_ℂ * ⟪WithLp.toLp 2 (z k),
      ((stdOrthonormalBasis ℂ s) l : EuclideanSpace ℂ (Fin d))⟫_ℂ).re = _
    rw [← inner_conj_symm (WithLp.toLp 2 (z k))
      ((stdOrthonormalBasis ℂ s) l : EuclideanSpace ℂ (Fin d)), Complex.mul_conj']
    simp only [← Complex.ofReal_pow, Complex.ofReal_re,
      EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp]

private theorem discrimination_bound {d : ℕ}
    (v : ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m : ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (hv : ∀ b, ‖v b‖ = 1)
    (hm : (∀ b, (m b).PosSemidef) ∧ ∑ b, m b = 1)
    (s : Submodule ℂ (EuclideanSpace ℂ (Fin d))) (hs : Module.finrank ℂ s ≤ 2)
    (hvs : ∀ b, v b ∈ s) :
    ∑ b, (projector (v b) * m b).trace.re ≤ 2 := by
  classical
  calc
    _ ≤ ∑ b, ∑ k,
        (projector ((stdOrthonormalBasis ℂ s) k : EuclideanSpace ℂ (Fin d)) * m b).trace.re :=
      Finset.sum_le_sum fun b _ => expectation_le_basis s (v b) (hv b) (hvs b) (m b) (hm.1 b)
    _ = ∑ k : Fin (Module.finrank ℂ s), (1 : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      calc
        _ = (projector ((stdOrthonormalBasis ℂ s) k : EuclideanSpace ℂ (Fin d)) *
            ∑ b, m b).trace.re := by simp [Matrix.mul_sum, trace_sum]
        _ = 1 := by
          rw [hm.2, mul_one, projector, trace_vecMulVec]
          change (⟪(stdOrthonormalBasis ℂ s) k, (stdOrthonormalBasis ℂ s) k⟫_ℂ).re = 1
          rw [inner_self_eq_one_of_norm_eq_one ((stdOrthonormalBasis ℂ s).orthonormal.1 k)]
          rfl
    _ = Module.finrank ℂ s := by simp
    _ ≤ 2 := by exact_mod_cast hs

private theorem effect_bound {d : ℕ}
    (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1)
    (m : ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (hm : (∀ b, (m b).PosSemidef) ∧ ∑ b, m b = 1) (b : ZMod 3) :
    0 ≤ (projector v * m b).trace.re ∧ (projector v * m b).trace.re ≤ 1 := by
  classical
  have hnonneg : ∀ k, 0 ≤ (projector v * m k).trace.re := by
    intro k
    rw [trace_mul_comm, projector, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
    exact (hm.1 k).re_dotProduct_nonneg v
  refine ⟨hnonneg b, ?_⟩
  calc
    (projector v * m b).trace.re ≤ ∑ k, (projector v * m k).trace.re :=
      Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ b)
    _ = (projector v * ∑ k, m k).trace.re := by
      simp [Matrix.mul_sum, trace_sum]
    _ = 1 := by
      rw [hm.2, mul_one, projector, trace_vecMulVec]
      change (⟪v, v⟫_ℂ).re = 1
      rw [inner_self_eq_one_of_norm_eq_one hv]
      rfl

private theorem discrimination_three {d : ℕ}
    (v : ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m : ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (hv : ∀ b, ‖v b‖ = 1)
    (hm : (∀ b, (m b).PosSemidef) ∧ ∑ b, m b = 1) :
    ∑ b, (projector (v b) * m b).trace.re ≤ 3 := by
  calc
    _ ≤ ∑ _b : ZMod 3, (1 : ℝ) :=
      Finset.sum_le_sum fun b _ => (effect_bound (v b) (hv b) m hm b).2
    _ = 3 := by norm_num

private theorem constant_discrimination {d : ℕ}
    (v : ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m : ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (hv : ‖v 0‖ = 1) (hm : ∑ b, m b = 1)
    (h : ∀ b, projector (v b) = projector (v 0)) :
    ∑ b, (projector (v b) * m b).trace.re = 1 := by
  simp_rw [h]
  calc
    _ = (projector (v 0) * ∑ b, m b).trace.re := by
      simp [Matrix.mul_sum, trace_sum]
    _ = 1 := by
      rw [hm, mul_one, projector, trace_vecMulVec]
      change (⟪v 0, v 0⟫_ℂ).re = 1
      rw [inner_self_eq_one_of_norm_eq_one hv]
      rfl

private theorem value_reduction {d : ℕ}
    (ψ : ZMod 3 × ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m n : ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (hψ : ∀ x, ‖ψ x‖ = 1) (hm : ∑ b, m b = 1) (hn : ∑ b, n b = 1)
    (hadd : ∀ i j, projector (ψ (i, j)) =
      projector (ψ (i, 0)) + projector (ψ (0, j)) - projector (ψ (0, 0))) :
    htmbValue ψ m n = (1 / 6) *
      ((∑ i, (projector (ψ (i, 0)) * m i).trace.re) +
       (∑ j, (projector (ψ (0, j)) * n j).trace.re)) := by
  classical
  have hc (j : ZMod 3) := constant_discrimination (fun _ : ZMod 3 => ψ (0, j)) m
    (hψ (0, j)) hm (fun _ => rfl)
  have hr (i : ZMod 3) := constant_discrimination (fun _ : ZMod 3 => ψ (i, 0)) n
    (hψ (i, 0)) hn (fun _ => rfl)
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  have hr0 := hr 0
  have hr1 := hr 1
  have hr2 := hr 2
  simp only [sum_trit] at hc0 hc1 hc2 hr0 hr1 hr2
  simp only [htmbValue, Fintype.sum_prod_type, sum_trit]
  rw [hadd 1 1, hadd 1 2, hadd 2 1, hadd 2 2]
  simp only [add_mul, sub_mul, trace_add, trace_sub, Complex.add_re, Complex.sub_re]
  linear_combination (1 / 18 : ℝ) * (hc1 + hc2 - 2 * hc0 + hr1 + hr2 - 2 * hr0)

private theorem cross_in_plane {d : ℕ}
    (ψ : ZMod 3 × ZMod 3 → EuclideanSpace ℂ (Fin d))
    (hψ : ∀ x, ‖ψ x‖ = 1)
    (hadd : ∀ i j, projector (ψ (i, j)) =
      projector (ψ (i, 0)) + projector (ψ (0, j)) - projector (ψ (0, 0)))
    (i j : ZMod 3)
    (hi : projector (ψ (i, 0)) ≠ projector (ψ (0, 0)))
    (hj : projector (ψ (0, j)) ≠ projector (ψ (0, 0))) :
    ∃ s : Submodule ℂ (EuclideanSpace ℂ (Fin d)), Module.finrank ℂ s ≤ 2 ∧
      (∀ k, ψ (k, 0) ∈ s) ∧ (∀ k, ψ (0, k) ∈ s) := by
  classical
  let s := Submodule.span ℂ ({ψ (0, j), ψ (0, 0)} : Set (EuclideanSpace ℂ (Fin d)))
  have hcs : ∀ k, ψ (k, 0) ∈ s := by
    intro k
    have heq : projector (ψ (k, j)) - projector (ψ (k, 0)) =
        projector (ψ (0, j)) - projector (ψ (0, 0)) := by rw [hadd]; abel
    exact (projector_difference_span _ _ _ _ (hψ _) (hψ _) (hψ _) (hψ _)
      heq (sub_ne_zero.mpr hj)).2
  refine ⟨s, ?_, hcs, ?_⟩
  · change Module.finrank ℂ (Submodule.span ℂ
      ({ψ (0, j), ψ (0, 0)} : Set (EuclideanSpace ℂ (Fin d)))) ≤ 2
    apply (finrank_span_le_ncard _ ((Set.finite_singleton _).insert _)).trans
    simpa only [Set.ncard_singleton, Nat.reduceAdd] using
      Set.ncard_insert_le (ψ (0, j)) ({ψ (0, 0)} : Set (EuclideanSpace ℂ (Fin d)))
  · intro k
    have heq : projector (ψ (i, k)) - projector (ψ (0, k)) =
        projector (ψ (i, 0)) - projector (ψ (0, 0)) := by rw [hadd]; abel
    have hk := (projector_difference_span _ _ _ _ (hψ _) (hψ _) (hψ _) (hψ _)
      heq (sub_ne_zero.mpr hi)).2
    exact (Submodule.span_le.mpr (by
      intro v hv
      rcases hv with rfl | hv
      · exact hcs i
      · rcases hv with rfl
        exact hcs 0)) hk

/-- The pure-state HTMB conjecture of Tavakoli, Zambrini Cruzeiro, Uola and Abbott. -/
theorem result : claim := by
  intro d ψ m n hψ hm hn hequiv
  have hadd := additive_form (fun x => projector (ψ x)) hequiv
  rw [value_reduction ψ m n hψ hm.2 hn.2 hadd]
  have hcol := discrimination_three (fun i => ψ (i, 0)) m (fun i => hψ (i, 0)) hm
  have hrow := discrimination_three (fun j => ψ (0, j)) n (fun j => hψ (0, j)) hn
  by_cases hc : ∀ i, projector (ψ (i, 0)) = projector (ψ (0, 0))
  · have h := constant_discrimination (fun i => ψ (i, 0)) m (hψ (0, 0)) hm.2 hc
    linarith
  by_cases hr : ∀ j, projector (ψ (0, j)) = projector (ψ (0, 0))
  · have h := constant_discrimination (fun j => ψ (0, j)) n (hψ (0, 0)) hn.2 hr
    linarith
  push Not at hc hr
  obtain ⟨i, hi⟩ := hc
  obtain ⟨j, hj⟩ := hr
  obtain ⟨s, hs, hcs, hrs⟩ := cross_in_plane ψ hψ hadd i j hi hj
  have htwo_col := discrimination_bound (fun i => ψ (i, 0)) m
    (fun i => hψ (i, 0)) hm s hs hcs
  have htwo_row := discrimination_bound (fun j => ψ (0, j)) n
    (fun j => hψ (0, j)) hn s hs hrs
  linarith

end D5.S3.Quantum.Contextuality.PureStateHTMBBound
