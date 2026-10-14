/- GID: D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.claim; result=D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.result; claim=D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.claim
   digest: A triangulated complete graph refutes the least-energy uniform-overlap bound. -/

import D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum
import D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees

set_option linter.style.longLine false

open Matrix Finset

namespace D5.S3.Quantum.Dynamics.QuantumBatteryUniformOverlapRefutation

open D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum
/-- The least adjacency eigenvalue λ_min(A(G)). -/
noncomputable def lamMin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  let hA : (G.adjMatrix ℝ).IsHermitian := Matrix.isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix
  ⨅ i : Fin n, hA.eigenvalues i
/-- The minimal-energy uniform overlap w_min(G) = Σ_{k : ε_k = λ_min} (1ᵀu_k)² = 1ᵀ E_{λ_min} 1,
    where E_θ = `idempotent G θ` is the sum of u uᵀ over an orthonormal eigenbasis with eigenvalue θ. -/
noncomputable def wmin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  ∑ i, ∑ j, idempotent G (lamMin G) i j
/-- Conjecture 1 of Sarkis–Prośniak–Nigro–Tkatchenko. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeSet.Nonempty →
    wmin G ≤ (n : ℝ) / 2 - Real.sqrt ((n : ℝ) - 1)

private theorem overlap_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n → ℝ) (hv : G.adjMatrix ℝ *ᵥ v = lamMin G • v) :
    (∑ j, v j) ^ 2 ≤ wmin G * (∑ j, v j ^ 2) := by
  classical
  let hA : (G.adjMatrix ℝ).IsHermitian := isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix
  let b := hA.eigenvectorBasis
  let c := fun i => inner ℝ (b i) (WithLp.toLp 2 v)
  let a := fun i => inner ℝ (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))) (b i)
  let s := univ.filter (fun i => hA.eigenvalues i = lamMin G)
  have hc : ∀ i ∉ s, c i = 0 := by
    intro i hi
    simpa only [c, b, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
      star_trivial, dotProduct_comm] using
      D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees.eig_dot_zero hA v (lamMin G) hv i
        (fun he => hi (mem_filter.mpr ⟨mem_univ i, he⟩))
  have hs : ∑ i ∈ s, a i * c i = ∑ j, v j := by
    calc
      _ = ∑ i, a i * c i := sum_subset (filter_subset _ _) (fun i _ hi => by
        rw [hc i hi, mul_zero])
      _ = _ := by
        simpa only [a, c, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
          star_trivial, dotProduct, Pi.one_apply, mul_one, one_mul] using
          b.sum_inner_mul_inner (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))) (WithLp.toLp 2 v)
  have hn : ∑ i ∈ s, c i ^ 2 = ∑ j, v j ^ 2 := by
    calc
      _ = ∑ i, c i ^ 2 := sum_subset (filter_subset _ _) (fun i _ hi => by
        rw [hc i hi, zero_pow (by omega)])
      _ = _ := by
        simpa only [PiLp.norm_sq_eq_of_L2, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs] using
          b.sum_sq_inner_right (WithLp.toLp 2 v)
  have hw : ∑ i ∈ s, a i ^ 2 = wmin G := by
    change _ = ∑ j, ∑ k, (∑ i ∈ s, vecMulVec ⇑(b i) ⇑(b i)) j k
    simp only [Matrix.sum_apply, vecMulVec_apply]
    rw [sum_comm]
    simp_rw [sum_comm (s := univ) (t := s), ← sum_mul, ← mul_sum]
    apply sum_congr rfl
    intro i _
    simp only [a, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, dotProduct, mul_one]
    ring
  simpa (config := { congrConsts := false }) only [hs, hn, hw] using
    sum_mul_sq_le_sq_mul_sq s a c

private abbrev Pair := {p : Fin 10 × Fin 10 // p.1 < p.2}
private abbrev Vert := Fin 10 ⊕ (Pair × Fin 27)

private theorem pair_sum (f : Fin 10 → Fin 10 → ℝ) (hf : ∀ i j, f i j = f j i) :
    2 * (∑ p : Pair, f p.1.1 p.1.2) = (∑ i, ∑ j, f i j) - ∑ i, f i i := by
  classical
  let t := univ.filter (fun p : Fin 10 × Fin 10 => p.1 < p.2)
  have hsub : ∑ p ∈ t, f p.1 p.2 = ∑ p : Pair, f p.1.1 p.1.2 :=
    sum_subtype t (fun _ => by simp only [t, mem_filter, mem_univ, true_and]) _
  have hswap : ∑ p : Fin 10 × Fin 10, (if p.2 < p.1 then f p.1 p.2 else 0) =
      ∑ p : Fin 10 × Fin 10, (if p.1 < p.2 then f p.1 p.2 else 0) := by
    rw [← (Equiv.prodComm (Fin 10) (Fin 10)).sum_comp
      (fun p => if p.2 < p.1 then f p.1 p.2 else 0)]
    refine sum_congr rfl fun p _ => ?_
    change (if p.1 < p.2 then f p.2 p.1 else 0) = _
    rw [hf p.2 p.1]
  have hsplit : ∀ i j : Fin 10, f i j = (if i < j then f i j else 0) +
      (if j < i then f i j else 0) + (if i = j then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp only [if_pos h, if_neg h.not_gt, if_neg h.ne, add_zero]
    · subst j; simp only [lt_self_iff_false, if_false, if_true, zero_add]
    · simp only [if_neg h.not_gt, if_pos h, if_neg h.ne.symm, zero_add, add_zero]
  have hfull := sum_congr rfl
    (fun (p : Fin 10 × Fin 10) (_ : p ∈ univ) => hsplit p.1 p.2)
  rw [sum_add_distrib, sum_add_distrib, hswap, ← sum_filter, hsub] at hfull
  rw [Fintype.sum_prod_type] at hfull
  simp only [Fintype.sum_prod_type] at hfull
  simp at hfull
  linarith

private theorem pair_card : Fintype.card Pair = 45 := by
  rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]
  norm_num [Nat.choose]

private noncomputable def vertEquiv : Vert ≃ Fin 1225 :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, pair_card])

private def rel : Vert → Vert → Prop :=
  Sum.elim
    (fun i => Sum.elim (fun j => i ≠ j) (fun t => i = t.1.1.1 ∨ i = t.1.1.2))
    (fun t => Sum.elim (fun i => i = t.1.1.1 ∨ i = t.1.1.2) (fun _ => False))

private def graphS : SimpleGraph Vert := SimpleGraph.fromRel rel

private noncomputable instance graphSDecidable : DecidableRel graphS.Adj := Classical.decRel _

private noncomputable def graph : SimpleGraph (Fin 1225) := graphS.comap vertEquiv.symm

private noncomputable instance graphDecidable : DecidableRel graph.Adj := Classical.decRel _

private noncomputable def vectorS : Vert → ℝ := Sum.elim (fun _ => 1) (fun _ => -1 / 9)

private noncomputable def vector : Fin 1225 → ℝ := vectorS ∘ vertEquiv.symm

private theorem pair_linear (x : Fin 10 → ℝ) :
    (∑ p : Pair, (x p.1.1 + x p.1.2)) = 9 * ∑ i, x i := by
  have h := pair_sum (fun i j => x i + x j) (fun i j => add_comm (x i) (x j))
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, Nat.cast_ofNat, nsmul_eq_mul,
    ← mul_sum] at h ⊢
  linarith

private theorem pair_squares (x : Fin 10 → ℝ) :
    (∑ p : Pair, (x p.1.1 + x p.1.2) ^ 2) =
      8 * (∑ i, x i ^ 2) + (∑ i, x i) ^ 2 := by
  have h := pair_sum (fun i j => (x i + x j) ^ 2)
    (fun i j => congrArg (fun t : ℝ => t ^ 2) (add_comm (x i) (x j)))
  simp only [add_sq, mul_assoc, ← pow_two, sum_add_distrib, sum_const, card_univ,
    Fintype.card_fin, Nat.cast_ofNat, nsmul_eq_mul, ← sum_mul, ← mul_sum] at h ⊢
  nlinarith [h]

private theorem incident_sum (p : Pair) (x : Fin 10 → ℝ) :
    (∑ i, if i = p.1.1 ∨ i = p.1.2 then x i else 0) = x p.1.1 + x p.1.2 := by
  calc
    _ = ∑ i, ((if i = p.1.1 then x i else 0) +
        (if i = p.1.2 then x i else 0)) := by
      refine sum_congr rfl fun i _ => ?_
      by_cases h1 : i = p.1.1
      · have h2 : i ≠ p.1.2 := fun h => p.2.ne (h1.symm.trans h)
        simp only [if_pos (Or.inl h1), if_pos h1, if_neg h2, add_zero]
      · by_cases h2 : i = p.1.2
        · simp only [if_pos (Or.inr h2), if_neg h1, if_pos h2, zero_add]
        · simp only [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg h1, if_neg h2, zero_add]
    _ = _ := by rw [sum_add_distrib]; simp only [Fintype.sum_ite_eq']

private theorem core_incidence (i : Fin 10) :
    (∑ t : Pair × Fin 27, if i = t.1.1.1 ∨ i = t.1.1.2 then (1 : ℝ) else 0) = 243 := by
  rw [Fintype.sum_prod_type]
  change (∑ p : Pair, ∑ _q : Fin 27,
    if i = p.1.1 ∨ i = p.1.2 then (1 : ℝ) else 0) = 243
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
  have h := pair_linear (fun j => if i = j then (1 : ℝ) else 0)
  simp only [Fintype.sum_ite_eq] at h
  have he : ∀ p : Pair, (if i = p.1.1 ∨ i = p.1.2 then (1 : ℝ) else 0) =
      (if i = p.1.1 then 1 else 0) + (if i = p.1.2 then 1 else 0) := by
    intro p
    by_cases h1 : i = p.1.1
    · have h2 : i ≠ p.1.2 := fun h => p.2.ne (h1.symm.trans h)
      simp only [if_pos (Or.inl h1), if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : i = p.1.2
      · simp only [if_pos (Or.inr h2), if_neg h1, if_pos h2, zero_add]
      · simp only [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg h1, if_neg h2, zero_add]
  rw [sum_congr rfl (fun p _ => he p), h]
  norm_num

private theorem row_core (x : Vert → ℝ) (i : Fin 10) :
    (graphS.adjMatrix ℝ *ᵥ x) (Sum.inl i) =
      (∑ j, x (Sum.inl j)) - x (Sum.inl i) +
        ∑ t : Pair × Fin 27, if i = t.1.1.1 ∨ i = t.1.1.2 then x (Sum.inr t) else 0 := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type]
  have hcc : ∀ j, graphS.adjMatrix ℝ (Sum.inl i) (Sum.inl j) * x (Sum.inl j) =
      x (Sum.inl j) - (if i = j then x (Sum.inl j) else 0) := by
    intro j
    rw [SimpleGraph.adjMatrix_apply]
    delta graphS rel
    by_cases h : i = j <;> simp [h, ne_comm]
  have hca : ∀ t : Pair × Fin 27,
      graphS.adjMatrix ℝ (Sum.inl i) (Sum.inr t) * x (Sum.inr t) =
        if i = t.1.1.1 ∨ i = t.1.1.2 then x (Sum.inr t) else 0 := by
    intro t
    rw [SimpleGraph.adjMatrix_apply]
    delta graphS rel
    simp [ite_mul]
  rw [sum_congr rfl (fun j _ => hcc j), sum_congr rfl (fun t _ => hca t),
    sum_sub_distrib, Fintype.sum_ite_eq]

private theorem row_attached (x : Vert → ℝ) (t : Pair × Fin 27) :
    (graphS.adjMatrix ℝ *ᵥ x) (Sum.inr t) = x (Sum.inl t.1.1.1) + x (Sum.inl t.1.1.2) := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type]
  have hac : ∀ i, graphS.adjMatrix ℝ (Sum.inr t) (Sum.inl i) * x (Sum.inl i) =
      if i = t.1.1.1 ∨ i = t.1.1.2 then x (Sum.inl i) else 0 := by
    intro i
    rw [SimpleGraph.adjMatrix_apply]
    delta graphS rel
    simp [ite_mul]
  have haa : ∀ s : Pair × Fin 27,
      graphS.adjMatrix ℝ (Sum.inr t) (Sum.inr s) * x (Sum.inr s) = 0 := by
    intro s
    rw [SimpleGraph.adjMatrix_apply]
    delta graphS rel
    simp
  rw [sum_congr rfl (fun i _ => hac i), sum_congr rfl (fun s _ => haa s),
    sum_const_zero, add_zero, incident_sum]

private theorem vectorS_eigen : graphS.adjMatrix ℝ *ᵥ vectorS = (-18 : ℝ) • vectorS := by
  funext a
  rcases a with i | t
  · rw [row_core]
    delta vectorS
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h : ∀ t : Pair × Fin 27,
        (if i = t.1.1.1 ∨ i = t.1.1.2 then (-1 / 9 : ℝ) else 0) =
          (-1 / 9) * (if i = t.1.1.1 ∨ i = t.1.1.2 then 1 else 0) := by
      intro t
      simp only [mul_ite, mul_one, mul_zero]
    rw [sum_congr rfl (fun t _ => h t), ← mul_sum, core_incidence]
    norm_num
  · rw [row_attached]
    delta vectorS
    norm_num

private theorem weighted_incidence (x : Fin 10 → ℝ) (y : Pair × Fin 27 → ℝ) :
    (∑ i, x i * ∑ t : Pair × Fin 27,
      if i = t.1.1.1 ∨ i = t.1.1.2 then y t else 0) =
        ∑ t : Pair × Fin 27, y t * (x t.1.1.1 + x t.1.1.2) := by
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  calc
    _ = ∑ i, (if i = t.1.1.1 ∨ i = t.1.1.2 then x i else 0) * y t := by
      refine sum_congr rfl fun i _ => ?_
      simp only [mul_ite, ite_mul, mul_zero, zero_mul]
    _ = _ := by rw [← sum_mul, incident_sum]; ring

private theorem quadratic_identity (x : Vert → ℝ) :
    (∑ a, x a * (graphS.adjMatrix ℝ *ᵥ x) a) + 18 * (∑ a, x a ^ 2) =
      (∑ i : Fin 10, x (Sum.inl i)) ^ 2 + 17 * (∑ i : Fin 10, x (Sum.inl i) ^ 2) +
        ∑ t : Pair × Fin 27, (18 * x (Sum.inr t) ^ 2 +
          2 * x (Sum.inr t) * (x (Sum.inl t.1.1.1) + x (Sum.inl t.1.1.2))) := by
  simp only [Fintype.sum_sum_type, row_core, row_attached, mul_add, mul_sub,
    sum_add_distrib, sum_sub_distrib]
  rw [weighted_incidence]
  simp only [mul_add, mul_assoc, sum_add_distrib, ← sum_mul, ← mul_sum, ← pow_two]
  ring

private theorem quadratic_nonneg (x : Vert → ℝ) :
    0 ≤ (∑ a, x a * (graphS.adjMatrix ℝ *ᵥ x) a) + 18 * (∑ a, x a ^ 2) := by
  rw [quadratic_identity]
  have hterm : ∀ t : Pair × Fin 27,
      -(x (Sum.inl t.1.1.1) + x (Sum.inl t.1.1.2)) ^ 2 / 18 ≤
        18 * x (Sum.inr t) ^ 2 +
          2 * x (Sum.inr t) * (x (Sum.inl t.1.1.1) + x (Sum.inl t.1.1.2)) := by
    intro t
    nlinarith [sq_nonneg (18 * x (Sum.inr t) +
      (x (Sum.inl t.1.1.1) + x (Sum.inl t.1.1.2)))]
  have hsum := sum_le_sum (fun t (_ : t ∈ univ) => hterm t)
  rw [← sum_div, sum_neg_distrib, Fintype.sum_prod_type] at hsum
  dsimp only at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum] at hsum
  rw [pair_squares (fun i => x (Sum.inl i))] at hsum
  norm_num only [Nat.cast_ofNat] at hsum
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 10)))
    (f := fun i => x (Sum.inl i))
  simp only [card_univ, Fintype.card_fin, Nat.cast_ofNat] at hcs
  linarith

private theorem adj_transport (a b : Vert) :
    graph.adjMatrix ℝ (vertEquiv a) (vertEquiv b) = graphS.adjMatrix ℝ a b := by
  rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
  delta graph
  simp only [SimpleGraph.comap_adj,
    Equiv.symm_apply_apply]

private theorem mulVec_transport (x : Fin 1225 → ℝ) (a : Vert) :
    (graph.adjMatrix ℝ *ᵥ x) (vertEquiv a) =
      (graphS.adjMatrix ℝ *ᵥ (x ∘ vertEquiv)) a := by
  change (∑ b, graph.adjMatrix ℝ (vertEquiv a) b * x b) = _
  rw [← vertEquiv.sum_comp (fun b => graph.adjMatrix ℝ (vertEquiv a) b * x b)]
  simp only [adj_transport]
  rfl

private theorem vector_eigen : graph.adjMatrix ℝ *ᵥ vector = (-18 : ℝ) • vector := by
  funext a
  obtain ⟨a, rfl⟩ := vertEquiv.surjective a
  rw [mulVec_transport]
  have he : vector ∘ vertEquiv = vectorS := by
    funext a
    delta vector
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [he, vectorS_eigen]
  delta vector
  simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply,
    Equiv.symm_apply_apply]

private theorem vector_sum : (∑ a, vector a) = -125 := by
  rw [← vertEquiv.sum_comp vector]
  delta vector vectorS
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, sum_const, card_univ, Fintype.card_fin,
    Fintype.card_prod, pair_card, nsmul_eq_mul]
  norm_num

private theorem vector_norm : (∑ a, vector a ^ 2) = 25 := by
  rw [← vertEquiv.sum_comp (fun a => vector a ^ 2)]
  delta vector vectorS
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, sum_const, card_univ, Fintype.card_fin,
    Fintype.card_prod, pair_card, nsmul_eq_mul]
  norm_num

private theorem graph_quadratic_nonneg (x : Fin 1225 → ℝ) :
    0 ≤ (∑ a, x a * (graph.adjMatrix ℝ *ᵥ x) a) + 18 * (∑ a, x a ^ 2) := by
  rw [← vertEquiv.sum_comp (fun a => x a * (graph.adjMatrix ℝ *ᵥ x) a),
    ← vertEquiv.sum_comp (fun a => x a ^ 2)]
  simp only [mulVec_transport]
  exact quadratic_nonneg (x ∘ vertEquiv)

private theorem graph_nonempty : graph.edgeSet.Nonempty := by
  refine ⟨s(vertEquiv (Sum.inl 0), vertEquiv (Sum.inl 1)), ?_⟩
  rw [SimpleGraph.mem_edgeSet]
  delta graph graphS rel
  simp

private theorem least_eigenvalue : lamMin graph = -18 := by
  let hA : (graph.adjMatrix ℝ).IsHermitian := isHermitian_iff_isSymm.mpr graph.isSymm_adjMatrix
  have hlower : ∀ i, (-18 : ℝ) ≤ hA.eigenvalues i := by
    intro i
    have h := graph_quadratic_nonneg ⇑(hA.eigenvectorBasis i)
    have hn : (∑ a, hA.eigenvectorBasis i a ^ 2) = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, hA.eigenvectorBasis.orthonormal.1 i]
      norm_num
    have he := hA.eigenvalues_eq i
    simp only [star_trivial, RCLike.re_to_real, dotProduct] at he
    rw [← he, hn] at h
    linarith
  have hne : vector ≠ 0 := by
    intro h
    have hs := vector_sum
    rw [h] at hs
    norm_num at hs
  have heig : Module.End.HasEigenvalue (graph.adjMatrix ℝ).toLin' (-18) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by
        simpa only [Matrix.toLin'_apply] using vector_eigen), hne⟩
  have hspec : (-18 : ℝ) ∈ spectrum ℝ (graph.adjMatrix ℝ) := by
    simpa only [Matrix.spectrum_toLin'] using heig.mem_spectrum
  rw [hA.spectrum_real_eq_range_eigenvalues] at hspec
  obtain ⟨i, hi⟩ := hspec
  change (⨅ i, hA.eigenvalues i) = -18
  exact le_antisymm (ciInf_le_of_le ⟨-18, by rintro _ ⟨j, rfl⟩; exact hlower j⟩ i hi.le)
    (le_ciInf hlower)

theorem result : ¬ claim := by
  intro h
  have he : graph.adjMatrix ℝ *ᵥ vector = lamMin graph • vector := by
    rw [least_eigenvalue]
    exact vector_eigen
  have hw := overlap_bound graph vector he
  rw [vector_sum, vector_norm] at hw
  have hb := h 1225 graph graph_nonempty
  have hs := Real.sqrt_nonneg (1224 : ℝ)
  generalize wmin graph = w at hw hb
  norm_num (config := { congrConsts := false }) at hw hb
  linarith

end D5.S3.Quantum.Dynamics.QuantumBatteryUniformOverlapRefutation
