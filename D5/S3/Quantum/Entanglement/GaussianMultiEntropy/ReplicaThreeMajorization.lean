/- GID: D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeMajorization
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeMajorization
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Strict Schur comparison for the positive-real replica-three scalar extension. -/

import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeBalancing
import D5.S3.Geometry.AlphaGeometry.LogScalarCurvatureMonotone
import Mathlib.Tactic.FinCases

/-!
The fixed-sum scalar extension is strictly Schur-convex. The finite transfer
chain is the existing `LogScalarCurvatureMonotone.moreMixed_positive_chain`,
after positive normalization of the common total. No Schur property is assumed.
Scientific source: Haobo Ma then Wenlin Zhang, 2026-11-04,
CC BY 4.0; Camargo–Nishida for the physical family and Marshall–Olkin–Arnold
for the classical majorization criterion. Real sizes remain scalar data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeMajorization

open ReplicaThreeScalar ReplicaThreeBalancing
open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
open D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector

private def scalar (k : ℝ) (x : Fin 3 → ℝ) : ℝ := value k (x 0) (x 1) (x 2)

private lemma pairSum_sum (x : Fin 3 → ℝ) :
    2 * pairSum (x 0) (x 1) (x 2) = (∑ i, x i) ^ 2 - ∑ i, x i ^ 2 := by
  simp [Fin.sum_univ_succ, pairSum]
  ring

private lemma scalar_sum (k : ℝ) (x : Fin 3 → ℝ) :
    scalar k x = (2 * Real.log (1 + k * pairSum (x 0) (x 1) (x 2)) -
      ∑ i, Real.log (1 + k * x i * ((∑ j, x j) - x i))) / 12 := by
  have hs : (∑ j, x j) = x 0 + x 1 + x 2 := by
    simp [Fin.sum_univ_succ, add_assoc]
  have h0 : cut k (x 0) (x 1) (x 2) = 1 + k * x 0 * ((∑ j, x j) - x 0) := by
    rw [hs]; unfold cut; ring
  have h1 : cut k (x 1) (x 0) (x 2) = 1 + k * x 1 * ((∑ j, x j) - x 1) := by
    rw [hs]; unfold cut; ring
  have h2 : cut k (x 2) (x 0) (x 1) = 1 + k * x 2 * ((∑ j, x j) - x 2) := by
    rw [hs]; unfold cut; ring
  simp only [scalar, value, h0, h1, h2]
  simp [Fin.sum_univ_succ, add_assoc]

private lemma scalar_perm (k : ℝ) (x : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) :
    scalar k (x ∘ σ) = scalar k x := by
  have hs : (∑ i, (x ∘ σ) i) = ∑ i, x i := Equiv.sum_comp σ x
  have hsq : (∑ i, (x ∘ σ) i ^ 2) = ∑ i, x i ^ 2 :=
    Equiv.sum_comp σ (fun i => x i ^ 2)
  have hp : pairSum ((x ∘ σ) 0) ((x ∘ σ) 1) ((x ∘ σ) 2) =
      pairSum (x 0) (x 1) (x 2) := by
    have h := pairSum_sum (x ∘ σ)
    rw [hs, hsq] at h
    linarith [pairSum_sum x]
  rw [scalar_sum, scalar_sum, hp, hs]
  have hl := Equiv.sum_comp σ (fun i => Real.log (1 + k * x i * ((∑ j, x j) - x i)))
  simp only [Function.comp_apply] at hl ⊢
  rw [hl]

private lemma value_swap_last (k x y z : ℝ) : value k x y z = value k x z y :=
  (value_swap k x y z).trans (value_cycle k y x z)

private lemma value_swap_ends (k x y z : ℝ) : value k x y z = value k z y x :=
  (value_cycle k x y z).trans (value_swap k y z x)

private lemma scalar_reorder (k : ℝ) (x : Fin 3 → ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j) :
    scalar k x = value k (x i) (x j) (x l) := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals first
    | rfl
    | exact value_swap k _ _ _
    | exact value_swap_last k _ _ _
    | exact value_swap_ends k _ _ _
    | exact value_cycle k _ _ _
    | exact (value_cycle k _ _ _).symm

private lemma scalar_oneT (k : ℝ) (hk : 0 < k) {x q : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (htr : IsTTransform x q) :
    scalar k q ≤ scalar k x ∧
      (scalar k q = scalar k x → ∃ σ : Equiv.Perm (Fin 3), q = x ∘ σ) := by
  obtain ⟨i,j,c,hc0,hc1,hq⟩ := htr
  have hperm (h : ∃ σ : Equiv.Perm (Fin 3), q = x ∘ σ) :
      scalar k q ≤ scalar k x ∧
        (scalar k q = scalar k x → ∃ σ : Equiv.Perm (Fin 3), q = x ∘ σ) := by
    obtain ⟨σ,hσ⟩ := h
    rw [hσ, scalar_perm]
    exact ⟨le_rfl,fun _ => ⟨σ,rfl⟩⟩
  by_cases hij : i = j
  · apply hperm
    refine ⟨1, ?_⟩
    subst j
    rw [hq]
    funext l
    simp
    ring
  by_cases hc : c = 0
  · exact hperm ⟨1, by simpa [hc] using hq⟩
  by_cases hc' : c = 1
  · exact hperm ⟨Equiv.swap i j, by simpa [hc'] using hq⟩
  by_cases hab : x i = x j
  · apply hperm
    refine ⟨1, ?_⟩
    rw [hq]
    funext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      Equiv.Perm.coe_one, id_eq]
    by_cases hli : l = i
    · subst l; rw [Equiv.swap_apply_left, hab]; ring
    by_cases hlj : l = j
    · subst l; rw [Equiv.swap_apply_right, hab]; ring
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]; ring
  have hstrict (a b z : ℝ) (ha : 0 < a) (hb : 0 < b) (hz : 0 < z) (hne : a ≠ b) :
      value k ((1 - c) * a + c * b) (c * a + (1 - c) * b) z < value k a b z := by
    obtain ⟨hle, heq⟩ := pair_mixing k a b z c hk ha hb hz hc0 hc1
    exact lt_of_le_of_ne hle (fun h => by simpa [hc, hc', hne] using heq.mp h)
  have hlt : scalar k q < scalar k x := by
    have hthird : ∃ l : Fin 3, l ≠ i ∧ l ≠ j := by
      fin_cases i <;> fin_cases j <;> first | exact False.elim (hij rfl) | decide
    obtain ⟨l,hli,hlj⟩ := hthird
    have hqi : q i = (1 - c) * x i + c * x j := by simp [hq]
    have hqj : q j = c * x i + (1 - c) * x j := by simp [hq]; ring
    have hql : q l = x l := by
      simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        Equiv.swap_apply_of_ne_of_ne hli hlj]
      ring
    rw [scalar_reorder k q i j l hij hli hlj, scalar_reorder k x i j l hij hli hlj,
      hqi, hqj, hql]
    exact hstrict (x i) (x j) (x l) (hx i) (hx j) (hx l) hab
  exact ⟨hlt.le, fun h => False.elim (hlt.ne h)⟩

private lemma scalar_chain (k : ℝ) (hk : 0 < k) {y x : Fin 3 → ℝ}
    (hy : ∀ i, 0 < y i) (h : Relation.ReflTransGen PositiveT y x) :
    (∀ i, 0 < x i) ∧ scalar k x ≤ scalar k y ∧
      (scalar k x = scalar k y → ∃ σ : Equiv.Perm (Fin 3), x = y ∘ σ) := by
  induction h with
  | refl => exact ⟨hy, le_rfl, fun _ => ⟨1,rfl⟩⟩
  | @tail z q hzq hstep ih =>
    obtain ⟨hle,heq⟩ := scalar_oneT k hk ih.1 hstep.1
    refine ⟨hstep.2.2.1, hle.trans ih.2.1, ?_⟩
    intro hsum
    have he1 : scalar k z = scalar k y := le_antisymm ih.2.1 (by rw [← hsum]; exact hle)
    have he2 : scalar k q = scalar k z := le_antisymm hle (by rw [hsum]; exact ih.2.1)
    obtain ⟨σ,hσ⟩ := ih.2.2 he1
    obtain ⟨τ,hτ⟩ := heq he2
    refine ⟨τ.trans σ, ?_⟩
    rw [hτ,hσ]
    rfl

private lemma desc_scale (a : ℝ) (ha : 0 < a) (x : Fin 3 → ℝ) :
    desc (fun i => a * x i) = (desc x).map (fun t => a * t) := by
  apply List.Perm.eq_of_pairwise' (r := fun b c : ℝ => c ≤ b)
  · exact List.pairwise_mergeSort' (fun b c : ℝ => c ≤ b) _
  · apply List.pairwise_map.mpr
    exact (List.pairwise_mergeSort' (fun b c : ℝ => c ≤ b) (List.ofFn x)).imp
      (fun h => mul_le_mul_of_nonneg_left h ha.le)
  · exact (List.mergeSort_perm _ _).trans (by
      change List.Perm (List.ofFn (fun i => a * x i))
        ((List.ofFn x).mergeSort (fun b c : ℝ => decide (c ≤ b)) |>.map (fun t => a * t))
      simpa only [List.map_ofFn, Function.comp_def] using
        ((List.mergeSort_perm (List.ofFn x) (fun b c : ℝ => decide (c ≤ b))).map
          (fun t => a * t)).symm)

private lemma prefix_scale (a : ℝ) (l : List ℝ) (n : ℕ) :
    D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.prefixSum
      (l.map (fun t => a * t)) n =
      a * D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.prefixSum l n := by
  unfold D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.prefixSum
  rw [← List.map_take]
  induction l.take n with
  | nil => simp
  | cons t l ih => simp [ih, mul_add]

private lemma moreMixed_scale (a : ℝ) (ha : 0 < a) (x y : Fin 3 → ℝ)
    (h : moreMixed x y) : moreMixed (fun i => a * x i) (fun i => a * y i) := by
  constructor
  · intro n hn
    rw [desc_scale a ha, desc_scale a ha, prefix_scale, prefix_scale]
    exact mul_le_mul_of_nonneg_left (h.1 n hn) ha.le
  · rw [desc_scale a ha, desc_scale a ha, prefix_scale, prefix_scale, h.2]

private lemma scalar_scale (k a : ℝ) (ha : a ≠ 0) (x : Fin 3 → ℝ) :
    scalar (k / a ^ 2) (fun i => a * x i) = scalar k x := by
  have hm : 1 + k / a ^ 2 * pairSum (a * x 0) (a * x 1) (a * x 2) =
      1 + k * pairSum (x 0) (x 1) (x 2) := by
    unfold pairSum
    field_simp
  have hd (b c d : ℝ) : cut (k / a ^ 2) (a * b) (a * c) (a * d) = cut k b c d := by
    unfold cut
    field_simp
  simp only [scalar, value, hm, hd]

/-- On positive real triples of equal sum, majorization increases the value.
For comparable triples equality is exactly permutation equality; consequently
strict majorization outside a permutation class gives a strict increase.
The standard `moreMixed` hypothesis includes equal total sums. -/
theorem schur_comparison (k : ℝ) (x y : Fin 3 → ℝ) (hk : 0 < k)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : moreMixed x y) :
    value k (x 0) (x 1) (x 2) ≤ value k (y 0) (y 1) (y 2) ∧
      (value k (x 0) (x 1) (x 2) = value k (y 0) (y 1) (y 2) ↔
        ∃ σ : Equiv.Perm (Fin 3), x = y ∘ σ) := by
  have hs (v : Fin 3 → ℝ) :
      D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.prefixSum (desc v) 3 =
        ∑ i, v i := by
    unfold D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.prefixSum
    rw [List.take_of_length_le (by simp [desc])]
    rw [desc, (List.mergeSort_perm _ _).sum_eq, List.sum_ofFn]
  have hsum : (∑ i, x i) = ∑ i, y i := by simpa only [hs] using hxy.2
  let a : ℝ := (∑ i, x i)⁻¹
  have htotal : 0 < ∑ i, x i := Finset.sum_pos (fun i _ => hx i) (by simp)
  have ha : 0 < a := inv_pos.mpr htotal
  have hx' : (fun i => a * x i) ∈ simplex 3 := by
    refine ⟨fun i => mul_pos ha (hx i), ?_⟩
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ htotal.ne'
  have hy' : (fun i => a * y i) ∈ simplex 3 := by
    refine ⟨fun i => mul_pos ha (hy i), ?_⟩
    rw [← Finset.mul_sum, ← hsum]
    exact inv_mul_cancel₀ htotal.ne'
  have hc := D5.S3.Geometry.AlphaGeometry.LogScalarCurvatureMonotone.moreMixed_positive_chain
    (fun i => a * x i) (fun i => a * y i) hx' hy' (moreMixed_scale a ha x y hxy)
  obtain ⟨_, hle, heq⟩ := scalar_chain (k / a ^ 2) (div_pos hk (sq_pos_of_pos ha)) hy'.1 hc
  rw [scalar_scale k a ha.ne', scalar_scale k a ha.ne'] at hle heq
  refine ⟨hle, ?_⟩
  constructor
  · intro he
    obtain ⟨σ,hσ⟩ := heq he
    refine ⟨σ, ?_⟩
    funext i
    exact mul_left_cancel₀ ha.ne' (congrFun hσ i)
  · rintro ⟨σ,rfl⟩
    exact scalar_perm k y σ

end D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeMajorization
