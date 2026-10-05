/- GID: D5/S3/TotalVariation/TreeParityKernel
   generality: G
   mirror-B: D5/B/S3/TotalVariation/TreeParityKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered tree parity fibers share a uniform conditional kernel. -/

import D5.S3.TotalVariation.ParityCompositionKernel
import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.TotalVariation.TreeParityKernel

open scoped BigOperators
open Finset
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
open D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration (fixedLengthCompositionEquiv)
open D5.S3.TotalVariation.ParityCompositionKernel (R Q)
open D5.S3.TotalVariation.Pinsker (totalVariation)

/-- Ordered shape and the complete gaps between minority leaves. The minority is alpha
when the composition is tied; each gap counts the majority leaves before the next separator. -/
noncomputable def intervals (a b : ℕ) (hv : 1 ≤ a + b) :
    Fiber (a, b) ≃
      BinaryTree.treesOfNumNodesEq (a + b - 1) ×
        (univ : Finset (Fin (min a b + 1))).finsuppAntidiag (max a b) := by
  classical
  let n := a + b
  let k := min a b
  let M := max a b
  have hn : n = k + M := by dsimp [n, k, M]; omega
  let shift : {c : Composition (n + 1) // c.length = k + 1} ≃
      (univ : Finset (Fin (k + 1))).finsuppAntidiag M :=
    { toFun := fun c => ⟨Finsupp.equivFunOnFinite.symm
        (fun i => c.val.blocksFun (Fin.cast c.property.symm i) - 1), by
        simp only [mem_finsuppAntidiag, Finset.subset_univ, and_true]
        have hc : (∑ i : Fin (k + 1), c.val.blocksFun (Fin.cast c.property.symm i)) = n + 1 := by
          simpa using (Equiv.sum_comp (finCongr c.property.symm) c.val.blocksFun).trans
            c.val.sum_blocksFun
        have hp (i : Fin (k + 1)) := c.val.one_le_blocksFun (Fin.cast c.property.symm i)
        simp only [Finsupp.coe_equivFunOnFinite_symm]
        change (∑ i : Fin (k + 1), (c.val.blocksFun (Fin.cast c.property.symm i) - 1)) = M
        rw [Finset.sum_tsub_distrib _ (fun i _ => hp i), hc]
        simp [hn]⟩
      invFun := fun r => ⟨
        { blocks := List.ofFn (fun i : Fin (k + 1) => r.val i + 1)
          blocks_pos := by simp
          blocks_sum := by
            have hr : ∑ i, r.val i = M := (mem_finsuppAntidiag.mp r.property).1
            rw [List.sum_ofFn, sum_add_distrib, hr]
            simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_one]
            omega },
        List.length_ofFn⟩
      left_inv := by
        intro c
        apply Subtype.ext
        apply Composition.ext
        change List.ofFn (fun i : Fin (k + 1) =>
          c.val.blocksFun (Fin.cast c.property.symm i) - 1 + 1) = c.val.blocks
        apply List.ext_getElem
        · simp only [List.length_ofFn, c.property]
        · intro i hi hj
          rw [List.getElem_ofFn]
          change c.val.blocks[i] - 1 + 1 = c.val.blocks[i]
          have hp := c.val.blocks_pos' i hj
          omega
      right_inv := by
        intro r
        apply Subtype.ext
        ext i
        change (List.ofFn (fun i : Fin (k + 1) => r.val i + 1)).get
          (Fin.cast List.length_ofFn.symm i) - 1 = r.val i
        rw [List.get_ofFn]
        simp only [Nat.add_sub_cancel]
        congr 1 }
  let perShape (s : BinaryTree.treesOfNumNodesEq (n - 1)) :
      {A : Finset (Fin s.val.numLeaves) // A.card = a} ≃
        (univ : Finset (Fin (k + 1))).finsuppAntidiag M := by
    have hleaves : s.val.numLeaves = n := by
      have hs := BinaryTree.mem_treesOfNumNodesEq.mp s.property
      have hl := s.val.numLeaves_eq_numNodes_succ
      dsimp [n] at *
      omega
    let castPositions := (finCongr hleaves).finsetCongr.subtypeEquiv
      (p := fun A => A.card = a) (q := fun A => A.card = a)
      (by intro A; simp [Equiv.finsetCongr_apply])
    let minority : {A : Finset (Fin n) // A.card = a} ≃
        {A : Finset (Fin n) // A.card = k} := by
      by_cases hab : a ≤ b
      · have hk : k = a := min_eq_left hab
        exact Equiv.cast (by rw [hk])
      · have hk : k = b := min_eq_right (by omega)
        exact
          { toFun := fun A => ⟨A.valᶜ, by simp [card_compl, A.property, n, hk]⟩
            invFun := fun A => ⟨A.valᶜ, by simp [card_compl, A.property, n, hk]⟩
            left_inv := fun A => by simp
            right_inv := fun A => by simp }
    have separator' : {c : Composition (n + 1) // c.length = k + 1} ≃
        {A : Finset (Fin n) // A.card = k} := by
      convert fixedLengthCompositionEquiv (n + 1) (k + 1) (by omega) (by omega) using 1 <;> simp
    exact castPositions.trans (minority.trans (separator'.symm.trans shift))
  exact (fiberEquiv (a, b) hv).trans
    ((Equiv.sigmaCongrRight perShape).trans (Equiv.sigmaEquivProd _ _))

/-- The parity of every majority-leaf gap, including both outside gaps. -/
noncomputable def gapParity (a b : ℕ) (hv : 1 ≤ a + b) (t : Fiber (a, b)) :
    Fin (min a b + 1) → Bool :=
  fun i => decide (((intervals a b hv t).2.val i) % 2 = 1)

/-- The conditioned Bernoulli parity law with the actual uniform conditional tree kernel. -/
noncomputable def referenceTreeMass (a b : ℕ) (hv : 1 ≤ a + b) : Fiber (a, b) → ℝ :=
  fun t =>
    let d := min a b + 1
    let M := max a b
    let h := ∑ i, (gapParity a b hv t i).toNat
    Q d M (gapParity a b hv t) /
      (catalan (a + b - 1) * (((M - h) / 2 + d - 1).choose (d - 1)) : ℕ)

/-- Actual and reference tree laws have the same uniform conditional kernel given
all gap parities. Their total variation equals that of the parity laws, and every
actual-tree event satisfies the corresponding two-sided finite error bound. -/
theorem result :
    ∀ a b : ℕ, ∀ hv : 1 ≤ a + b,
      let d := min a b + 1
      let M := max a b
      d ≤ M →
      D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (gapParity a b hv)
        (uniformMass (a, b)) = R d M ∧
      (∀ t, 0 ≤ referenceTreeMass a b hv t) ∧
      (∑ t, referenceTreeMass a b hv t) = 1 ∧
      D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (gapParity a b hv)
        (referenceTreeMass a b hv) = Q d M ∧
      totalVariation (uniformMass (a, b)) (referenceTreeMass a b hv) =
        totalVariation (R d M) (Q d M) ∧
      (2 ≤ d → 3 * d ≤ M → ∀ A : Finset (Fiber (a, b)),
        let ε := min 1 (5 * (Real.sqrt (d : ℝ) / M +
          (d : ℝ) * (d - 1) / (M : ℝ) ^ 2))
        max 0 ((∑ t ∈ A, referenceTreeMass a b hv t) - ε) ≤
          ∑ t ∈ A, uniformMass (a, b) t ∧
        (∑ t ∈ A, uniformMass (a, b) t) ≤
          min 1 ((∑ t ∈ A, referenceTreeMass a b hv t) + ε)) ∧
      (d = 1 → uniformMass (a, b) = referenceTreeMass a b hv) := by
  classical
  intro a b hv d M hM
  let f := gapParity a b hv
  let C := catalan (a + b - 1)
  let D := (M + d - 1).choose (d - 1)
  let h : (Fin d → Bool) → ℕ := fun z => ∑ i, (z i).toNat
  let B : (Fin d → Bool) → ℕ := fun z => ((M - h z) / 2 + d - 1).choose (d - 1)
  let N : (Fin d → Bool) → ℕ := fun z => C * B z
  let legal : (Fin d → Bool) → Prop := fun z => h z % 2 = M % 2 ∧ h z ≤ M
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hheight (z : Fin d → Bool) : h z ≤ d := by
    dsimp [h]
    calc
      _ ≤ ∑ _i : Fin d, 1 := sum_le_sum (fun i _ => by cases z i <;> simp)
      _ = d := by simp
  have hC : 0 < C := by
    have hf := (D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.result.1 a b hv).2.2.1
    have hc : 0 < Fintype.card (BinaryTree.treesOfNumNodesEq (a + b - 1)) :=
      Fintype.card_pos_iff.mpr (hf.map (fun t => (intervals a b hv t).1))
    simpa only [Fintype.card_coe, BinaryTree.treesOfNumNodesEq_card_eq_catalan] using hc
  have hD : 0 < D := Nat.choose_pos (by omega)
  have hB (z : Fin d → Bool) : 0 < B z := Nat.choose_pos (by omega)
  have hN (z : Fin d → Bool) : 0 < N z := Nat.mul_pos hC (hB z)
  have htotal : Nat.card (Fiber (a, b)) = C * D := by
    rw [(D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.result.1 a b hv).2.1]
    dsimp [fiberCount, C, D, d, M]
    have hn : a + b = max a b + min a b := by omega
    rw [← hn]
    by_cases hab : a ≤ b
    · rw [min_eq_left hab]
    · rw [min_eq_right (by omega : b ≤ a)]
      have he := Nat.choose_symm (by omega : a ≤ a + b)
      simpa only [Nat.add_sub_cancel_left] using congrArg (catalan (a + b - 1) * ·) he.symm
  have hcount (z : Fin d → Bool) :
      (univ.filter (fun t : Fiber (a, b) => f t = z)).card =
        if legal z then N z else 0 := by
    let T := (univ : Finset (Fin d)).finsuppAntidiag M
    let par : (Fin d →₀ ℕ) → (Fin d → Bool) := fun r i => decide (r i % 2 = 1)
    have hcomp := D5.S3.TotalVariation.ParityCompositionKernel.composition_parity_count d M hd z
    have hsum : (∑ r : T, if par r.val = z then (1 : ℕ) else 0) =
        (T.filter (fun r => par r = z)).card := by
      calc
        _ = ∑ r ∈ T, if par r = z then (1 : ℕ) else 0 :=
          Finset.sum_coe_sort T (fun r => if par r = z then (1 : ℕ) else 0)
        _ = _ := by simp only [sum_boole, Nat.cast_id]
    have he := Equiv.sum_comp (intervals a b hv)
      (fun p => if par p.2.val = z then (1 : ℕ) else 0)
    have hc : Fintype.card (BinaryTree.treesOfNumNodesEq (a + b - 1)) = C := by
      rw [Fintype.card_coe, BinaryTree.treesOfNumNodesEq_card_eq_catalan]
    have hf : (univ.filter (fun t : Fiber (a, b) => f t = z)).card =
        C * (T.filter (fun r => par r = z)).card := by
      rw [card_eq_sum_ones, sum_filter]
      change (∑ t : Fiber (a, b), if par (intervals a b hv t).2.val = z then 1 else 0) = _
      rw [he, Fintype.sum_prod_type]
      calc
        _ = ∑ _s : BinaryTree.treesOfNumNodesEq (a + b - 1),
            (T.filter (fun r => par r = z)).card := by
          apply sum_congr rfl
          intro s _
          calc
            _ = ∑ r : T, if par r.val = z then (1 : ℕ) else 0 := by
              apply sum_congr rfl
              intro r _
              by_cases hp : par r.val = z <;> simp [hp]
            _ = _ := hsum
        _ = _ := by simp only [sum_const, card_univ, hc, nsmul_eq_mul, Nat.cast_id]
    rw [hf, hcomp]
    dsimp [legal, N, B, h]
    split <;> simp
  have hlegal (t : Fiber (a, b)) : legal (f t) := by
    have hc : 0 < (univ.filter (fun x : Fiber (a, b) => f x = f t)).card :=
      card_pos.mpr ⟨t, by simp⟩
    rw [hcount] at hc
    by_contra hn
    simp only [if_neg hn] at hc
    omega
  have hu (t : Fiber (a, b)) : uniformMass (a, b) t = ((C * D : ℕ) : ℝ)⁻¹ := by
    dsimp [uniformMass]
    rw [htotal]
  have hU0 (t : Fiber (a, b)) : 0 ≤ uniformMass (a, b) t := by
    rw [hu]; positivity
  have hU1 : (∑ t, uniformMass (a, b) t) = 1 := by
    simp only [uniformMass, sum_const, card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    rw [htotal]
    exact mul_inv_cancel₀ (by exact_mod_cast (Nat.mul_pos hC hD).ne')
  have hQdata := D5.S3.TotalVariation.ParityCompositionKernel.reference_moments d M hd hM
  have hQ0 (z : Fin d → Bool) : 0 ≤ Q d M z := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hMR : (d : ℝ) ≤ M := by exact_mod_cast hM
    have hden : (0 : ℝ) < 2 * M + d := by positivity
    have hν : (M : ℝ) / (2 * M + d) ≤ 1 := by
      rw [div_le_iff₀ hden]; linarith
    dsimp only [Q]
    split
    · apply div_nonneg
      · exact mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by linarith) _)
      · linarith [hQdata.2.1]
    · exact le_rfl
  have hQ1 : (∑ z, Q d M z) = 1 := hQdata.1
  have href (t : Fiber (a, b)) : referenceTreeMass a b hv t = Q d M (f t) / N (f t) := rfl
  have hUconditional (t : Fiber (a, b)) : uniformMass (a, b) t = R d M (f t) / N (f t) := by
    rw [hu]
    dsimp only [R]
    change ((C * D : ℕ) : ℝ)⁻¹ = (if legal (f t) then (B (f t) : ℝ) / D else 0) / N (f t)
    rw [if_pos (hlegal t)]
    have hc : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
    have hb : (B (f t) : ℝ) ≠ 0 := by exact_mod_cast (hB (f t)).ne'
    have hd0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    dsimp only [N]
    push_cast
    field_simp
  have hkernel (z : Fin d → Bool) (hz : legal z) :
      (∑ t ∈ univ.filter (fun t : Fiber (a, b) => f t = z), (N z : ℝ)⁻¹) = 1 := by
    rw [sum_const, nsmul_eq_mul, hcount, if_pos hz]
    exact mul_inv_cancel₀ (by exact_mod_cast (hN z).ne')
  have hpush (p : Fiber (a, b) → ℝ) (z : Fin d → Bool) :
      D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward f p z =
        ∑ t ∈ univ.filter (fun t : Fiber (a, b) => f t = z), p t := by
    simp only [D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward, sum_filter]
    apply sum_congr rfl
    intro t _
    by_cases ht : f t = z <;> simp [ht]
  have hzero (z : Fin d → Bool) (hz : ¬ legal z) : R d M z = 0 ∧ Q d M z = 0 := by
    have hp : h z % 2 ≠ M % 2 := by
      intro he
      exact hz ⟨he, (hheight z).trans hM⟩
    simp only [R, Q]
    exact ⟨if_neg hz, if_neg hp⟩
  have pushU : D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward f
      (uniformMass (a, b)) = R d M := by
    funext z
    rw [hpush]
    by_cases hz : legal z
    · calc
        _ = ∑ t ∈ univ.filter (fun t : Fiber (a, b) => f t = z),
            R d M z * (N z : ℝ)⁻¹ := by
          apply sum_congr rfl
          intro t ht
          rw [hUconditional, (mem_filter.mp ht).2, div_eq_mul_inv]
        _ = R d M z := by rw [← mul_sum, hkernel z hz, mul_one]
    · rw [show univ.filter (fun t : Fiber (a, b) => f t = z) = ∅ from
        card_eq_zero.mp (by rw [hcount, if_neg hz])]
      simpa using (hzero z hz).1.symm
  have pushQ : D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward f
      (referenceTreeMass a b hv) = Q d M := by
    funext z
    rw [hpush]
    by_cases hz : legal z
    · calc
        _ = ∑ t ∈ univ.filter (fun t : Fiber (a, b) => f t = z),
            Q d M z * (N z : ℝ)⁻¹ := by
          apply sum_congr rfl
          intro t ht
          rw [href, (mem_filter.mp ht).2, div_eq_mul_inv]
        _ = Q d M z := by rw [← mul_sum, hkernel z hz, mul_one]
    · rw [show univ.filter (fun t : Fiber (a, b) => f t = z) = ∅ from
        card_eq_zero.mp (by rw [hcount, if_neg hz])]
      simpa using (hzero z hz).2.symm
  have hV0 (t : Fiber (a, b)) : 0 ≤ referenceTreeMass a b hv t := by
    rw [href]
    exact div_nonneg (hQ0 _) (Nat.cast_nonneg _)
  have hV1 : (∑ t, referenceTreeMass a b hv t) = 1 := by
    rw [← sum_fiberwise univ f]
    simp_rw [← hpush, pushQ]
    exact hQ1
  have hTV : totalVariation (uniformMass (a, b)) (referenceTreeMass a b hv) =
      totalVariation (R d M) (Q d M) := by
    rw [totalVariation, totalVariation, ← sum_fiberwise univ f]
    congr 1
    apply sum_congr rfl
    intro z _
    by_cases hz : legal z
    · calc
        _ = ∑ t ∈ univ.filter (fun t : Fiber (a, b) => f t = z),
            |R d M z - Q d M z| * (N z : ℝ)⁻¹ := by
          apply sum_congr rfl
          intro t ht
          rw [hUconditional, href, (mem_filter.mp ht).2, ← sub_div, abs_div,
            abs_of_nonneg (show (0 : ℝ) ≤ (N z : ℝ) from Nat.cast_nonneg _), div_eq_mul_inv]
        _ = |R d M z - Q d M z| := by
          rw [← mul_sum, hkernel z hz, mul_one]
    · rw [show univ.filter (fun t : Fiber (a, b) => f t = z) = ∅ from
        card_eq_zero.mp (by rw [hcount, if_neg hz])]
      simp [(hzero z hz).1, (hzero z hz).2]
  refine ⟨pushU, hV0, hV1, pushQ, hTV, ?_, ?_⟩
  · intro hd2 hM3 A ε
    have hbound := D5.S3.TotalVariation.ParityCompositionKernel.result.1 d M hd2 hM3
    have hgap := (D5.S3.TotalVariation.Metric.total_variation_eq_sup_event_gap
      (uniformMass (a, b)) (referenceTreeMass a b hv) (hU1.trans hV1.symm)).2
      (Set.mem_range.mpr ⟨A, rfl⟩)
    rw [hTV] at hgap
    have habs := abs_le.mp (hgap.trans hbound)
    have hnonneg : 0 ≤ ∑ t ∈ A, uniformMass (a, b) t := sum_nonneg (fun t _ => hU0 t)
    have hprob : (∑ t ∈ A, uniformMass (a, b) t) ≤ 1 := by
      rw [← hU1]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ A) (fun t _ _ => hU0 t)
    exact ⟨max_le hnonneg (by linarith [habs.1]), le_min hprob (by linarith [habs.2])⟩
  · intro hd1
    have hk := D5.S3.TotalVariation.ParityCompositionKernel.result.2 M (by omega)
    rw [hd1, hk] at hTV
    apply (D5.S3.TotalVariation.Metric.total_variation_eq_zero_iff _ _).mp
    simpa [totalVariation] using hTV

end D5.S3.TotalVariation.TreeParityKernel
