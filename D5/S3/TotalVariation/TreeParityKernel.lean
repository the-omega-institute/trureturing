/- GID: D5/S3/TotalVariation/TreeParityKernel
   generality: G
   mirror-B: D5/B/S3/TotalVariation/TreeParityKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered tree parity fibers share a uniform conditional kernel. -/

import D5.S3.TotalVariation.ParityFiniteTV
import D5.S3.TotalVariation.ParityKernelMasses
import D5.S3.TotalVariation.Metric
import D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift
import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.TotalVariation.TreeParityKernel

open scoped BigOperators
open Finset
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
open D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration (fixedLengthCompositionEquiv)
open D5.S3.TotalVariation.Pinsker (totalVariation)
open D5.S3.Divergence.ClassicalDPI (channelOutput)
open D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift (labelKernel)
open D5.S3.TotalVariation.Equality.DataProcessingEquality
  (total_variation_channel_eq_iff_no_sign_mixing)
open D5.S3.Entropy.Forgetting.CapacityMonotone (pushforward)

/-- The parity-vector mass induced by the uniform weak compositions of `M` into `d` parts;
`h` is the number of occupied coordinates. The binomial coefficient is evaluated only after
the support and parity tests succeed. -/
noncomputable def R (d M : ℕ) (x : Fin d → Bool) : ℝ :=
  let h : ℕ := (Finset.univ.filter fun i => x i = true).card
  if h ≤ M ∧ h % 2 = M % 2 then
    ((M-h)/2+d-1).choose (d-1)/((M+d-1).choose (d-1) : ℝ) else 0

/-- Independent Bernoulli masses with parameter `M / (2M + d)`, conditioned on the parity
of the number of occupied coordinates. -/
noncomputable def Q (d M : ℕ) (x : Fin d → Bool) : ℝ :=
  let h : ℕ := (Finset.univ.filter fun i => x i = true).card
  let ν : ℝ := M/(2*(M : ℝ)+d)
  let pe : ℝ := (1+(-1 : ℝ)^M*((d : ℝ)/(2*(M : ℝ)+d))^d)/2
  if h % 2 = M % 2 then ν^h*(1-ν)^(d-h)/pe else 0

/-- Ordered shape and the complete gaps between minority leaves. The minority is alpha
when the composition is tied; each gap counts the majority leaves before the next separator. -/
noncomputable def intervals (a b : ℕ) (hv : 1 ≤ a + b) :
    Fiber (a, b) ≃
      BinaryTree.treesOfNumNodesEq (a + b - 1) ×
        Finset.Nat.antidiagonalTuple (min a b + 1) (max a b) := by
  classical
  let n := a + b
  let k := min a b
  let M := max a b
  have hn : n = k + M := by dsimp [n, k, M]; omega
  let shift : {c : Composition (n + 1) // c.length = k + 1} ≃
      Finset.Nat.antidiagonalTuple (k + 1) M :=
    { toFun := fun c => ⟨fun i => c.val.blocksFun (Fin.cast c.property.symm i) - 1, by
        rw [Finset.Nat.mem_antidiagonalTuple]
        have hc : (∑ i : Fin (k + 1), c.val.blocksFun (Fin.cast c.property.symm i)) = n + 1 := by
          simpa using (Equiv.sum_comp (finCongr c.property.symm) c.val.blocksFun).trans
            c.val.sum_blocksFun
        have hp (i : Fin (k + 1)) := c.val.one_le_blocksFun (Fin.cast c.property.symm i)
        change (∑ i : Fin (k + 1), (c.val.blocksFun (Fin.cast c.property.symm i) - 1)) = M
        rw [Finset.sum_tsub_distrib _ (fun i _ => hp i), hc]
        simp [hn]⟩
      invFun := fun r => ⟨
        { blocks := List.ofFn (fun i : Fin (k + 1) => r.val i + 1)
          blocks_pos := by simp
          blocks_sum := by
            have hr : ∑ i, r.val i = M := Finset.Nat.mem_antidiagonalTuple.mp r.property
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
        funext i
        change (List.ofFn (fun i : Fin (k + 1) => r.val i + 1)).get
          (Fin.cast List.length_ofFn.symm i) - 1 = r.val i
        rw [List.get_ofFn]
        simp only [Nat.add_sub_cancel]
        congr 1 }
  let perShape (s : BinaryTree.treesOfNumNodesEq (n - 1)) :
      {A : Finset (Fin s.val.numLeaves) // A.card = a} ≃
        Finset.Nat.antidiagonalTuple (k + 1) M := by
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
    let h := (Finset.univ.filter fun i => gapParity a b hv t i = true).card
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
      pushforward (gapParity a b hv) (uniformMass (a, b)) = R d M ∧
      (∀ t, 0 ≤ referenceTreeMass a b hv t) ∧
      (∑ t, referenceTreeMass a b hv t) = 1 ∧
      pushforward (gapParity a b hv) (referenceTreeMass a b hv) = Q d M ∧
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
  let h : (Fin d → Bool) → ℕ := fun z => (Finset.univ.filter fun i => z i = true).card
  let B : (Fin d → Bool) → ℕ := fun z => ((M - h z) / 2 + d - 1).choose (d - 1)
  let N : (Fin d → Bool) → ℕ := fun z => C * B z
  let legal : (Fin d → Bool) → Prop := fun z => h z ≤ M ∧ h z % 2 = M % 2
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hheight (z : Fin d → Bool) : h z ≤ d :=
    (Finset.card_filter_le _ _).trans_eq (by simp)
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
  -- The actual trees with a prescribed complete gap parity: every ordered shape, times the
  -- weak compositions of `M` with that parity vector.
  have hcount (z : Fin d → Bool) :
      (univ.filter (fun t : Fiber (a, b) => f t = z)).card =
        if legal z then N z else 0 := by
    let T := Finset.Nat.antidiagonalTuple d M
    let par : (Fin d → ℕ) → (Fin d → Bool) := fun r i => decide (r i % 2 = 1)
    have hpar : T.filter (fun r => par r = z) =
        T.filter (fun r => ∀ i, r i % 2 = if z i then 1 else 0) := by
      apply Finset.filter_congr
      intro r _
      simp only [par, funext_iff]
      refine forall_congr' fun i => ?_
      have hm := Nat.mod_lt (r i) (by decide : 0 < 2)
      cases z i <;> simp <;> omega
    have hcomp : (T.filter (fun r => par r = z)).card = if legal z then B z else 0 := by
      have hpf : (T.filter (fun r => ∀ i, r i % 2 = if z i then 1 else 0)).card =
          if h z ≤ M ∧ h z % 2 = M % 2 then B z else 0 :=
        D5.S3.TotalVariation.ParityKernelMasses.parity_fiber_card (by omega) z
      rw [hpar, hpf]
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
    by_cases hz : legal z <;> simp [hz, N]
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
  obtain ⟨-, hQ0, hQ1⟩ : 0 < (1+(-1 : ℝ)^M*((d : ℝ)/(2*(M : ℝ)+d))^d)/2 ∧
      (∀ z, 0 ≤ Q d M z) ∧ ∑ z, Q d M z = 1 :=
    D5.S3.TotalVariation.ParityKernelMasses.parity_reference_mass (by omega) (by omega)
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
      pushforward f p z = ∑ t ∈ univ.filter (fun t : Fiber (a, b) => f t = z), p t := by
    simp only [pushforward, sum_filter]
    apply sum_congr rfl
    intro t _
    by_cases ht : f t = z <;> simp [ht]
  have hzero (z : Fin d → Bool) (hz : ¬ legal z) : R d M z = 0 ∧ Q d M z = 0 := by
    have hp : h z % 2 ≠ M % 2 := by
      intro he
      exact hz ⟨(hheight z).trans hM, he⟩
    simp only [R, Q]
    exact ⟨if_neg hz, if_neg hp⟩
  have pushU : pushforward f (uniformMass (a, b)) = R d M := by
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
  have pushQ : pushforward f (referenceTreeMass a b hv) = Q d M := by
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
  -- The two tree laws differ by one sign on every parity fiber, so the deterministic parity
  -- channel preserves their total variation.
  have hTV : totalVariation (uniformMass (a, b)) (referenceTreeMass a b hv) =
      totalVariation (R d M) (Q d M) := by
    have hW : (∀ t z, 0 ≤ labelKernel f t z) ∧ ∀ t, ∑ z, labelKernel f t z = 1 := by
      refine ⟨fun t z => by unfold labelKernel; split_ifs <;> norm_num, fun t => ?_⟩
      simp [labelKernel]
    have hchannel (p : Fiber (a, b) → ℝ) :
        channelOutput (labelKernel f) p = pushforward f p := by
      funext z
      rw [hpush]
      simp only [channelOutput, labelKernel, mul_ite, mul_one, mul_zero, sum_ite, sum_const_zero,
        add_zero]
    have hsign := (total_variation_channel_eq_iff_no_sign_mixing (uniformMass (a, b))
      (referenceTreeMass a b hv) (labelKernel f) hW).mpr (by
        intro z
        by_cases hz : R d M z ≤ Q d M z
        · right
          intro t ht
          unfold labelKernel
          rw [if_neg]
          intro hft
          rw [hUconditional, href, hft] at ht
          exact absurd ht (not_lt.mpr (div_le_div_of_nonneg_right hz (Nat.cast_nonneg _)))
        · left
          intro t ht
          unfold labelKernel
          rw [if_neg]
          intro hft
          rw [hUconditional, href, hft] at ht
          exact hz (le_of_lt ((div_lt_div_iff_of_pos_right
            (by exact_mod_cast hN z : (0 : ℝ) < N z)).mp ht)))
    rw [hchannel, hchannel, pushU, pushQ] at hsign
    exact hsign.symm
  refine ⟨pushU, hV0, hV1, pushQ, hTV, ?_, ?_⟩
  · intro hd2 hM3 A ε
    have hbound : totalVariation (R d M) (Q d M) ≤ ε :=
      D5.S3.TotalVariation.ParityFiniteTV.parity_finite_tv hd2 hM3
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
    -- With one gap, the actual parity is that of `M`, and conditioning the single Bernoulli
    -- coordinate on the same parity leaves the same point mass.
    have hRQ (M : ℕ) (hM : 1 ≤ M) : R 1 M = Q 1 M := by
      funext ξ
      have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
      have hden : (0 : ℝ) < 2 * M + 1 := by positivity
      have hs : (-1 : ℝ) ^ M = (-1 : ℝ) ^ (M % 2) := neg_one_pow_eq_pow_mod_two (R := ℝ) M
      have hcard : (Finset.univ.filter fun i : Fin 1 => ξ i = true).card =
          if ξ 0 = true then 1 else 0 := by
        rw [Finset.card_filter, Fin.sum_univ_one]
      simp only [R, Q]
      rw [hcard]
      cases ξ 0
      · by_cases he : M % 2 = 0
        · simp [hs, he]
          field_simp
          ring
        · simp [Ne.symm he]
      · by_cases he : M % 2 = 1
        · simp [hs, he, hM]
          field_simp
          ring
        · simp [Ne.symm he]
    rw [hd1, hRQ M (by omega)] at hTV
    apply (D5.S3.TotalVariation.Metric.total_variation_eq_zero_iff _ _).mp
    simpa [totalVariation] using hTV

end D5.S3.TotalVariation.TreeParityKernel
