/- GID: D5/S3/Estimation/DecisionRisk/CARRevelationScaling
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/CARRevelationScaling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fully revealing mixtures scale both CAR deficiencies exactly and admit ordinary partition realizations on a common seed. -/

import D5.S3.Estimation.DecisionRisk.CARApproximateRecovery
import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Order.Partition.Finpartition

universe u
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators ENNReal
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open D5.S3.Estimation.DecisionRisk.CARApproximateRecovery

namespace D5.S3.Estimation.DecisionRisk.CARRevelationScaling

/-- Exact revelation scaling and ordinary partition laws on a common public seed.
`finiteDeficiency` takes the target first. The state type is arbitrary and nonempty;
all nonempty subsets, including zero-weight blocks, remain observation letters.
The common seed is the product of two finite partition selectors. Both experiments
expose the whole seed, and the final kernels prove exact equivalence with their
block observations, including probability-row completion at zero-weight blocks. -/
theorem result {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (w v : Block A → ℝ) (hw : ∀ B, 0 ≤ w B) (hv : ∀ B, 0 ≤ v B)
    (hwrow : ∀ i, ∑ B, row w i B = 1)
    (hvrow : ∀ i, ∑ B, row v i B = 1) :
    let M := fun (t : ℝ) (u : Block A → ℝ) B =>
      (1 - t) * (if B.1.card = 1 then 1 else 0) + t * u B
    let Seed := Option (Block A) × Option (Block A)
    let E := fun (p : Seed → ℝ) (P : Seed → Finpartition (Finset.univ : Finset A))
      (i : A) (o : Seed × Block A) => if (P o.1).part i = o.2.1 then p o.1 else 0
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      finiteDeficiency (row (M t v)) (row (M t w)) =
        ENNReal.ofReal t * finiteDeficiency (row v) (row w) ∧
      finiteDeficiency (row (M t w)) (row (M t v)) =
        ENNReal.ofReal t * finiteDeficiency (row w) (row v)) ∧
    (Fintype.card A = 1 → finiteDeficiency (row v) (row w) = 0 ∧
      finiteDeficiency (row w) (row v) = 0) ∧
    (2 ≤ Fintype.card A → ∀ t : ℝ, 0 ≤ t → t ≤ 2 / (Fintype.card A : ℝ) →
      ∃ (p : Seed → ℝ) (P Q : Seed → Finpartition (Finset.univ : Finset A)),
        (∀ r, 0 ≤ p r) ∧ (∑ r, p r = 1) ∧
        (∀ B, (∑ r, if B.1 ∈ (P r).parts then p r else 0) = M t w B) ∧
        (∀ B, (∑ r, if B.1 ∈ (Q r).parts then p r else 0) = M t v B) ∧
        (∃ (F : FiniteMarkovKernel (Seed × Block A) (Block A))
            (R : FiniteMarkovKernel (Block A) (Seed × Block A)),
          (∀ i, channelOutput F.1 (E p P i) = row (M t w) i) ∧
          (∀ i, channelOutput R.1 (row (M t w) i) = E p P i)) ∧
        (∃ (F : FiniteMarkovKernel (Seed × Block A) (Block A))
            (R : FiniteMarkovKernel (Block A) (Seed × Block A)),
          (∀ i, channelOutput F.1 (E p Q i) = row (M t v) i) ∧
          (∀ i, channelOutput R.1 (row (M t v) i) = E p Q i))) := by
  classical
  dsimp only
  have cost_expand {O D : Type u} [Fintype O] [Fintype D] (p : A → ℝ)
      (l : A → D → ℝ) (X : A → O → ℝ) (d : O → D → ℝ) :
      finiteBayesCost p l X d =
        ∑ a, ∑ b, d a b * ∑ i, p i * X i a * l i b := by
    simp only [finiteBayesCost, channelOutput, Finset.mul_sum, Finset.sum_mul]
    calc
      (∑ i, ∑ b, ∑ a, p i * (X i a * d a b * l i b)) =
          ∑ i, ∑ a, ∑ b, p i * (X i a * d a b * l i b) := by
        apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
      _ = ∑ a, ∑ i, ∑ b, p i * (X i a * d a b * l i b) := Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ i, p i * (X i a * d a b * l i b) := by
        apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        apply Finset.sum_congr rfl; intro i _; ring
  have bayes_attain {O D : Type u} [Fintype O] [Fintype D] [Nonempty D]
      (p : A → ℝ) (l : A → D → ℝ) (X : A → O → ℝ)
      (hp : ∀ i, 0 ≤ p i) (hl : ∀ i b, 0 ≤ l i b)
      (hX : ∀ i a, 0 ≤ X i a) :
      ∃ d : FiniteMarkovKernel O D,
        finiteBayesRisk p l X = ENNReal.ofReal (finiteBayesCost p l X d.1) ∧
        0 ≤ finiteBayesCost p l X d.1 ∧
        ∀ k : FiniteMarkovKernel O D,
          finiteBayesCost p l X d.1 ≤ finiteBayesCost p l X k.1 := by
    have hm (a : O) := Finset.exists_min_image Finset.univ
      (fun b : D => ∑ i, p i * X i a * l i b) Finset.univ_nonempty
    choose m hm using hm
    let d : FiniteMarkovKernel O D :=
      ⟨fun a b => if m a = b then 1 else 0,
        ⟨by intro a b; dsimp only; split_ifs <;> norm_num, by intro a; simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]⟩⟩
    have hd : finiteBayesCost p l X d.1 = ∑ a, ∑ i, p i * X i a * l i (m a) := by
      rw [cost_expand]
      simp [d]
    have hn : 0 ≤ finiteBayesCost p l X d.1 := by
      rw [hd]
      exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (hp i) (hX i a)) (hl i (m a))
    have hmin (k : FiniteMarkovKernel O D) :
        finiteBayesCost p l X d.1 ≤ finiteBayesCost p l X k.1 := by
      rw [hd, cost_expand]
      apply Finset.sum_le_sum
      intro a _
      calc
        (∑ i, p i * X i a * l i (m a)) =
            (∑ b, k.1 a b) * ∑ i, p i * X i a * l i (m a) := by rw [k.2.2, one_mul]
        _ = ∑ b, k.1 a b * ∑ i, p i * X i a * l i (m a) := Finset.sum_mul _ _ _
        _ ≤ _ := Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left ((hm a).2 b (Finset.mem_univ b)) (k.2.1 a b)
    refine ⟨d, le_antisymm (iInf_le _ d) (le_iInf fun k => ?_), hn, hmin⟩
    exact ENNReal.ofReal_le_ofReal (hmin k)
  -- The state-event simplex encodes a prior and bounded test simultaneously.
  have dual {O : Type u} [Fintype O] [DecidableEq O] [Nonempty O]
      (X Y : A → O → ℝ)
      (hX : IsRowStochastic X) (hY : IsRowStochastic Y) :
      ∃ (p : A → ℝ) (l : A → O → ℝ),
        ((∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) ∧
        (∀ i b, 0 ≤ l i b ∧ l i b ≤ 1) ∧
        ∃ K : FiniteMarkovKernel O O,
          uniformSimulationError Y X K ≤
            (finiteBayesRisk p l X).toReal - (finiteBayesRisk p l Y).toReal := by
    let I : FiniteMarkovKernel O O :=
      ⟨fun a b => if a = b then 1 else 0,
        ⟨by intro a b; dsimp only; split_ifs <;> norm_num,
          by intro a; exact Fintype.sum_ite_eq a (fun _ => (1 : ℝ))⟩⟩
    have comp_stoch (N : FiniteMarkovKernel O O) :
        IsRowStochastic (fun i => channelOutput N.1 (X i)) := by
      constructor
      · intro i b
        exact Finset.sum_nonneg fun a _ => mul_nonneg (hX.1 i a) (N.2.1 a b)
      · intro i
        simp only [channelOutput]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, N.2.2, mul_one]
        exact hX.2 i
    let KS : Set (O → O → ℝ) := Set.univ.pi (fun _ => stdSimplex ℝ O)
    let ZS : Set ((A × Finset O) → ℝ) := stdSimplex ℝ (A × Finset O)
    let f : (O → O → ℝ) → ((A × Finset O) → ℝ) → ℝ :=
      fun K z => ∑ t, z t * ∑ b ∈ t.2, (channelOutput K (X t.1) b - Y t.1 b)
    have hKS (K) : K ∈ KS ↔ IsRowStochastic K := by
      simp only [KS, Set.mem_pi, Set.mem_univ, forall_true_left, stdSimplex,
        Set.mem_ofPred_eq, IsRowStochastic]
      exact ⟨fun h => ⟨fun a b => (h a).1 b, fun a => (h a).2⟩,
        fun h a => ⟨h.1 a, h.2 a⟩⟩
    have cKS : Convex ℝ KS := convex_pi fun _ _ => convex_stdSimplex ℝ O
    have cZS : Convex ℝ ZS := convex_stdSimplex ℝ _
    have fx (z) : Continuous (fun K => f K z) := by
      dsimp only [f, channelOutput]
      fun_prop
    have fz (K) : Continuous (f K) := by
      dsimp only [f]
      fun_prop
    have ax (z) (K L : O → O → ℝ) (a b : ℝ) (hab : a + b = 1) :
        f (a • K + b • L) z = a * f K z + b * f L z := by
      have hm (i : A) (c : O) :
          channelOutput (a • K + b • L) (X i) c - Y i c =
            a * (channelOutput K (X i) c - Y i c) +
            b * (channelOutput L (X i) c - Y i c) := by
        have hc : channelOutput (a • K + b • L) (X i) c =
            a * channelOutput K (X i) c + b * channelOutput L (X i) c := by
          simp only [channelOutput, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro o _; ring
        rw [hc]
        linear_combination (Y i c) * hab
      dsimp only [f]
      calc
        (∑ t, z t * ∑ c ∈ t.2, (channelOutput (a • K + b • L) (X t.1) c - Y t.1 c)) =
            ∑ t, (a * (z t * ∑ c ∈ t.2, (channelOutput K (X t.1) c - Y t.1 c)) +
              b * (z t * ∑ c ∈ t.2, (channelOutput L (X t.1) c - Y t.1 c))) := by
          apply Finset.sum_congr rfl; intro t _
          simp_rw [hm, Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have az (K) (z u : (A × Finset O) → ℝ) (a b : ℝ) :
        f K (a • z + b • u) = a * f K z + b * f K u := by
      dsimp only [f]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro t _; ring
    have qx (z) : QuasiconvexOn ℝ KS (fun K => f K z) := by
      apply ConvexOn.quasiconvexOn
      refine ⟨cKS, ?_⟩
      intro K hK L hL a b ha hb hab
      exact (ax z K L a b hab).le
    have qz (K) : QuasiconcaveOn ℝ ZS (f K) := by
      apply ConcaveOn.quasiconcaveOn
      refine ⟨cZS, ?_⟩
      intro z hz u hu a b ha hb hab
      exact (az K z u a b).ge
    obtain ⟨K, hK, z, hz, hs⟩ := Sion.exists_isSaddlePointOn'
      (X := KS) (Y := ZS) (f := f)
      ⟨I.1, (hKS I.1).mpr I.2⟩
      (isCompact_univ_pi fun _ => isCompact_stdSimplex ℝ O)
      (fun z _ => (fx z).continuousOn.lowerSemicontinuousOn)
      (fun z _ => qx z) cZS (isCompact_stdSimplex ℝ _)
      (fun K _ => (fz K).continuousOn.upperSemicontinuousOn)
      (fun K _ => qz K) cKS
      ⟨Pi.single (Classical.choice (inferInstance : Nonempty A), ∅) 1, single_mem_stdSimplex ℝ _⟩
    let p : A → ℝ := fun i => ∑ E : Finset O, z (i, E)
    let g : A → O → ℝ := fun i b => ∑ E : Finset O, if b ∈ E then z (i, E) else 0
    have hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 := by
      refine ⟨fun i => Finset.sum_nonneg fun E _ => hz.1 (i, E), ?_⟩
      simpa only [p, ← Fintype.sum_prod_type] using hz.2
    have hg (i b) : 0 ≤ g i b ∧ g i b ≤ p i := by
      constructor
      · exact Finset.sum_nonneg fun E _ => by split_ifs; exact hz.1 (i, E); exact le_rfl
      · apply Finset.sum_le_sum; intro E _
        split_ifs; exact le_rfl; exact hz.1 (i, E)
    let l : A → O → ℝ := fun i b => if p i = 0 then 0 else g i b / p i
    have hl (i b) : 0 ≤ l i b ∧ l i b ≤ 1 := by
      dsimp only [l]
      split_ifs with h
      · norm_num
      · exact ⟨div_nonneg (hg i b).1 (hp.1 i),
          (div_le_one (lt_of_le_of_ne (hp.1 i) (Ne.symm h))).mpr (hg i b).2⟩
    have hpl (i b) : p i * l i b = g i b := by
      dsimp only [l]
      split_ifs with h
      · have : g i b = 0 := le_antisymm (by simpa [h] using (hg i b).2) (hg i b).1
        simp [h, this]
      · exact mul_div_cancel₀ _ h
    obtain ⟨d, hd, hdn, hdmin⟩ := bayes_attain p l X hp.1 (fun i b => (hl i b).1) hX.1
    obtain ⟨e, he, hen, hemin⟩ := bayes_attain p l Y hp.1 (fun i b => (hl i b).1) hY.1
    have hpay (L : O → O → ℝ) : f L z =
        finiteBayesCost p l X L - finiteBayesCost p l Y I.1 := by
      have hevent (i : A) (q : O → ℝ) :
          (∑ E : Finset O, z (i, E) * ∑ b ∈ E, q b) = ∑ b, g i b * q b := by
        dsimp only [g]
        simp_rw [Finset.mul_sum, Finset.sum_mul, ite_mul, zero_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro E _
        simp only [← Finset.sum_filter]
        simp
      dsimp only [f]
      rw [Fintype.sum_prod_type]
      simp_rw [hevent, mul_sub, Finset.sum_sub_distrib]
      have hcost (T : A → O → ℝ) (N : O → O → ℝ) :
          finiteBayesCost p l T N = ∑ i, ∑ b, g i b * channelOutput N (T i) b := by
        simp only [finiteBayesCost, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro b _
        rw [← hpl]; ring
      rw [hcost, hcost]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro b _
      simp only [I, channelOutput, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have hTV (i : A) :
        totalVariation (Y i) (channelOutput K (X i)) ≤ f d.1 z := by
      let E : Finset O := Finset.univ.filter (fun b => Y i b ≤ channelOutput K (X i) b)
      have hvtx := hs d.1 ((hKS d.1).mpr d.2) (Pi.single (i, E) 1)
        (single_mem_stdSimplex ℝ _)
      have hmass : (∑ b, channelOutput K (X i) b) = ∑ b, Y i b :=
        ((comp_stoch ⟨K, (hKS K).mp hK⟩).2 i).trans (hY.2 i).symm
      rw [total_variation_comm, total_variation_eq_sum_positive _ _ hmass]
      change (∑ b ∈ E, (channelOutput K (X i) b - Y i b)) ≤ f d.1 z
      simpa only [f, Pi.single_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] using hvtx
    refine ⟨p, l, hp, hl, ⟨K, (hKS K).mp hK⟩, ?_⟩
    calc
      uniformSimulationError Y X ⟨K, (hKS K).mp hK⟩ ≤ f d.1 z :=
        Finset.sup'_le _ _ (fun i _ => hTV i)
      _ ≤ finiteBayesCost p l X d.1 - finiteBayesCost p l Y e.1 := by
        rw [hpay]; linarith [hemin I]
      _ = _ := by rw [hd, he, ENNReal.toReal_ofReal hdn, ENNReal.toReal_ofReal hen]
  let O := Block (A)
  letI : Nonempty O := ⟨⟨{Classical.choice (inferInstance : Nonempty A)}, by simp⟩⟩
  let I : FiniteMarkovKernel O O := ⟨fun a b => if a = b then 1 else 0,
    ⟨by intro a b; dsimp only; split_ifs <;> norm_num, by intro a; exact Fintype.sum_ite_eq a (fun _ => (1 : ℝ))⟩⟩
  have comp_stoch (X : A → O → ℝ) (hX : IsRowStochastic X)
      (K : FiniteMarkovKernel O O) :
      IsRowStochastic (fun i => channelOutput K.1 (X i)) := by
    constructor
    · intro i b
      exact Finset.sum_nonneg fun a _ => mul_nonneg (hX.1 i a) (K.2.1 a b)
    · intro i
      simp only [channelOutput]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, K.2.2, mul_one]
      exact hX.2 i
  have def_le_one (X Y : A → O → ℝ)
      (hX : IsRowStochastic X) (hY : IsRowStochastic Y) :
      finiteDeficiency Y X ≤ 1 := by
    apply (iInf_le _ I).trans
    apply ENNReal.ofReal_le_one.mpr
    apply Finset.sup'_le
    intro i _
    exact total_variation_le_one _ _ ⟨hY.1 i, hY.2 i⟩
      ⟨(comp_stoch X hX I).1 i, (comp_stoch X hX I).2 i⟩
  have hfin (X Y : A → O → ℝ) (hX : IsRowStochastic X)
      (hY : IsRowStochastic Y) : finiteDeficiency Y X ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num) (def_le_one X Y hX hY)
  have block_risk {D : Type u} [Fintype D] [Nonempty D]
      (p : A → ℝ) (l : A → D → ℝ) :
      ∃ H : Finset (A) → ℝ,
        (∀ S, (∀ a, H S ≤ ∑ i ∈ S, p i * l i a) ∧
          ∃ a, H S = ∑ i ∈ S, p i * l i a) ∧
        ∀ u : O → ℝ, (∀ B, 0 ≤ u B) →
          finiteBayesRisk p l (row u) = ENNReal.ofReal (∑ B, u B * H B.1) := by
    have hm (S : Finset (A)) := Finset.exists_min_image Finset.univ
      (fun a : D => ∑ i ∈ S, p i * l i a) Finset.univ_nonempty
    choose m hm using hm
    let H : Finset (A) → ℝ := fun S => ∑ i ∈ S, p i * l i (m S)
    have hH (S) : (∀ a, H S ≤ ∑ i ∈ S, p i * l i a) ∧
        ∃ a, H S = ∑ i ∈ S, p i * l i a :=
      ⟨fun a => (hm S).2 a (Finset.mem_univ a), m S, rfl⟩
    refine ⟨H, hH, ?_⟩
    intro u hu
    have hc (d : O → D → ℝ) : finiteBayesCost p l (row u) d =
        ∑ B, u B * ∑ a, d B a * ∑ i ∈ B.1, p i * l i a := by
      rw [cost_expand]
      apply Finset.sum_congr rfl; intro B _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      have hh : (∑ i, p i * row u i B * l i a) =
          u B * ∑ i ∈ B.1, p i * l i a := by
        simp only [row, mul_ite, ite_mul, mul_zero, zero_mul]
        rw [← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hh]; ring
    let d : FiniteMarkovKernel O D :=
      ⟨fun B a => if m B.1 = a then 1 else 0,
        ⟨by intro B a; dsimp only; split_ifs <;> norm_num,
          by intro B; simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]⟩⟩
    have hd : finiteBayesCost p l (row u) d.1 = ∑ B, u B * H B.1 := by
      rw [hc]
      simp only [d, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, H]
    apply le_antisymm
    · exact (iInf_le _ d).trans_eq (congrArg ENNReal.ofReal hd)
    · apply le_iInf; intro k
      apply ENNReal.ofReal_le_ofReal
      rw [hc]
      apply Finset.sum_le_sum; intro B _
      apply mul_le_mul_of_nonneg_left _ (hu B)
      calc H B.1 = (∑ a, k.1 B a) * H B.1 := by rw [k.2.2, one_mul]
        _ = ∑ a, k.1 B a * H B.1 := Finset.sum_mul _ _ _
        _ ≤ _ := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left ((hH B.1).1 a) (k.2.1 B a)

  let reveal : O → ℝ := fun B => if B.1.card = 1 then 1 else 0
  let M := fun (t : ℝ) (u : O → ℝ) B => (1 - t) * reveal B + t * u B
  let sing := fun i : A => (⟨{i}, by simp⟩ : O)
  have hs (i : A) (B : O) : row reveal i B = if sing i = B then 1 else 0 := by
    by_cases he : sing i = B
    · subst B; simp [row, reveal, sing]
    · have hn : ¬(i ∈ B.1 ∧ B.1.card = 1) := by
        rintro ⟨hi, hc⟩
        obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
        have hij : i = j := by simpa [hj] using hi
        apply he
        apply Subtype.ext
        simpa [sing, hij] using hj.symm
      simp only [row, reveal, if_neg he]
      split_ifs with hi hc
      · exact False.elim (hn ⟨hi, hc⟩)
      · rfl
      · rfl
  have hr : ∀ i, ∑ B, row reveal i B = 1 := by
    intro i; simp_rw [hs]; simp
  have hMnon (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
      (u : O → ℝ) (hu : ∀ B, 0 ≤ u B) (B : O) : 0 ≤ M t u B := by
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (by dsimp [reveal]; split_ifs <;> norm_num))
      (mul_nonneg ht (hu B))
  have hMrow (t : ℝ) (u : O → ℝ) (i : A) (B : O) :
      row (M t u) i B = (1 - t) * row reveal i B + t * row u i B := by
    dsimp only [row, M]; split_ifs <;> ring
  have hMstoch (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
      (u : O → ℝ) (hu : ∀ B, 0 ≤ u B) (hur : ∀ i, ∑ B, row u i B = 1) :
      IsRowStochastic (row (M t u)) := by
    constructor
    · intro i B; dsimp only [row]; split_ifs
      · exact hMnon t ht ht1 u hu B
      · exact le_rfl
    · intro i
      simp_rw [hMrow, Finset.sum_add_distrib, ← Finset.mul_sum, hr, hur]
      ring
  have risk_le (X Y : A → O → ℝ) (hX : IsRowStochastic X) (hY : IsRowStochastic Y)
      (p : A → ℝ) (l : A → O → ℝ)
      (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
      (hl : ∀ i a, 0 ≤ l i a ∧ l i a ≤ 1) :
      (finiteBayesRisk p l X).toReal - (finiteBayesRisk p l Y).toReal ≤
        (finiteDeficiency Y X).toReal := by
    obtain ⟨d, hd, _, _⟩ := bayes_attain p l X hp.1 (fun i a => (hl i a).1) hX.1
    obtain ⟨e, he, _, _⟩ := bayes_attain p l Y hp.1 (fun i a => (hl i a).1) hY.1
    have hfx : finiteBayesRisk p l X ≠ ⊤ := by rw [hd]; exact ENNReal.ofReal_ne_top
    have hfy : finiteBayesRisk p l Y ≠ ⊤ := by rw [he]; exact ENNReal.ofReal_ne_top
    have hf := hfin X Y hX hY
    have h := (ENNReal.toReal_le_toReal hfx (ENNReal.add_ne_top.mpr ⟨hfy, hf⟩)).mpr
      (deficiency_risk_bound p l X Y hp hX hY hl)
    rw [ENNReal.toReal_add hfy hf] at h
    linarith
  -- Finiteness is proved before converting the two risks and deficiency to reals.
  have exact_dual (X Y : A → O → ℝ) (hX : IsRowStochastic X) (hY : IsRowStochastic Y) :
      ∃ (p : A → ℝ) (l : A → O → ℝ) (K : FiniteMarkovKernel O O),
        ((∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) ∧
        (∀ i a, 0 ≤ l i a ∧ l i a ≤ 1) ∧
        (finiteBayesRisk p l X).toReal - (finiteBayesRisk p l Y).toReal =
          (finiteDeficiency Y X).toReal ∧
        ENNReal.ofReal (uniformSimulationError Y X K) = finiteDeficiency Y X := by
    obtain ⟨p, l, hp, hl, K, hK⟩ := dual X Y hX hY
    have he0 : 0 ≤ uniformSimulationError Y X K :=
      (total_variation_nonneg (Y (Classical.choice (inferInstance : Nonempty A)))
        (channelOutput K.1 (X (Classical.choice (inferInstance : Nonempty A))))).trans
        (Finset.le_sup' (fun i => totalVariation (Y i) (channelOutput K.1 (X i)))
          (Finset.mem_univ (Classical.choice (inferInstance : Nonempty A))))
    have hde : (finiteDeficiency Y X).toReal ≤ uniformSimulationError Y X K := by
      have h := (ENNReal.toReal_le_toReal (hfin X Y hX hY) ENNReal.ofReal_ne_top).mpr
        (iInf_le _ K)
      simpa only [ENNReal.toReal_ofReal he0] using h
    have hgap := risk_le X Y hX hY p l hp hl
    have heq : (finiteBayesRisk p l X).toReal - (finiteBayesRisk p l Y).toReal =
        (finiteDeficiency Y X).toReal := le_antisymm hgap (hde.trans hK)
    refine ⟨p, l, K, hp, hl, heq, ?_⟩
    have herr : uniformSimulationError Y X K = (finiteDeficiency Y X).toReal := by linarith
    rw [herr, ENNReal.ofReal_toReal (hfin X Y hX hY)]
  -- The same task has a common full-revelation term, which cancels.
  have gap_scale (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
      (u z : O → ℝ) (hu : ∀ B, 0 ≤ u B) (hz : ∀ B, 0 ≤ z B)
      (p : A → ℝ) (l : A → O → ℝ)
      (hp : ∀ i, 0 ≤ p i) (hl : ∀ i a, 0 ≤ l i a) :
      (finiteBayesRisk p l (row (M t u))).toReal -
        (finiteBayesRisk p l (row (M t z))).toReal =
      t * ((finiteBayesRisk p l (row u)).toReal -
        (finiteBayesRisk p l (row z)).toReal) := by
    obtain ⟨H, hH, hR⟩ := block_risk p l
    have hH0 (B : O) : 0 ≤ H B.1 := by
      obtain ⟨a, ha⟩ := (hH B.1).2
      rw [ha]; exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hl i a)
    have hreal (z : O → ℝ) (hz : ∀ B, 0 ≤ z B) :
        (finiteBayesRisk p l (row z)).toReal = ∑ B, z B * H B.1 := by
      rw [hR z hz, ENNReal.toReal_ofReal (Finset.sum_nonneg fun B _ => mul_nonneg (hz B) (hH0 B))]
    rw [hreal _ (hMnon t ht ht1 u hu), hreal _ (hMnon t ht ht1 z hz), hreal u hu, hreal z hz]
    simp only [M, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have scale (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
      (u z : O → ℝ) (hu : ∀ B, 0 ≤ u B) (hz : ∀ B, 0 ≤ z B)
      (hur : ∀ i, ∑ B, row u i B = 1) (hzr : ∀ i, ∑ B, row z i B = 1) :
      finiteDeficiency (row (M t z)) (row (M t u)) =
        ENNReal.ofReal t * finiteDeficiency (row z) (row u) := by
    have hU : IsRowStochastic (row u) :=
      ⟨by intro i B; dsimp only [row]; split_ifs; exact hu B; exact le_rfl, hur⟩
    have hZ : IsRowStochastic (row z) :=
      ⟨by intro i B; dsimp only [row]; split_ifs; exact hz B; exact le_rfl, hzr⟩
    have hMU := hMstoch t ht ht1 u hu hur
    have hMZ := hMstoch t ht ht1 z hz hzr
    have hf := hfin (row u) (row z) hU hZ
    have hmf := hfin (row (M t u)) (row (M t z)) hMU hMZ
    apply (ENNReal.toReal_eq_toReal_iff' hmf (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
    apply le_antisymm
    · obtain ⟨p, l, K, hp, hl, heq, _⟩ := exact_dual _ _ hMU hMZ
      rw [← heq, gap_scale t ht ht1 u z hu hz p l hp.1 (fun i a => (hl i a).1)]
      exact mul_le_mul_of_nonneg_left (risk_le _ _ hU hZ p l hp hl) ht
    · obtain ⟨p, l, K, hp, hl, heq, _⟩ := exact_dual _ _ hU hZ
      rw [← heq, ← gap_scale t ht ht1 u z hu hz p l hp.1 (fun i a => (hl i a).1)]
      exact risk_le _ _ hMU hMZ p l hp hl
  refine ⟨?_, ?_, ?_⟩
  · intro t ht ht1
    exact ⟨scale t ht ht1 w v hw hv hwrow hvrow, scale t ht ht1 v w hv hw hvrow hwrow⟩
  · intro hn
    letI : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp hn.le
    have hB (B : O) : B.1 = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      obtain ⟨j, hj⟩ := B.2
      simpa only [Subsingleton.elim i j] using hj
    letI : Subsingleton O := ⟨fun B C => Subtype.ext ((hB B).trans (hB C).symm)⟩
    letI : Unique O := { default := sing (Classical.choice (inferInstance : Nonempty A)),
                         uniq := fun _ => Subsingleton.elim _ _ }
    have huw (u : O → ℝ) (hu : ∀ i, ∑ B, row u i B = 1) : ∀ B, u B = 1 := by
      intro B
      have h := hu (Classical.choice (inferInstance : Nonempty A))
      simp only [Fintype.sum_unique, row, hB, Finset.mem_univ, if_true] at h
      simpa only [Subsingleton.elim (default : O) B] using h
    have hwv : w = v := funext fun B => (huw w hwrow B).trans (huw v hvrow B).symm
    have hz : finiteDeficiency (row w) (row w) = 0 := by
      apply le_antisymm _ bot_le
      apply (iInf_le _ I).trans_eq
      have hi (i : A) : channelOutput I.1 (row w i) = row w i := by
        funext B; simp [channelOutput, I, Subsingleton.elim (default : O) B]
      have hz (i : A) : totalVariation (row w i) (channelOutput I.1 (row w i)) = 0 := by
        rw [hi]; exact (total_variation_eq_zero_iff _ _).mpr rfl
      simp only [uniformSimulationError, hz, Finset.sup'_const, ENNReal.ofReal_zero]; rfl
    simpa only [← hwv] using And.intro hz hz
  · intro hn t ht htn
    have hn0 : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
    have hn2 : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hn
    have ht1 : t ≤ 1 := htn.trans ((div_le_one hn0).mpr hn2)
    have hparts (B : O) : ∃ P : Finpartition (Finset.univ : Finset A),
        ∀ C : Finset A, C ∈ P.parts ↔ C = B.1 ∨ ∃ i, i ∉ B.1 ∧ C = {i} := by
      let parts : Finset (Finset A) := insert B.1 ((Finset.univ \ B.1).image (fun i : A => ({i} : Finset A)))
      have hm (C : Finset A) : C ∈ parts ↔ C = B.1 ∨ ∃ i, i ∉ B.1 ∧ C = {i} := by
        simp only [parts, Finset.mem_insert, Finset.mem_image, Finset.mem_sdiff,
          Finset.mem_univ, true_and]
        constructor
        · rintro (h | ⟨i, hi, hC⟩)
          · exact Or.inl h
          · exact Or.inr ⟨i, hi, hC.symm⟩
        · rintro (h | ⟨i, hi, hC⟩)
          · exact Or.inl h
          · exact Or.inr ⟨i, hi, hC.symm⟩
      have hu (i : A) : ∃! C, C ∈ parts ∧ i ∈ C := by
        by_cases hi : i ∈ B.1
        · refine ⟨B.1, ⟨(hm _).mpr (Or.inl rfl), hi⟩, ?_⟩
          intro C hC
          rcases (hm C).mp hC.1 with he | ⟨j, hj, he⟩
          · exact he
          · have hij : i = j := by simpa [he] using hC.2
            exact False.elim (hj (hij ▸ hi))
        · refine ⟨{i}, ⟨(hm _).mpr (Or.inr ⟨i, hi, rfl⟩), by simp⟩, ?_⟩
          intro C hC
          rcases (hm C).mp hC.1 with he | ⟨j, hj, he⟩
          · exact False.elim (hi (he ▸ hC.2))
          · have hij : i = j := by simpa [he] using hC.2
            simpa [hij] using he
      let P : Finpartition (Finset.univ : Finset A) := Finpartition.ofExistsUnique parts
        (fun _ _ => Finset.subset_univ _) (fun i _ => hu i) (by
          intro he
          rcases (hm ∅).mp he with he | ⟨i, _, he⟩
          · exact B.2.ne_empty he.symm
          · exact (Finset.singleton_ne_empty i) he.symm)
      exact ⟨P, hm⟩
    choose part hpart using hparts
    let P : Option O → Finpartition (Finset.univ : Finset A) :=
      fun r => match r with | none => ⊥ | some B => part B
    have hPnone (B : O) : B.1 ∈ (P none).parts ↔ B.1.card = 1 := by
      change B.1 ∈ (⊥ : Finpartition (Finset.univ : Finset A)).parts ↔ _
      rw [Finpartition.mem_bot_iff]
      simp only [Finset.mem_univ, true_and, Finset.card_eq_one]
      exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
    have single_row (u : O → ℝ) (hur : ∀ i, ∑ B, row u i B = 1) (i : A) :
        u (sing i) + (∑ B : O, if 2 ≤ B.1.card ∧ i ∈ B.1 then u B else 0) = 1 := by
      have hb (B : O) : row u i B =
          (if sing i = B then u B else 0) + (if 2 ≤ B.1.card ∧ i ∈ B.1 then u B else 0) := by
        by_cases hi : i ∈ B.1
        · by_cases hcard : B.1.card = 1
          · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
            have hij : i = j := by simpa [hj] using hi
            have he : sing i = B := Subtype.ext (by simpa [sing, hij] using hj.symm)
            simp [row, hi, he, hcard]
          · have hc : 2 ≤ B.1.card := by have := B.2.card_pos; omega
            have he : sing i ≠ B := by intro he; have hh := congrArg (fun C : O => C.1.card) he; simp only [sing, Finset.card_singleton] at hh; exact hcard hh.symm
            simp [row, hi, hc, he]
        · have he : sing i ≠ B := by intro he; apply hi; rw [← he]; simp [sing]
          simp [row, hi, he]
      have h := hur i
      simp_rw [hb, Finset.sum_add_distrib] at h
      simpa only [Finset.sum_ite_eq, Finset.mem_univ, if_true] using h
    -- One non-singleton block plus outside singletons; the residual mass is discrete.
    have law (u : O → ℝ) (hu : ∀ B, 0 ≤ u B) (hur : ∀ i, ∑ B, row u i B = 1) :
        ∃ p : Option O → ℝ, (∀ r, 0 ≤ p r) ∧ (∑ r, p r = 1) ∧
          ∀ B, (∑ r, if B.1 ∈ (P r).parts then p r else 0) = M t u B := by
      let S : ℝ := ∑ B : O, if 2 ≤ B.1.card then u B else 0
      have hd : (∑ B : O, (B.1.card : ℝ) * u B) = Fintype.card A := by
        calc
          (∑ B : O, (B.1.card : ℝ) * u B) = ∑ B : O, ∑ i : A, row u i B := by
            apply Finset.sum_congr rfl; intro B _
            simp [row, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
          _ = ∑ i : A, ∑ B : O, row u i B := Finset.sum_comm
          _ = ∑ _i : A, (1 : ℝ) := Finset.sum_congr rfl (fun i _ => hur i)
          _ = (Fintype.card A : ℝ) := by simp
      have hS : 2 * S ≤ (Fintype.card A : ℝ) := by
        change 2 * (∑ B : O, if 2 ≤ B.1.card then u B else 0) ≤ _
        rw [← hd, Finset.mul_sum]
        apply Finset.sum_le_sum; intro B _
        split_ifs with hB
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hB) (hu B)
        · simpa only [mul_zero] using mul_nonneg (Nat.cast_nonneg B.1.card) (hu B)
      have htS : t * S ≤ 1 := by
        have hS0 : 0 ≤ S := Finset.sum_nonneg fun B _ => by split_ifs; exact hu B; exact le_rfl
        calc
          t * S ≤ (2 / (Fintype.card A : ℝ)) * S := mul_le_mul_of_nonneg_right htn hS0
          _ ≤ (2 / (Fintype.card A : ℝ)) * ((Fintype.card A : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (by norm_num) hn0.le)
          _ = 1 := by field_simp
      let p : Option O → ℝ := fun r => match r with
        | none => 1 - t * S
        | some B => if 2 ≤ B.1.card then t * u B else 0
      have hp0 : ∀ r, 0 ≤ p r := by
        intro r; cases r with
        | none => exact sub_nonneg.mpr htS
        | some B => dsimp only [p]; split_ifs; exact mul_nonneg ht (hu B); exact le_rfl
      have hp1 : ∑ r, p r = 1 := by
        rw [Fintype.sum_option]
        dsimp only [p]
        have he : (∑ B : O, if 2 ≤ B.1.card then t * u B else 0) = t * S := by
          simp only [S, Finset.mul_sum, mul_ite, mul_zero]
        rw [he]; ring
      refine ⟨p, hp0, hp1, ?_⟩
      intro C
      rw [Fintype.sum_option]
      have hsome (B : O) : (if C.1 ∈ (P (some B)).parts then p (some B) else 0) =
          if 2 ≤ B.1.card then
            if C = B ∨ ∃ i, i ∉ B.1 ∧ C.1 = {i} then t * u B else 0 else 0 := by
        have he : C.1 = B.1 ↔ C = B := Subtype.ext_iff.symm
        simp only [P, hpart, he, p]
        split_ifs <;> rfl
      simp_rw [hsome]
      simp only [hPnone]
      by_cases hc : C.1.card = 1
      · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
        have hC : C = sing i := Subtype.ext hi
        have he (B : O) :
            (if 2 ≤ B.1.card then if C = B ∨ ∃ i, i ∉ B.1 ∧ C.1 = {i} then t * u B else 0 else 0) =
            t * (if 2 ≤ B.1.card ∧ i ∉ B.1 then u B else 0) := by
          by_cases hB : 2 ≤ B.1.card
          · have hCB : C ≠ B := by
              intro he
              have hcB : B.1.card = 1 := by rw [← he]; exact hc
              omega
            have hevent : (C = B ∨ ∃ j, j ∉ B.1 ∧ C.1 = {j}) ↔ i ∉ B.1 := by
              constructor
              · rintro (h | ⟨j, hj, hCj⟩)
                · exact False.elim (hCB h)
                · have hij : i = j := Finset.singleton_injective (hi.symm.trans hCj)
                  simpa only [hij] using hj
              · intro h; exact Or.inr ⟨i, h, hi⟩
            simp only [hB, if_true, hevent, true_and, mul_ite, mul_zero]
          · simp [hB]
        simp_rw [he]
        have hsplit : S = (∑ B : O, if 2 ≤ B.1.card ∧ i ∈ B.1 then u B else 0) +
            ∑ B : O, if 2 ≤ B.1.card ∧ i ∉ B.1 then u B else 0 := by
          change (∑ B : O, if 2 ≤ B.1.card then u B else 0) = _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro B _
          by_cases hB : 2 ≤ B.1.card <;> by_cases hBi : i ∈ B.1 <;> simp [hB, hBi]
        have hirow := single_row u hur i
        simp only [p, M, reveal, hc, if_true, mul_one, ← Finset.mul_sum]
        rw [hC]
        linear_combination -t * hirow - t * hsplit
      · have hc2 : 2 ≤ C.1.card := by have := C.2.card_pos; omega
        have he (B : O) :
            (if 2 ≤ B.1.card then if C = B ∨ ∃ i, i ∉ B.1 ∧ C.1 = {i} then t * u B else 0 else 0) =
            if C = B then t * u B else 0 := by
          have hn : ¬∃ i, i ∉ B.1 ∧ C.1 = {i} := by
            rintro ⟨i, _, hi⟩; apply hc; simp [hi]
          by_cases hCB : C = B
          · subst B; simp [hc2]
          · simp [hCB, hn]
        simp_rw [he]
        simp only [hc, M, reveal, if_false, mul_zero, zero_add]
        exact Fintype.sum_ite_eq C (fun B => t * u B)
    obtain ⟨pw, hpw0, hpw1, hpw⟩ := law w hw hwrow
    obtain ⟨pv, hpv0, hpv1, hpv⟩ := law v hv hvrow
    let p : (Option O × Option O) → ℝ := fun r => pw r.1 * pv r.2
    have hp0 : ∀ r, 0 ≤ p r := fun r => mul_nonneg (hpw0 r.1) (hpv0 r.2)
    have hp1 : ∑ r, p r = 1 := by
      simp only [p, Fintype.sum_prod_type, ← Finset.mul_sum, hpv1, mul_one, hpw1]
    have hPw (B : O) : (∑ r : Option O × Option O,
        if B.1 ∈ (P r.1).parts then p r else 0) = M t w B := by
      simp only [p, Fintype.sum_prod_type]
      have hrow (r : Option O) : (∑ s : Option O,
          if B.1 ∈ (P r).parts then pw r * pv s else 0) =
          if B.1 ∈ (P r).parts then pw r else 0 := by
        by_cases h : B.1 ∈ (P r).parts <;> simp [h, ← Finset.mul_sum, hpv1]
      simp_rw [hrow]
      exact hpw B
    have hPv (B : O) : (∑ r : Option O × Option O,
        if B.1 ∈ (P r.2).parts then p r else 0) = M t v B := by
      simp only [p, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      have hrow (s : Option O) : (∑ r : Option O,
          if B.1 ∈ (P s).parts then pw r * pv s else 0) =
          if B.1 ∈ (P s).parts then pv s else 0 := by
        by_cases h : B.1 ∈ (P s).parts <;> simp [h, ← Finset.sum_mul, hpw1]
      simp_rw [hrow]
      exact hpv B
    let Seed := Option O × Option O
    -- Condition the entire product seed on the observed block, with a fixed zero row.
    have normalize (u : O → ℝ) (hu : ∀ B, 0 ≤ u B)
        (T : Seed → Finpartition (Finset.univ : Finset A))
        (hT : ∀ B, (∑ r, if B.1 ∈ (T r).parts then p r else 0) = u B) :
        ∃ (F : FiniteMarkovKernel (Seed × O) O) (R : FiniteMarkovKernel O (Seed × O)),
          (∀ i, channelOutput F.1 (fun o => if (T o.1).part i = o.2.1 then p o.1 else 0) = row u i) ∧
          (∀ i, channelOutput R.1 (row u i) =
            fun o => if (T o.1).part i = o.2.1 then p o.1 else 0) := by
      have hpartiff (r : Seed) (i : A) (B : O) :
          (T r).part i = B.1 ↔ B.1 ∈ (T r).parts ∧ i ∈ B.1 := by
        constructor
        · intro he
          refine ⟨?_, ?_⟩
          · rw [← he]; exact (T r).part_mem.mpr (Finset.mem_univ i)
          · rw [← he]; exact (T r).mem_part_self.mpr (Finset.mem_univ i)
        · intro h
          exact (T r).part_eq_of_mem h.1 h.2
      let F : FiniteMarkovKernel (Seed × O) O :=
        ⟨fun o B => if o.2 = B then 1 else 0,
          ⟨by intro o B; dsimp only; split_ifs <;> norm_num,
            by intro o; exact Fintype.sum_ite_eq o.2 (fun _ => (1 : ℝ))⟩⟩
      have hF (i : A) : channelOutput F.1
          (fun o => if (T o.1).part i = o.2.1 then p o.1 else 0) = row u i := by
        funext B
        simp only [channelOutput, F, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
        have hsum (r : Seed) : (∑ C : O,
            if C = B then (if (T r).part i = C.1 then p r else 0) else 0) =
            (if (T r).part i = B.1 then p r else 0) :=
          Fintype.sum_ite_eq' B (fun C => if (T r).part i = C.1 then p r else 0)
        simp_rw [hsum, hpartiff]
        by_cases hi : i ∈ B.1
        · simp only [hi, and_true, row, if_true]; exact hT B
        · simp [hi, row]
      have hpu (B : O) (r : Seed) (hB : B.1 ∈ (T r).parts) : p r ≤ u B := by
        rw [← hT B]
        calc
          p r = (if B.1 ∈ (T r).parts then p r else 0) := (if_pos hB).symm
          _ ≤ ∑ r, if B.1 ∈ (T r).parts then p r else 0 := by
            apply Finset.single_le_sum _ (Finset.mem_univ r)
            intro s _; split_ifs; exact hp0 s; exact le_rfl
      let o0 : Seed × O := ((none, none), sing (Classical.choice (inferInstance : Nonempty A)))
      let R : O → Seed × O → ℝ := fun B o =>
        if u B = 0 then (if o0 = o then 1 else 0)
        else if B = o.2 ∧ B.1 ∈ (T o.1).parts then p o.1 / u B else 0
      have hR0 : ∀ B o, 0 ≤ R B o := by
        intro B o; dsimp only [R]; split_ifs
        · norm_num
        · exact le_rfl
        · exact div_nonneg (hp0 o.1) (hu B)
        · exact le_rfl
      have hR1 (B : O) : ∑ o, R B o = 1 := by
        by_cases hz : u B = 0
        · simp only [R, hz, if_true]
          exact Fintype.sum_ite_eq o0 (fun _ => (1 : ℝ))
        · simp only [R, hz, if_false, Fintype.sum_prod_type]
          have he (r : Seed) :
              (∑ C : O, if B = C ∧ B.1 ∈ (T r).parts then p r / u B else 0) =
              (if B.1 ∈ (T r).parts then p r else 0) / u B := by
            by_cases hB : B.1 ∈ (T r).parts
            · simp only [hB, and_true, if_true]
              exact Fintype.sum_ite_eq B (fun _ => p r / u B)
            · simp only [hB, and_false, if_false, Finset.sum_const_zero, zero_div]
          simp_rw [he]
          rw [← Finset.sum_div, hT B, div_self hz]
      have hmass (B : O) (o : Seed × O) :
          u B * R B o = if B = o.2 ∧ B.1 ∈ (T o.1).parts then p o.1 else 0 := by
        by_cases hz : u B = 0
        · have hpz (hB : B.1 ∈ (T o.1).parts) : p o.1 = 0 :=
            le_antisymm (by simpa [hz] using hpu B o.1 hB) (hp0 o.1)
          dsimp only [R]; rw [if_pos hz, hz, zero_mul]
          split_ifs with h
          · exact (hpz h.2).symm
          · rfl
        · dsimp only [R]; rw [if_neg hz]
          split_ifs
          · exact mul_div_cancel₀ _ hz
          · exact mul_zero _
      have hR (i : A) : channelOutput R (row u i) =
          fun o => if (T o.1).part i = o.2.1 then p o.1 else 0 := by
        funext o
        have he (B : O) : row u i B * R B o =
            if B = o.2 then (if B.1 ∈ (T o.1).parts ∧ i ∈ B.1 then p o.1 else 0) else 0 := by
          dsimp only [row]
          rw [ite_mul, zero_mul, hmass]
          by_cases hBC : B = o.2
          · subst B
            by_cases hi : i ∈ o.2.1 <;> by_cases hB : o.2.1 ∈ (T o.1).parts <;>
              simp only [hi, hB, and_self, and_false, and_true, if_true, if_false]
          · simp only [hBC, false_and, if_false, ite_self]
        simp only [channelOutput]
        simp_rw [he]
        rw [Fintype.sum_ite_eq']
        simp only [hpartiff]
      exact ⟨F, ⟨R, hR0, hR1⟩, hF, hR⟩
    refine ⟨p, (fun r => P r.1), (fun r => P r.2), hp0, hp1, hPw, hPv, ?_, ?_⟩
    · exact normalize (M t w) (hMnon t ht ht1 w hw) (fun r => P r.1) hPw
    · exact normalize (M t v) (hMnon t ht ht1 v hv) (fun r => P r.2) hPv


end D5.S3.Estimation.DecisionRisk.CARRevelationScaling
