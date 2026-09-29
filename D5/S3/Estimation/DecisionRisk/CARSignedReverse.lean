/- GID: D5/S3/Estimation/DecisionRisk/CARSignedReverse
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/CARSignedReverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-state CAR profiles satisfy the signed three-halves reverse deficiency bound. -/

import D5.S3.Estimation.DecisionRisk.CARApproximateRecovery
import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open scoped BigOperators ENNReal
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open D5.S3.Estimation.DecisionRisk.CARApproximateRecovery

namespace D5.S3.Estimation.DecisionRisk.CARSignedReverse

/-- The unrestricted three-state CAR deficiency satisfies the signed reverse bound. -/
theorem result (w v : Block (Fin 3) → ℝ)
    (hw : ∀ B, 0 ≤ w B) (hv : ∀ B, 0 ≤ v B)
    (hwrow : ∀ i, ∑ B, row w i B = 1)
    (hvrow : ∀ i, ∑ B, row v i B = 1) :
    let Δ := fun i j => pair v i j - pair w i j
    let R := (1 / 2 : ℝ) * Finset.univ.sup' Finset.univ_nonempty
      (fun i => ∑ j ∈ Finset.univ.erase i, max (Δ i j) 0)
    finiteDeficiency (row w) (row v) ≤
      ENNReal.ofReal (min 1 (R + (3 / 2 : ℝ) *
        (finiteDeficiency (row v) (row w)).toReal)) := by
  classical
  dsimp only
  have cost_expand {O D : Type} [Fintype O] [Fintype D] (p : Fin 3 → ℝ)
      (l : Fin 3 → D → ℝ) (X : Fin 3 → O → ℝ) (d : O → D → ℝ) :
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
  have bayes_attain {O D : Type} [Fintype O] [Fintype D] [Nonempty D]
      (p : Fin 3 → ℝ) (l : Fin 3 → D → ℝ) (X : Fin 3 → O → ℝ)
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
  have dual {O : Type} [Fintype O] [DecidableEq O] [Nonempty O]
      (X Y : Fin 3 → O → ℝ)
      (hX : IsRowStochastic X) (hY : IsRowStochastic Y) :
      ∃ (p : Fin 3 → ℝ) (l : Fin 3 → O → ℝ),
        ((∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) ∧
        (∀ i b, 0 ≤ l i b ∧ l i b ≤ 1) ∧
        finiteDeficiency Y X ≤ ENNReal.ofReal
          ((finiteBayesRisk p l X).toReal - (finiteBayesRisk p l Y).toReal) := by
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
    let ZS : Set ((Fin 3 × Finset O) → ℝ) := stdSimplex ℝ (Fin 3 × Finset O)
    let f : (O → O → ℝ) → ((Fin 3 × Finset O) → ℝ) → ℝ :=
      fun K z => ∑ t, z t * ∑ b ∈ t.2, (channelOutput K (X t.1) b - Y t.1 b)
    have hKS (K) : K ∈ KS ↔ IsRowStochastic K := by
      simp only [KS, Set.mem_pi, Set.mem_univ, forall_true_left, stdSimplex,
        Set.mem_setOf_eq, IsRowStochastic]
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
      have hm (i : Fin 3) (c : O) :
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
    have az (K) (z u : (Fin 3 × Finset O) → ℝ) (a b : ℝ) :
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
      ⟨Pi.single (0, ∅) 1, single_mem_stdSimplex ℝ _⟩
    let p : Fin 3 → ℝ := fun i => ∑ E : Finset O, z (i, E)
    let g : Fin 3 → O → ℝ := fun i b => ∑ E : Finset O, if b ∈ E then z (i, E) else 0
    have hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 := by
      refine ⟨fun i => Finset.sum_nonneg fun E _ => hz.1 (i, E), ?_⟩
      simpa only [p, ← Fintype.sum_prod_type] using hz.2
    have hg (i b) : 0 ≤ g i b ∧ g i b ≤ p i := by
      constructor
      · exact Finset.sum_nonneg fun E _ => by split_ifs; exact hz.1 (i, E); exact le_rfl
      · apply Finset.sum_le_sum; intro E _
        split_ifs; exact le_rfl; exact hz.1 (i, E)
    let l : Fin 3 → O → ℝ := fun i b => if p i = 0 then 0 else g i b / p i
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
      have hevent (i : Fin 3) (q : O → ℝ) :
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
      have hcost (T : Fin 3 → O → ℝ) (N : O → O → ℝ) :
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
    have hTV (i : Fin 3) :
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
    refine ⟨p, l, hp, hl, ?_⟩
    apply (iInf_le _ (⟨K, (hKS K).mp hK⟩ : FiniteMarkovKernel O O)).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      uniformSimulationError Y X ⟨K, (hKS K).mp hK⟩ ≤ f d.1 z :=
        Finset.sup'_le _ _ (fun i _ => hTV i)
      _ ≤ finiteBayesCost p l X d.1 - finiteBayesCost p l Y e.1 := by
        rw [hpay]; linarith [hemin I]
      _ = _ := by rw [hd, he, ENNReal.toReal_ofReal hdn, ENNReal.toReal_ofReal hen]
  let O := Block (Fin 3)
  letI : Nonempty O := ⟨⟨{0}, by simp⟩⟩
  let I : FiniteMarkovKernel O O := ⟨fun a b => if a = b then 1 else 0,
    ⟨by intro a b; dsimp only; split_ifs <;> norm_num, by intro a; exact Fintype.sum_ite_eq a (fun _ => (1 : ℝ))⟩⟩
  have comp_stoch (X : Fin 3 → O → ℝ) (hX : IsRowStochastic X)
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
  have def_le_one (X Y : Fin 3 → O → ℝ)
      (hX : IsRowStochastic X) (hY : IsRowStochastic Y) :
      finiteDeficiency Y X ≤ 1 := by
    apply (iInf_le _ I).trans
    apply ENNReal.ofReal_le_one.mpr
    apply Finset.sup'_le
    intro i _
    exact total_variation_le_one _ _ ⟨hY.1 i, hY.2 i⟩
      ⟨(comp_stoch X hX I).1 i, (comp_stoch X hX I).2 i⟩
  have hW : IsRowStochastic (row w) :=
    ⟨by intro i B; dsimp only [row]; split_ifs; exact hw B; exact le_rfl, hwrow⟩
  have hV : IsRowStochastic (row v) :=
    ⟨by intro i B; dsimp only [row]; split_ifs; exact hv B; exact le_rfl, hvrow⟩
  have hfin (X Y : Fin 3 → O → ℝ) (hX : IsRowStochastic X)
      (hY : IsRowStochastic Y) : finiteDeficiency Y X ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num) (def_le_one X Y hX hY)
  have block_risk {D : Type} [Fintype D] [Nonempty D]
      (p : Fin 3 → ℝ) (l : Fin 3 → D → ℝ) :
      ∃ H : Finset (Fin 3) → ℝ,
        (∀ S, (∀ a, H S ≤ ∑ i ∈ S, p i * l i a) ∧
          ∃ a, H S = ∑ i ∈ S, p i * l i a) ∧
        ∀ u : O → ℝ, (∀ B, 0 ≤ u B) →
          finiteBayesRisk p l (row u) = ENNReal.ofReal (∑ B, u B * H B.1) := by
    have hm (S : Finset (Fin 3)) := Finset.exists_min_image Finset.univ
      (fun a : D => ∑ i ∈ S, p i * l i a) Finset.univ_nonempty
    choose m hm using hm
    let H : Finset (Fin 3) → ℝ := fun S => ∑ i ∈ S, p i * l i (m S)
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
  let B0 : O := ⟨{0}, by simp⟩
  let B1 : O := ⟨{1}, by simp⟩
  let B2 : O := ⟨{2}, by simp⟩
  let B01 : O := ⟨{0, 1}, by simp⟩
  let B02 : O := ⟨{0, 2}, by simp⟩
  let B12 : O := ⟨{1, 2}, by simp⟩
  let BT : O := ⟨Finset.univ, Finset.univ_nonempty⟩
  have hsum (f : O → ℝ) : (∑ B, f B) =
      f B0 + f B1 + f B2 + f B01 + f B02 + f B12 + f BT := by
    have hu : (Finset.univ : Finset O) = {B0, B1, B2, B01, B02, B12, BT} := by decide
    rw [hu]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have ne01 : (0 : Fin 3) ≠ 1 := by decide
  have ne02 : (0 : Fin 3) ≠ 2 := by decide
  have ne12 : (1 : Fin 3) ≠ 2 := by decide
  let δ₁ := pair v 0 1 - pair w 0 1
  let δ₂ := pair v 0 2 - pair w 0 2
  let δ₃ := pair v 1 2 - pair w 1 2
  let τ := v BT - w BT
  let ε := (finiteDeficiency (row v) (row w)).toReal
  let R := (1 / 2 : ℝ) * Finset.univ.sup' Finset.univ_nonempty
    (fun i => ∑ j ∈ Finset.univ.erase i, max (pair v i j - pair w i j) 0)
  have hε : 0 ≤ ε := ENNReal.toReal_nonneg
  have hp01 (u : O → ℝ) : pair u 0 1 = u B01 + u BT := by
    unfold pair
    rw [hsum]
    norm_num [B0, B1, B2, B01, B02, B12, BT, Fin.ext_iff]
  have hp02 (u : O → ℝ) : pair u 0 2 = u B02 + u BT := by
    unfold pair
    rw [hsum]
    norm_num [B0, B1, B2, B01, B02, B12, BT, Fin.ext_iff]
  have hp12 (u : O → ℝ) : pair u 1 2 = u B12 + u BT := by
    unfold pair
    rw [hsum]
    norm_num [B0, B1, B2, B01, B02, B12, BT, Fin.ext_iff]
  have risk_bound {D : Type} [Fintype D] [Nonempty D]
      (p : Fin 3 → ℝ) (l : Fin 3 → D → ℝ)
      (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
      (hl : ∀ i a, 0 ≤ l i a ∧ l i a ≤ 1) :
      (finiteBayesRisk p l (row w)).toReal -
        (finiteBayesRisk p l (row v)).toReal ≤ ε := by
    obtain ⟨H, hH, hr⟩ := block_risk p l
    have hfw : finiteBayesRisk p l (row w) ≠ ⊤ := by rw [hr w hw]; exact ENNReal.ofReal_ne_top
    have hfv : finiteBayesRisk p l (row v) ≠ ⊤ := by rw [hr v hv]; exact ENNReal.ofReal_ne_top
    have hd := hfin (row w) (row v) hW hV
    have h := (ENNReal.toReal_le_toReal hfw (ENNReal.add_ne_top.mpr ⟨hfv, hd⟩)).mpr
      (deficiency_risk_bound p l (row w) (row v) hp hW hV hl)
    rw [ENNReal.toReal_add hfv hd] at h
    exact sub_le_iff_le_add.mpr (by simpa only [ε, add_comm] using h)
  have lower₁ : -τ / 3 ≤ ε := by
    let p : Fin 3 → ℝ := fun _ => 1 / 3
    let l : Fin 3 → Fin 3 → ℝ := fun i a => if i.val = a.val then 1 else 0
    obtain ⟨H, hH, hr⟩ := block_risk p l
    have heval (S : Finset (Fin 3)) (r : ℝ) (a : Fin 3)
        (hu : (∑ i ∈ S, p i * l i a) ≤ r)
        (hd : ∀ a, r ≤ ∑ i ∈ S, p i * l i a) : H S = r := by
      obtain ⟨b, hb⟩ := (hH S).2
      exact le_antisymm (((hH S).1 a).trans hu) (by rw [hb]; exact hd b)
    have h0 : H {0} = 0 := heval _ _ 1 (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
    have h1 : H {1} = 0 := heval _ _ 0 (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
    have h2 : H {2} = 0 := heval _ _ 0 (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
    have h01 : H {0, 1} = 0 := heval _ _ 2 (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
    have h02 : H {0, 2} = 0 := heval _ _ 1 (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
    have h12 : H {1, 2} = 0 := heval _ _ 0 (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
    have hT : H Finset.univ = 1 / 3 := heval _ _ 0
      (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l, Fin.sum_univ_three])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l, Fin.sum_univ_three])
    have he (u : O → ℝ) (hu : ∀ B, 0 ≤ u B) :
        (finiteBayesRisk p l (row u)).toReal = u BT / 3 := by
      rw [hr u hu, hsum]
      change (ENNReal.ofReal (u B0 * H {0} + u B1 * H {1} + u B2 * H {2} +
        u B01 * H {0, 1} + u B02 * H {0, 2} + u B12 * H {1, 2} +
        u BT * H Finset.univ)).toReal = _
      rw [h0, h1, h2, h01, h02, h12, hT]
      simp only [mul_zero, zero_add]
      rw [ENNReal.toReal_ofReal (mul_nonneg (hu BT) (by norm_num))]
      ring
    have h := risk_bound p l ⟨by intro i; norm_num [p], by norm_num [p, Fin.sum_univ_three]⟩
      (by intro i a; dsimp [l]; split_ifs <;> norm_num)
    rw [he w hw, he v hv] at h
    dsimp only [τ]; linarith
  have lower₂ : τ / 2 - (δ₁ + δ₂ + δ₃) / 3 ≤ ε := by
    let p : Fin 3 → ℝ := fun _ => 1 / 3
    let l : Fin 3 → Fin 4 → ℝ := fun i a =>
      if a.val = 3 then 1 / 2 else if i.val = a.val then 0 else 1
    obtain ⟨H, hH, hr⟩ := block_risk p l
    have heval (S : Finset (Fin 3)) (r : ℝ) (a : Fin 4)
        (hu : (∑ i ∈ S, p i * l i a) ≤ r)
        (hd : ∀ a, r ≤ ∑ i ∈ S, p i * l i a) : H S = r := by
      obtain ⟨b, hb⟩ := (hH S).2
      exact le_antisymm (((hH S).1 a).trans hu) (by rw [hb]; exact hd b)
    have h0 : H {0} = 0 := heval _ _ 0 (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
    have h1 : H {1} = 0 := heval _ _ 1 (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
    have h2 : H {2} = 0 := heval _ _ 2 (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
    have h01 : H {0, 1} = 1 / 3 := heval _ _ 0 (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
    have h02 : H {0, 2} = 1 / 3 := heval _ _ 0 (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
    have h12 : H {1, 2} = 1 / 3 := heval _ _ 1 (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l])
    have hT : H Finset.univ = 1 / 2 := heval _ _ 3
      (by norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l, Fin.sum_univ_three])
      (by intro a; fin_cases a <;> norm_num [ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12, p, l, Fin.sum_univ_three])
    have he (u : O → ℝ) (hu : ∀ B, 0 ≤ u B) :
        (finiteBayesRisk p l (row u)).toReal =
          (u B01 + u B02 + u B12) / 3 + u BT / 2 := by
      rw [hr u hu, hsum]
      change (ENNReal.ofReal (u B0 * H {0} + u B1 * H {1} + u B2 * H {2} +
        u B01 * H {0, 1} + u B02 * H {0, 2} + u B12 * H {1, 2} +
        u BT * H Finset.univ)).toReal = _
      rw [h0, h1, h2, h01, h02, h12, hT]
      simp only [mul_zero, zero_add]
      rw [ENNReal.toReal_ofReal (by
        exact add_nonneg (add_nonneg (add_nonneg
          (mul_nonneg (hu B01) (by norm_num))
          (mul_nonneg (hu B02) (by norm_num)))
          (mul_nonneg (hu B12) (by norm_num)))
          (mul_nonneg (hu BT) (by norm_num))) ]
      ring
    have h := risk_bound p l ⟨by intro i; norm_num [p], by norm_num [p, Fin.sum_univ_three]⟩
      (by intro i a; dsimp [l]; split_ifs <;> norm_num)
    rw [he w hw, he v hv] at h
    dsimp only [τ, δ₁, δ₂, δ₃]
    rw [hp01, hp01, hp02, hp02, hp12, hp12]
    linarith
  have pair_symm (u : O → ℝ) (i j : Fin 3) : pair u i j = pair u j i := by
    simp only [pair, and_comm]
  have star_le (i : Fin 3) :
      (∑ j ∈ Finset.univ.erase i, max (pair v i j - pair w i j) 0) / 2 ≤ R := by
    have hi := Finset.le_sup'
      (fun i => ∑ j ∈ Finset.univ.erase i, max (pair v i j - pair w i j) 0)
      (Finset.mem_univ i)
    dsimp only [R]; linarith
  have rs0 : (max δ₁ 0 + max δ₂ 0) / 2 ≤ R := by
    have he := Finset.sum_erase_add Finset.univ
      (fun j => max (pair v 0 j - pair w 0 j) 0) (Finset.mem_univ (0 : Fin 3))
    norm_num only [Fin.sum_univ_three, add_zero] at he
    have hi := star_le 0
    dsimp only [δ₁, δ₂]; linarith
  have rs1 : (max δ₁ 0 + max δ₃ 0) / 2 ≤ R := by
    have he := Finset.sum_erase_add Finset.univ
      (fun j => max (pair v 1 j - pair w 1 j) 0) (Finset.mem_univ (1 : Fin 3))
    norm_num only [Fin.sum_univ_three, add_zero] at he
    rw [pair_symm v 1 0, pair_symm w 1 0] at he
    have hi := star_le 1
    dsimp only [δ₁, δ₃]; linarith
  have rs2 : (max δ₂ 0 + max δ₃ 0) / 2 ≤ R := by
    have he := Finset.sum_erase_add Finset.univ
      (fun j => max (pair v 2 j - pair w 2 j) 0) (Finset.mem_univ (2 : Fin 3))
    norm_num only [Fin.sum_univ_three, add_zero] at he
    rw [pair_symm v 2 0, pair_symm w 2 0, pair_symm v 2 1, pair_symm w 2 1] at he
    have hi := star_le 2
    dsimp only [δ₂, δ₃]; linarith
  have cap (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
      (ha' : a ≤ 1 / 2) (hb' : b ≤ 1 / 2) (hc' : c ≤ 1 / 2)
      (hs : a + b + c ≤ 1) : δ₁ * a + δ₂ * b + δ₃ * c ≤ R := by
    let p := max δ₁ 0
    let q := max δ₂ 0
    let r := max δ₃ 0
    have hp : 0 ≤ p := le_max_right _ _
    have hq : 0 ≤ q := le_max_right _ _
    have hr : 0 ≤ r := le_max_right _ _
    have hcmp : δ₁ * a + δ₂ * b + δ₃ * c ≤ p * a + q * b + r * c :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hb))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hc)
    apply hcmp.trans
    rcases le_total p q with hpq | hqp
    · rcases le_total p r with hpr | hrp
      · have h1 := mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hb')
        have h2 := mul_nonneg (sub_nonneg.mpr hpr) (sub_nonneg.mpr hc')
        have h3 := mul_nonneg hp (sub_nonneg.mpr hs)
        have hR : (q + r) / 2 ≤ R := rs2
        nlinarith only [h1, h2, h3, hR]
      · have h1 := mul_nonneg (sub_nonneg.mpr hrp) (sub_nonneg.mpr ha')
        have h2 := mul_nonneg (sub_nonneg.mpr (hrp.trans hpq)) (sub_nonneg.mpr hb')
        have h3 := mul_nonneg hr (sub_nonneg.mpr hs)
        have hR : (p + q) / 2 ≤ R := rs0
        nlinarith only [h1, h2, h3, hR]
    · rcases le_total q r with hqr | hrq
      · have h1 := mul_nonneg (sub_nonneg.mpr hqp) (sub_nonneg.mpr ha')
        have h2 := mul_nonneg (sub_nonneg.mpr hqr) (sub_nonneg.mpr hc')
        have h3 := mul_nonneg hq (sub_nonneg.mpr hs)
        have hR : (p + r) / 2 ≤ R := rs1
        nlinarith only [h1, h2, h3, hR]
      · have h1 := mul_nonneg (sub_nonneg.mpr (hrq.trans hqp)) (sub_nonneg.mpr ha')
        have h2 := mul_nonneg (sub_nonneg.mpr hrq) (sub_nonneg.mpr hb')
        have h3 := mul_nonneg hr (sub_nonneg.mpr hs)
        have hR : (p + q) / 2 ≤ R := rs0
        nlinarith only [h1, h2, h3, hR]
  have task {D : Type} [Fintype D] [Nonempty D]
      (p : Fin 3 → ℝ) (l : Fin 3 → D → ℝ)
      (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
      (hl : ∀ i d, 0 ≤ l i d ∧ l i d ≤ 1) :
      (finiteBayesRisk p l (row v)).toReal -
        (finiteBayesRisk p l (row w)).toReal ≤ R + 3 / 2 * ε := by
    obtain ⟨H, hH, hrisk⟩ := block_risk p l
    let center : Fin 3 → ℝ := fun i => H {i}
    let x : Fin 3 → D → ℝ := fun i d => p i * l i d - center i
    let N : Finset (Fin 3) → ℝ := fun S => H S - ∑ i ∈ S, center i
    have hHn (S) : 0 ≤ H S := by
      obtain ⟨d, hd⟩ := (hH S).2
      rw [hd]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (hl i d).1
    have hx (i d) : 0 ≤ x i d ∧ x i d ≤ p i := by
      have hlo : center i ≤ p i * l i d := by simpa [center] using (hH {i}).1 d
      have hcn : 0 ≤ center i := hHn {i}
      have hhi := mul_le_mul_of_nonneg_left (hl i d).2 (hp.1 i)
      dsimp only [x]; constructor <;> linarith
    have hxzero (i) : ∃ d, x i d = 0 := by
      obtain ⟨d, hd⟩ := (hH {i}).2
      refine ⟨d, ?_⟩
      simpa [x, center] using (sub_eq_zero.mpr hd.symm)
    have hN (S) : (∀ d, N S ≤ ∑ i ∈ S, x i d) ∧
        ∃ d, N S = ∑ i ∈ S, x i d := by
      constructor
      · intro d
        simpa only [N, x, Finset.sum_sub_distrib] using
          sub_le_sub_right ((hH S).1 d) (∑ i ∈ S, center i)
      · obtain ⟨d, hd⟩ := (hH S).2
        exact ⟨d, by simp only [N, x, Finset.sum_sub_distrib, hd]⟩
    have hNn (S) : 0 ≤ N S := by
      obtain ⟨d, hd⟩ := (hN S).2
      rw [hd]; exact Finset.sum_nonneg fun i _ => (hx i d).1
    have hpair (i j : Fin 3) (hij : i ≠ j) : N {i, j} ≤ p i ∧ N {i, j} ≤ p j := by
      constructor
      · obtain ⟨d, hd⟩ := hxzero j
        have hh := (hN {i, j}).1 d
        simpa [hij, hd] using hh.trans (by simpa [hij, hd] using (hx i d).2)
      · obtain ⟨d, hd⟩ := hxzero i
        have hh := (hN {i, j}).1 d
        simpa [hij, hd] using hh.trans (by simpa [hij, hd] using (hx j d).2)
    let a := N {0, 1}
    let b := N {0, 2}
    let c := N {1, 2}
    let h := N Finset.univ
    have ha : 0 ≤ a := hNn _
    have hb : 0 ≤ b := hNn _
    have hc : 0 ≤ c := hNn _
    have ha0 : a ≤ p 0 := (hpair 0 1 (by decide)).1
    have ha1 : a ≤ p 1 := (hpair 0 1 (by decide)).2
    have hb0 : b ≤ p 0 := (hpair 0 2 (by decide)).1
    have hb2 : b ≤ p 2 := (hpair 0 2 (by decide)).2
    have hc1 : c ≤ p 1 := (hpair 1 2 (by decide)).1
    have hc2 : c ≤ p 2 := (hpair 1 2 (by decide)).2
    have hpSum : p 0 + p 1 + p 2 = 1 := by simpa [Fin.sum_univ_three, add_assoc] using hp.2
    have hs : a + b + c ≤ 1 := by linarith only [ha0, hb2, hc1, hpSum]
    have ha' : a ≤ 1 / 2 := by linarith only [ha0, ha1, hpSum, hp.1 2]
    have hb' : b ≤ 1 / 2 := by linarith only [hb0, hb2, hpSum, hp.1 1]
    have hc' : c ≤ 1 / 2 := by linarith only [hc1, hc2, hpSum, hp.1 0]
    have hhlo : a + b + c ≤ 2 * h := by
      obtain ⟨d, hd⟩ := (hN Finset.univ).2
      have h01 : a ≤ x 0 d + x 1 d := by simpa [a] using (hN {0, 1}).1 d
      have h02 : b ≤ x 0 d + x 2 d := by simpa [b] using (hN {0, 2}).1 d
      have h12 : c ≤ x 1 d + x 2 d := by simpa [c] using (hN {1, 2}).1 d
      have hT : h = x 0 d + x 1 d + x 2 d := by
        simpa [h, Fin.sum_univ_three, add_assoc] using hd
      linarith only [h01, h02, h12, hT]
    have hh01 : h ≤ a + p 2 := by
      obtain ⟨d, hd⟩ := (hN {0, 1}).2
      have hT : h ≤ x 0 d + x 1 d + x 2 d := by
        simpa [h, Fin.sum_univ_three, add_assoc] using (hN Finset.univ).1 d
      have hd' : a = x 0 d + x 1 d := by simpa [a] using hd
      linarith only [hT, hd', (hx 2 d).2]
    have hh02 : h ≤ b + p 1 := by
      obtain ⟨d, hd⟩ := (hN {0, 2}).2
      have hT : h ≤ x 0 d + x 1 d + x 2 d := by
        simpa [h, Fin.sum_univ_three, add_assoc] using (hN Finset.univ).1 d
      have hd' : b = x 0 d + x 2 d := by simpa [b] using hd
      linarith only [hT, hd', (hx 1 d).2]
    have hh12 : h ≤ c + p 0 := by
      obtain ⟨d, hd⟩ := (hN {1, 2}).2
      have hT : h ≤ x 0 d + x 1 d + x 2 d := by
        simpa [h, Fin.sum_univ_three, add_assoc] using (hN Finset.univ).1 d
      have hd' : c = x 1 d + x 2 d := by simpa [c] using hd
      linarith only [hT, hd', (hx 0 d).2]
    have hr (u : O → ℝ) (hu : ∀ B, 0 ≤ u B) :
        (finiteBayesRisk p l (row u)).toReal = ∑ B, u B * H B.1 := by
      rw [hrisk u hu, ENNReal.toReal_ofReal]
      exact Finset.sum_nonneg fun B _ => mul_nonneg (hu B) (hHn B.1)
    have row0 (u : O → ℝ) (hu : ∀ i, ∑ B, row u i B = 1) :
        u B0 + u B01 + u B02 + u BT = 1 := by
      have ht := hu 0
      rw [hsum] at ht
      simpa [row, B0, B1, B2, B01, B02, B12, BT] using ht
    have row1 (u : O → ℝ) (hu : ∀ i, ∑ B, row u i B = 1) :
        u B1 + u B01 + u B12 + u BT = 1 := by
      have ht := hu 1
      rw [hsum] at ht
      simpa [row, B0, B1, B2, B01, B02, B12, BT] using ht
    have row2 (u : O → ℝ) (hu : ∀ i, ∑ B, row u i B = 1) :
        u B2 + u B02 + u B12 + u BT = 1 := by
      have ht := hu 2
      rw [hsum] at ht
      simpa [row, B0, B1, B2, B01, B02, B12, BT] using ht
    have gap : (finiteBayesRisk p l (row v)).toReal -
        (finiteBayesRisk p l (row w)).toReal =
          δ₁ * a + δ₂ * b + δ₃ * c - τ * (a + b + c - h) := by
      rw [hr v hv, hr w hw, hsum, hsum]
      dsimp only [δ₁, δ₂, δ₃]
      rw [hp01, hp01, hp02, hp02, hp12, hp12]
      dsimp only [a, b, c, h, N, center, τ]
      simp only [B0, B1, B2, B01, B02, B12, BT]
      simp only [Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide),
        Finset.sum_pair (show (0 : Fin 3) ≠ 2 by decide),
        Finset.sum_pair (show (1 : Fin 3) ≠ 2 by decide),
        Fin.sum_univ_three, add_zero]
      linear_combination (H {0}) * (row0 v hvrow - row0 w hwrow) +
        (H {1}) * (row1 v hvrow - row1 w hwrow) +
        (H {2}) * (row2 v hvrow - row2 w hwrow)
    rw [gap]
    by_cases hk : 0 ≤ a + b + c - h
    · have hkhi : a + b + c - h ≤ 1 / 2 := by linarith only [hhlo, hs]
      have hcap := cap a b c ha hb hc ha' hb' hc' hs
      have hτ := mul_le_mul_of_nonneg_right lower₁ hk
      have hkε := mul_le_mul_of_nonneg_right hkhi hε
      nlinarith only [hcap, hτ, hkε]
    · let q := h - (a + b + c)
      have hq : 0 ≤ q := by dsimp [q]; linarith only [hk]
      have hbudget : 3 * q + 2 * (a + b + c) ≤ 1 := by
        dsimp only [q]; linarith only [hh01, hh02, hh12, hpSum]
      have haq : a + q ≤ 1 / 2 := by
        dsimp only [q]; linarith only [hh02, hh12, hpSum, hb, hc, hp.1 2]
      have hbq : b + q ≤ 1 / 2 := by
        dsimp only [q]; linarith only [hh01, hh12, hpSum, ha, hc, hp.1 1]
      have hcq : c + q ≤ 1 / 2 := by
        dsimp only [q]; linarith only [hh01, hh02, hpSum, ha, hb, hp.1 0]
      have hqhi : q ≤ 1 / 3 := by linarith only [hbudget, ha, hb, hc]
      have hcap := cap (a + 2 * q / 3) (b + 2 * q / 3) (c + 2 * q / 3)
        (by positivity) (by positivity) (by positivity)
        (by linarith only [haq, hq]) (by linarith only [hbq, hq])
        (by linarith only [hcq, hq]) (by linarith only [hbudget, ha, hb, hc, hq])
      have ht := mul_le_mul_of_nonneg_left lower₂ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hq)
      calc
        δ₁ * a + δ₂ * b + δ₃ * c - τ * (a + b + c - h) =
            (δ₁ * (a + 2 * q / 3) + δ₂ * (b + 2 * q / 3) + δ₃ * (c + 2 * q / 3)) +
              2 * q * (τ / 2 - (δ₁ + δ₂ + δ₃) / 3) := by dsimp only [q]; ring
        _ ≤ R + 2 * q * ε := add_le_add hcap ht
        _ ≤ R + 3 / 2 * ε := by nlinarith only [mul_le_mul_of_nonneg_right hqhi hε, hε]
  obtain ⟨p, l, hp, hl, hd⟩ := dual (row v) (row w) hV hW
  have hbound := hd.trans (ENNReal.ofReal_le_ofReal (task p l hp hl))
  have hone := def_le_one (row v) (row w) hV hW
  change finiteDeficiency (row w) (row v) ≤ ENNReal.ofReal (min 1 (R + 3 / 2 * ε))
  rw [ENNReal.ofReal_min, ENNReal.ofReal_one]
  exact le_min hone hbound

end D5.S3.Estimation.DecisionRisk.CARSignedReverse
