/- GID: D5/S3/Arith/AbsoluteValues/Heights/ProductOfBalls
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/ProductOfBalls
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A product of Euclidean balls satisfies a slice bound. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.SliceBound

public section

open MeasureTheory Measure Set ENNReal
open scoped Real

/-- The Gauss density on `ι → ℝ` for the euclidean norm. -/
@[expose] noncomputable def gaussPi {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-π * ∑ i, (x i) ^ 2))

/-- The radius of the ball of volume one in `n` dimensions: Bombieri–Gubler's `ρ(n)`. -/
@[expose] noncomputable def ballRadius (n : ℕ) : ℝ := unitVolumeRadius (EuclideanSpace ℝ (Fin n))

/-- **The slice bound for a single block**: the ball of volume one in `α → ℝ`. -/
theorem hasSliceBound_ballPi (α : Type*) [Fintype α] :
    HasSliceBound (volume : Measure (α → ℝ)) gaussPi
      {y : α → ℝ | ∑ j, (y j) ^ 2 ≤ ballRadius (Fintype.card α) ^ 2} := by
  have h := HasSliceBound.of_measurePreserving (WithLp.linearEquiv 2 ℝ (α → ℝ)).symm
    (PiLp.volume_preserving_toLp α) (PiLp.volume_preserving_ofLp α).measurable
    (show Measurable (gaussDensity : EuclideanSpace ℝ α → ℝ≥0∞) from by
      unfold gaussDensity
      fun_prop) measurableSet_closedBall
    (hasSliceBound_unitVolumeBall (E := EuclideanSpace ℝ α))
  have hdens : (fun x : α → ℝ =>
      gaussDensity ((WithLp.linearEquiv 2 ℝ (α → ℝ)).symm x)) = gaussPi :=
    funext fun x => ((fun {ι : Type _} [instF : Fintype ι] (x : ι → ℝ) =>
    (show gaussPi x = gaussDensity (WithLp.toLp 2 x : EuclideanSpace ℝ ι) from by
      rw [gaussPi, gaussDensity, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp)) x).symm
  have hset : (WithLp.linearEquiv 2 ℝ (α → ℝ)).symm ⁻¹'
      Metric.closedBall (0 : EuclideanSpace ℝ α) (unitVolumeRadius (EuclideanSpace ℝ α))
      = {y : α → ℝ | ∑ j, (y j) ^ 2 ≤ ballRadius (Fintype.card α) ^ 2} := by
    ext y
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq,
      (fun (α : Type _) [Fintype α] => (show unitVolumeRadius (EuclideanSpace ℝ α) = ballRadius (Fintype.card α) from by
  rw [ballRadius, unitVolumeRadius, unitVolumeRadius,
    (fun {α β : Type _} [Fintype α] [Fintype β] (e : α ≃ β) => (show volume (Metric.ball (0 : EuclideanSpace ℝ α) 1)
      = volume (Metric.ball (0 : EuclideanSpace ℝ β) 1) from by
  let f : EuclideanSpace ℝ α ≃ₗᵢ[ℝ] EuclideanSpace ℝ β :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  have hpre : f ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ β) 1)
      = Metric.ball (0 : EuclideanSpace ℝ α) 1 := by
    ext x
    simp [Metric.mem_ball, dist_zero_right]
  rw [← hpre, f.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet])) (Fintype.equivFin α)]
  simp)),
      Real.sqrt_le_left ((fun (α : Type _) [Fintype α] => (show unitVolumeRadius (EuclideanSpace ℝ α) = ballRadius (Fintype.card α) from by
  rw [ballRadius, unitVolumeRadius, unitVolumeRadius,
    (fun {α β : Type _} [Fintype α] [Fintype β] (e : α ≃ β) => (show volume (Metric.ball (0 : EuclideanSpace ℝ α) 1)
      = volume (Metric.ball (0 : EuclideanSpace ℝ β) 1) from by
  let f : EuclideanSpace ℝ α ≃ₗᵢ[ℝ] EuclideanSpace ℝ β :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  have hpre : f ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ β) 1)
      = Metric.ball (0 : EuclideanSpace ℝ α) 1 := by
    ext x
    simp [Metric.mem_ball, dist_zero_right]
  rw [← hpre, f.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet])) (Fintype.equivFin α)]
  simp)) α ▸
        ((fun {E : Type _} [instN : NormedAddCommGroup E] [instI : InnerProductSpace ℝ E]
      [instM : MeasurableSpace E] [instB : BorelSpace E] [instF : FiniteDimensional ℝ E] =>
    (show 0 < unitVolumeRadius E from Real.rpow_pos_of_pos (ENNReal.toReal_pos
      (Metric.measure_ball_pos (volume : Measure E) (0 : E) one_pos).ne' measure_ball_lt_top.ne) _)) (E := EuclideanSpace ℝ α)).le)]
    simp
  rw [hdens, hset] at h
  exact h

/-- The product over the blocks of `blk` of the euclidean ball of volume one in that block's
coordinates: Bombieri–Gubler's `Q_N = B_{ρ(n₁)} × ⋯ × B_{ρ(n_r)}`. -/
@[expose] def prodBallPi {ι κ : Type*} [Fintype ι] [DecidableEq κ] (blk : ι → κ) :
    Set (ι → ℝ) :=
  {x | ∀ k : κ, ∑ j : {j : ι // blk j = k}, (x j) ^ 2
    ≤ ballRadius (Fintype.card {j : ι // blk j = k}) ^ 2}

/-- The product of balls of volume one, in `EuclideanSpace ℝ ι`. -/
@[expose] def prodBall {ι κ : Type*} [Fintype ι] [DecidableEq κ] (blk : ι → κ) :
    Set (EuclideanSpace ℝ ι) :=
  {x | ∀ k : κ, ∑ j : {j : ι // blk j = k}, (x j) ^ 2
    ≤ ballRadius (Fintype.card {j : ι // blk j = k}) ^ 2}


/-- **Bombieri–Gubler, Lemma C.3.7 on `EuclideanSpace ℝ ι`.** -/
theorem hasSliceBound_prodBall.{u} {ι : Type u} {κ : Type*}
    [Fintype ι] [DecidableEq κ] [Countable κ]
    (blk : ι → κ) :
    HasSliceBound (volume : Measure (EuclideanSpace ℝ ι)) gaussDensity (prodBall blk) := by
  have hPi : HasSliceBound (volume : Measure (ι → ℝ)) gaussPi (prodBallPi blk) := by
    have hAux (n : ℕ) :
        ∀ (α : Type u) [Fintype α] (blk : α → κ),
          Fintype.card α ≤ n →
          HasSliceBound (volume : Measure (α → ℝ)) gaussPi (prodBallPi blk) := by
      have hPLPi (α : Type u) [Fintype α] :
          HasPrekopaLeindler (volume : Measure (α → ℝ)) := by
        let f : EuclideanSpace ℝ α ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Fintype.card α)) :=
          LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin α)
        exact HasPrekopaLeindler.of_measurePreserving
          (WithLp.linearEquiv 2 ℝ (α → ℝ)).symm
          (PiLp.volume_preserving_toLp α) (PiLp.volume_preserving_ofLp α).measurable
          (HasPrekopaLeindler.of_measurePreserving f.toLinearEquiv f.measurePreserving
            f.symm.continuous.measurable (hasPrekopaLeindler_euclideanSpace _))
      have hempty : ∀ (α : Type u) [Fintype α] (blk : α → κ), IsEmpty α →
          HasSliceBound (volume : Measure (α → ℝ)) gaussPi (prodBallPi blk) := by
        intro α _ blk hα
        refine (fun {E : Type _} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
        {μ : Measure E} {g : E → ℝ≥0∞} (hg : ∀ x, g x ≤ 1) {Q : Set E} (hQ : ∀ x, x ∈ Q) => (show HasSliceBound μ g Q from by
      intro A _ _ _
      calc ∫⁻ x in A, g x ∂μ ≤ ∫⁻ _ in A, (1 : ℝ≥0∞) ∂μ := lintegral_mono fun x => hg x
        _ = μ A := setLIntegral_one A
        _ = μ (A ∩ Q) := by rw [Set.inter_eq_self_of_subset_left fun x _ => hQ x]))
          (E := α → ℝ) (g := gaussPi) (Q := prodBallPi blk) (fun x =>
        (show gaussPi x ≤ 1 from by
          rw [gaussPi, ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.exp_le_one_iff]
          have h : (0 : ℝ) ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
          nlinarith [Real.pi_pos])) fun x k => ?_
        have h : (Finset.univ : Finset {j : α // blk j = k}) = ∅ :=
          Finset.eq_empty_iff_forall_notMem.mpr fun j _ => hα.elim j.1
        change ∑ j : {j : α // blk j = k}, (x j) ^ 2 ≤ _
        rw [h, Finset.sum_empty]
        exact sq_nonneg _
      induction n with
      | zero =>
        intro α _ blk hcard
        exact hempty α blk (Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard))
      | succ n ih =>
        intro α _ blk hcard
        rcases isEmpty_or_nonempty α with hα | hα
        · exact hempty α blk hα
        obtain ⟨j₀⟩ := hα
        have hcards : 0 < Fintype.card {j : α // blk j = blk j₀} :=
          Fintype.card_pos_iff.mpr ⟨⟨j₀, rfl⟩⟩
        have hcardt : Fintype.card {j : α // ¬ (blk j = blk j₀)} ≤ n := by
          have h := Fintype.card_subtype_compl (fun j : α => blk j = blk j₀)
          omega
        let L : (α → ℝ) ≃ₗ[ℝ]
            (({j : α // blk j = blk j₀} → ℝ) × ({j : α // ¬ (blk j = blk j₀)} → ℝ)) :=
          { Equiv.piEquivPiSubtypeProd (fun j : α => blk j = blk j₀) (fun _ => ℝ) with
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        let blkt : {j : α // ¬ (blk j = blk j₀)} → κ := fun j => blk j.val
        have hMP : MeasurePreserving L (volume : Measure (α → ℝ))
            (volume : Measure ((({j : α // blk j = blk j₀}) → ℝ)
              × (({j : α // ¬ (blk j = blk j₀)}) → ℝ))) := by
          rw [Measure.volume_eq_prod]
          exact measurePreserving_piEquivPiSubtypeProd (fun _ : α => (volume : Measure ℝ))
            (fun j : α => blk j = blk j₀)
        have hsymm : Measurable L.symm :=
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : α => ℝ)
            (fun j : α => blk j = blk j₀)).symm.measurable
        have hprod : HasSliceBound (volume : Measure ((({j : α // blk j = blk j₀}) → ℝ)
            × (({j : α // ¬ (blk j = blk j₀)}) → ℝ)))
            (fun q => gaussPi q.1 * gaussPi q.2)
            ({y : {j : α // blk j = blk j₀} → ℝ |
                ∑ j, (y j) ^ 2 ≤ ballRadius (Fintype.card {j : α // blk j = blk j₀}) ^ 2}
              ×ˢ prodBallPi blkt) := by
          rw [Measure.volume_eq_prod]
          exact HasSliceBound.prod
            (show Measurable (gaussPi : ({j : α // blk j = blk j₀} → ℝ) → ℝ≥0∞) from by
              unfold gaussPi
              fun_prop)
            (show ∀ x : {j : α // blk j = blk j₀} → ℝ, gaussPi (-x) = gaussPi x from by
              intro x
              simp only [gaussPi, Pi.neg_apply, neg_sq])
            (show LogConcave (gaussPi : ({j : α // blk j = blk j₀} → ℝ) → ℝ≥0∞) from by
      intro a b ha hb hab x y
      have hkey : ∑ i, ((a • x + b • y) i) ^ 2 ≤ a * ∑ i, (x i) ^ 2 + b * ∑ i, (y i) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [sq_nonneg (x i - y i), mul_nonneg ha.le hb.le]
      rw [gaussPi, gaussPi, gaussPi, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
        ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [Real.pi_pos])
            (show Measurable (gaussPi : ({j : α // ¬ (blk j = blk j₀)} → ℝ) → ℝ≥0∞) from by
              unfold gaussPi
              fun_prop) ((fun {ι κ : Type _} [instF : Fintype ι] [instD : DecidableEq κ]
          [instC : Countable κ] (blk : ι → κ) =>
        (show MeasurableSet (prodBallPi blk) from by
          have heq : prodBallPi blk = ⋂ k : κ, {x : ι → ℝ |
              ∑ j : {j : ι // blk j = k}, (x (Subtype.val j)) ^ 2
                ≤ ballRadius (Fintype.card {j : ι // blk j = k}) ^ 2} := by
            ext x; simp [prodBallPi]
          rw [heq]
          exact MeasurableSet.iInter fun k => measurableSet_le (by fun_prop) measurable_const)) blkt) ((fun {ι κ : Type _} [Fintype ι] [DecidableEq κ] (blk : ι → κ) => (show Convex ℝ (prodBallPi blk) from by
      rw [(fun {ι κ : Type _} [instF : Fintype ι] [instD : DecidableEq κ] (blk : ι → κ) =>
        (show prodBallPi blk = ⋂ k : κ, {x : ι → ℝ |
            ∑ j : {j : ι // blk j = k}, (x (Subtype.val j)) ^ 2
              ≤ ballRadius (Fintype.card {j : ι // blk j = k}) ^ 2} from by
          ext x; simp [prodBallPi]))]
      exact convex_iInter fun k => (fun {ι S : Type _} [Fintype S] (f : S → ι) (c : ℝ) => (show Convex ℝ {x : ι → ℝ | ∑ j : S, (x (f j)) ^ 2 ≤ c} from by
      intro x hx y hy a b ha hb hab
      have hpt : ∑ j : S, ((a • x + b • y) (f j)) ^ 2
          ≤ a * ∑ j : S, (x (f j)) ^ 2 + b * ∑ j : S, (y (f j)) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ => ?_
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [sq_nonneg (x (f j) - y (f j)), mul_nonneg ha hb]
      calc ∑ j : S, ((a • x + b • y) (f j)) ^ 2
          ≤ a * ∑ j : S, (x (f j)) ^ 2 + b * ∑ j : S, (y (f j)) ^ 2 := hpt
        _ ≤ a * c + b * c := by gcongr <;> [exact hx; exact hy]
        _ = c := by rw [← add_mul, hab, one_mul])) _ _)) blkt)
            (fun _ hz => (fun {ι κ : Type _} [instF : Fintype ι] [instD : DecidableEq κ] (blk : ι → κ)
          {x : ι → ℝ} (hx : x ∈ prodBallPi blk) =>
        (show -x ∈ prodBallPi blk from by
          change ∀ k : κ, ∑ j : {j : ι // blk j = k}, ((-x) j) ^ 2
            ≤ ballRadius (Fintype.card {j : ι // blk j = k}) ^ 2
          intro k
          simpa only [Pi.neg_apply, neg_sq] using hx k)) blkt hz)
            (hPLPi _) (hPLPi _)
            (hasSliceBound_ballPi _) (ih _ blkt hcardt)
        have hdens : (fun x : α → ℝ => gaussPi (L x).1 * gaussPi (L x).2) = gaussPi := by
          funext x
          have h1 : ∑ j : {j : α // blk j = blk j₀}, ((L x).1 j) ^ 2
              = ∑ j : {j : α // blk j = blk j₀}, (x j.val) ^ 2 := rfl
          have h2 : ∑ j : {j : α // ¬ (blk j = blk j₀)}, ((L x).2 j) ^ 2
              = ∑ j : {j : α // ¬ (blk j = blk j₀)}, (x j.val) ^ 2 := rfl
          have hsum : ∑ i, (x i) ^ 2
              = (∑ j : {j : α // blk j = blk j₀}, (x j.val) ^ 2)
                + ∑ j : {j : α // ¬ (blk j = blk j₀)}, (x j.val) ^ 2 :=
            (Fintype.sum_subtype_add_sum_subtype _ _).symm
          rw [gaussPi, gaussPi, gaussPi, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            h1, h2, hsum]
          congr 2
          ring
        have hiff : ∀ (x : α → ℝ) (k : κ), k ≠ blk j₀ →
            ((∑ j : {j : {j : α // ¬ (blk j = blk j₀)} // blkt j = k}, (x j.1.1) ^ 2
                ≤ ballRadius (Fintype.card {j : {j : α // ¬ (blk j = blk j₀)} // blkt j = k}) ^ 2)
              ↔ (∑ j : {j : α // blk j = k}, (x j.1) ^ 2
                ≤ ballRadius (Fintype.card {j : α // blk j = k}) ^ 2)) := by
          intro x k hk
          let e : {j : {j : α // ¬ (blk j = blk j₀)} // blkt j = k} ≃ {j : α // blk j = k} :=
            { toFun := fun j => ⟨j.1.1, j.2⟩
              invFun := fun j => ⟨⟨j.1, fun hcon => hk (by rw [← j.2, hcon])⟩, j.2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          rw [Fintype.sum_equiv e (fun j => (x j.1.1) ^ 2) (fun j => (x j.1) ^ 2)
            (fun _ => rfl), Fintype.card_congr e]
        have hset : (L : (α → ℝ) → _) ⁻¹' ({y : {j : α // blk j = blk j₀} → ℝ |
              ∑ j, (y j) ^ 2 ≤ ballRadius (Fintype.card {j : α // blk j = blk j₀}) ^ 2}
            ×ˢ prodBallPi blkt) = prodBallPi blk := by
          ext x
          constructor
          · rintro ⟨h1, h2⟩ k
            by_cases hk : k = blk j₀
            · subst hk; exact h1
            · exact (hiff x k hk).mp (h2 k)
          · intro h
            exact ⟨h (blk j₀), fun k => by
              by_cases hk : k = blk j₀
              · subst hk
                have hz : (Finset.univ :
                    Finset {j : {j : α // ¬ (blk j = blk j₀)} // blkt j = blk j₀}) = ∅ :=
                  Finset.eq_empty_iff_forall_notMem.mpr fun j _ => j.1.2 j.2
                change ∑ j : {j : {j : α // ¬ (blk j = blk j₀)} // blkt j = blk j₀},
                  ((L x).2 j) ^ 2 ≤ _
                rw [hz, Finset.sum_empty]
                exact sq_nonneg _
              · exact (hiff x k hk).mpr (h k)⟩
        have hmeasg : Measurable (fun q : (({j : α // blk j = blk j₀}) → ℝ)
            × (({j : α // ¬ (blk j = blk j₀)}) → ℝ) => gaussPi q.1 * gaussPi q.2) :=
          ((show Measurable (gaussPi : ({j : α // blk j = blk j₀} → ℝ) → ℝ≥0∞) from by
            unfold gaussPi
            fun_prop).comp measurable_fst).mul
            ((show Measurable (gaussPi : ({j : α // ¬ (blk j = blk j₀)} → ℝ) → ℝ≥0∞) from by
              unfold gaussPi
              fun_prop).comp measurable_snd)
        have hfin := HasSliceBound.of_measurePreserving L hMP hsymm hmeasg
          (((fun {ι S : Type _} [instF : Fintype S] (f : S → ι) (c : ℝ) =>
        (show MeasurableSet {x : ι → ℝ | ∑ j : S, (x (f j)) ^ 2 ≤ c} from
          measurableSet_le (by fun_prop) measurable_const)) (fun j : {j : α // blk j = blk j₀} => j) _).prod
            ((fun {ι κ : Type _} [instF : Fintype ι] [instD : DecidableEq κ]
          [instC : Countable κ] (blk : ι → κ) =>
        (show MeasurableSet (prodBallPi blk) from by
          have heq : prodBallPi blk = ⋂ k : κ, {x : ι → ℝ |
              ∑ j : {j : ι // blk j = k}, (x (Subtype.val j)) ^ 2
                ≤ ballRadius (Fintype.card {j : ι // blk j = k}) ^ 2} := by
            ext x; simp [prodBallPi]
          rw [heq]
          exact MeasurableSet.iInter fun k => measurableSet_le (by fun_prop) measurable_const)) blkt)) hprod
        rw [hdens, hset] at hfin
        exact hfin
    exact hAux (Fintype.card ι) ι blk le_rfl
  have h := HasSliceBound.of_measurePreserving (WithLp.linearEquiv 2 ℝ (ι → ℝ))
    (PiLp.volume_preserving_ofLp ι) (PiLp.volume_preserving_toLp ι).measurable
    (show Measurable (gaussPi : (ι → ℝ) → ℝ≥0∞) from by
      unfold gaussPi
      fun_prop) ((fun {ι κ : Type _} [instF : Fintype ι] [instD : DecidableEq κ]
      [instC : Countable κ] (blk : ι → κ) =>
    (show MeasurableSet (prodBallPi blk) from by
      have heq : prodBallPi blk = ⋂ k : κ, {x : ι → ℝ |
          ∑ j : {j : ι // blk j = k}, (x (Subtype.val j)) ^ 2
            ≤ ballRadius (Fintype.card {j : ι // blk j = k}) ^ 2} := by
        ext x; simp [prodBallPi]
      rw [heq]
      exact MeasurableSet.iInter fun k => measurableSet_le (by fun_prop) measurable_const)) blk) hPi
  have hdens : (fun x : EuclideanSpace ℝ ι =>
      gaussPi ((WithLp.linearEquiv 2 ℝ (ι → ℝ)) x)) = gaussDensity := by
    funext x
    rw [(fun {ι : Type _} [instF : Fintype ι] (x : ι → ℝ) =>
    (show gaussPi x = gaussDensity (WithLp.toLp 2 x : EuclideanSpace ℝ ι) from by
      rw [gaussPi, gaussDensity, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp))]
    rfl
  have hset : (WithLp.linearEquiv 2 ℝ (ι → ℝ)) ⁻¹' prodBallPi blk = prodBall blk := rfl
  rw [hdens, hset] at h
  exact h
