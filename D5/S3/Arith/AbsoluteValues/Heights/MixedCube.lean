/- GID: D5/S3/Arith/AbsoluteValues/Heights/MixedCube
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/MixedCube
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The mixed cube satisfies the central-slice volume bound. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.CubeSlicing
public import D5.S3.Arith.AbsoluteValues.Heights.MixedBall

public section

open MeasureTheory Measure Set ENNReal Pointwise
open scoped Real

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K] (κ : Type*) [Fintype κ]

/-- The partition of the standard real coordinates into the blocks of the sup-norm body: one
coordinate at a real place, two at a complex one. -/
@[expose] def mixedBlock : mixedIndex K κ →
    ({w : InfinitePlace K // IsReal w} × κ) ⊕ ({w : InfinitePlace K // IsComplex w} × κ) :=
  Sum.elim Sum.inl fun q ↦ Sum.inr (q.1, Sum.elim id id q.2)

variable {K κ}

omit [Fintype κ] in
/-- A block at a real place is a single coordinate. -/
def realBlockEquiv (w : {w : InfinitePlace K // IsReal w}) (j : κ) :
    {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨Sum.inl (w, j), rfl⟩
  left_inv := by
    rintro ⟨idx | idx, hidx⟩
    · refine Subtype.ext ?_
      simpa [mixedBlock] using hidx.symm
    · simp [mixedBlock] at hidx
  right_inv _ := rfl

omit [Fintype κ] in
/-- A block at a complex place is a pair of coordinates. -/
def complexBlockEquiv (w : {w : InfinitePlace K // IsComplex w}) (j : κ) :
    {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)} ≃ (Unit ⊕ Unit) where
  toFun a :=
    Sum.elim (fun _ ↦ Sum.inl ())
      (fun q ↦ Sum.elim (fun _ ↦ Sum.inl ()) (fun _ ↦ Sum.inr ()) q.2) a.1
  invFun := Sum.elim (fun _ ↦ ⟨Sum.inr (w, Sum.inl j), rfl⟩)
    fun _ ↦ ⟨Sum.inr (w, Sum.inr j), rfl⟩
  left_inv := by
    rintro ⟨idx | ⟨w', s | s⟩, hidx⟩
    · simp [mixedBlock] at hidx
    · refine Subtype.ext ?_
      simp only [mixedBlock, Sum.elim_inr, Sum.inr.injEq, Prod.mk.injEq, Sum.elim_inl,
        id_eq] at hidx
      simp [hidx.1, hidx.2]
    · refine Subtype.ext ?_
      simp only [mixedBlock, Sum.elim_inr, Sum.inr.injEq, Prod.mk.injEq, Sum.elim_inr,
        id_eq] at hidx
      simp [hidx.1, hidx.2]
  right_inv := by rintro (⟨⟩ | ⟨⟩) <;> rfl

variable (K κ)

open scoped Classical in
/-- The coordinate of a point of the euclidean tuple space at a real place. -/
@[expose] noncomputable def realCoord (w : {w : InfinitePlace K // IsReal w}) (j : κ) :
    mixedPi K κ →ₗ[ℝ] ℝ where
  toFun x := realPart K κ w x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
/-- The coordinate of a point of the euclidean tuple space at a complex place. -/
@[expose] noncomputable def complexCoord (w : {w : InfinitePlace K // IsComplex w}) (j : κ) :
    mixedPi K κ →ₗ[ℝ] ℂ where
  toFun x := complexPart K κ w x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
/-- **The convex body of Layer 5.4**: the product over the infinite places of the sup-norm unit
balls of the local coordinates, scaled to make each factor of volume one. -/
@[expose] def mixedCube : Set (mixedPi K κ) :=
  (⋂ (w : {w : InfinitePlace K // IsReal w}) (j : κ),
      realCoord K κ w j ⁻¹' Metric.closedBall 0 (ballRadius 1)) ∩
    ⋂ (w : {w : InfinitePlace K // IsComplex w}) (j : κ),
      complexCoord K κ w j ⁻¹' Metric.closedBall 0 (ballRadius 2)

variable {K κ}

open scoped Classical in
theorem preimage_mixedCube_mixedPiIsometry :
    (mixedPiIsometry K κ) ⁻¹' mixedCube K κ = prodBall (mixedBlock K κ) := by
  have hcardR (w : {w : InfinitePlace K // IsReal w}) (j : κ)
      [Fintype {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)}] :
      Fintype.card {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)} = 1 := by
    rw [Fintype.card_congr (realBlockEquiv w j), Fintype.card_punit]
  have hcardC (w : {w : InfinitePlace K // IsComplex w}) (j : κ)
      [Fintype {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)}] :
      Fintype.card {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)} = 2 := by
    rw [Fintype.card_congr (complexBlockEquiv w j)]
    simp
  have hsumR (w : {w : InfinitePlace K // IsReal w}) (j : κ)
      [Fintype {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)}]
      (f : mixedIndex K κ → ℝ) :
      ∑ idx : {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)}, f idx
        = f (Sum.inl (w, j)) := by
    rw [← Equiv.sum_comp (realBlockEquiv w j).symm
      (fun idx : {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)} ↦ f idx)]
    simp [realBlockEquiv]
  have hsumC (w : {w : InfinitePlace K // IsComplex w}) (j : κ)
      [Fintype {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)}]
      (f : mixedIndex K κ → ℝ) :
      ∑ idx : {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)}, f idx
        = f (Sum.inr (w, Sum.inl j)) + f (Sum.inr (w, Sum.inr j)) := by
    rw [← Equiv.sum_comp (complexBlockEquiv w j).symm
      (fun idx : {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)} ↦ f idx)]
    simp [complexBlockEquiv]
  ext c
  have hR : ∀ (w : {w : InfinitePlace K // IsReal w}) (j : κ),
      (|realCoord K κ w j (mixedPiIsometry K κ c)| ≤ ballRadius 1)
        ↔ (∑ idx : {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)},
              WithLp.ofLp c ↑idx ^ 2
            ≤ ballRadius (Fintype.card
                {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inl (w, j)}) ^ 2) := by
    intro w j
    rw [hcardR, hsumR w j (fun idx ↦ WithLp.ofLp c idx ^ 2),
      ← (show realCoord K κ w j (mixedPiIsometry K κ c) ^ 2 ≤ ballRadius 1 ^ 2 ↔
        |realCoord K κ w j (mixedPiIsometry K κ c)| ≤ ballRadius 1 from by
        rw [sq_le_sq, abs_of_nonneg ((fun (n : ℕ) =>
    (show 0 < ballRadius n from Real.rpow_pos_of_pos
      (ENNReal.toReal_pos
        (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
          (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne' measure_ball_lt_top.ne) _)) 1).le])]
    rfl
  have hC : ∀ (w : {w : InfinitePlace K // IsComplex w}) (j : κ),
      (‖complexCoord K κ w j (mixedPiIsometry K κ c)‖ ≤ ballRadius 2)
        ↔ (∑ idx : {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)},
              WithLp.ofLp c ↑idx ^ 2
            ≤ ballRadius (Fintype.card
                {idx : mixedIndex K κ // mixedBlock K κ idx = Sum.inr (w, j)}) ^ 2) := by
    intro w j
    rw [hcardC, hsumC w j (fun idx ↦ WithLp.ofLp c idx ^ 2),
      (show (WithLp.ofLp c (.inr (w, .inl j))) ^ 2 +
          (WithLp.ofLp c (.inr (w, .inr j))) ^ 2 =
          ‖(⟨WithLp.ofLp c (.inr (w, .inl j)),
            WithLp.ofLp c (.inr (w, .inr j))⟩ : ℂ)‖ ^ 2 from by
        rw [Complex.sq_norm, Complex.normSq_mk]
        ring), (show ‖(⟨WithLp.ofLp c (.inr (w, .inl j)),
            WithLp.ofLp c (.inr (w, .inr j))⟩ : ℂ)‖ ^ 2 ≤ ballRadius 2 ^ 2 ↔
          |‖(⟨WithLp.ofLp c (.inr (w, .inl j)),
            WithLp.ofLp c (.inr (w, .inr j))⟩ : ℂ)‖| ≤ ballRadius 2 from by
        rw [sq_le_sq, abs_of_nonneg ((fun (n : ℕ) =>
    (show 0 < ballRadius n from Real.rpow_pos_of_pos
      (ENNReal.toReal_pos
        (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
          (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne' measure_ball_lt_top.ne) _)) 2).le]), abs_norm]
    rfl
  rw [Set.mem_preimage, (show mixedPiIsometry K κ c ∈ mixedCube K κ ↔
      (∀ w j, |realCoord K κ w j (mixedPiIsometry K κ c)| ≤ ballRadius 1) ∧
        ∀ w j, ‖complexCoord K κ w j (mixedPiIsometry K κ c)‖ ≤ ballRadius 2 from by
      simp [mixedCube, Real.norm_eq_abs])]
  change _ ↔ ∀ k, _
  rw [Sum.forall]
  refine and_congr ?_ ?_
  · rw [Prod.forall]
    exact forall_congr' fun w ↦ forall_congr' fun j ↦ hR w j
  · rw [Prod.forall]
    exact forall_congr' fun w ↦ forall_congr' fun j ↦ hC w j

open scoped Classical in
omit [Fintype κ] in
theorem isBounded_mixedCube [Finite κ] : Bornology.IsBounded (mixedCube K κ) := by
  let _i : Fintype κ := Fintype.ofFinite κ
  have sq_norm_realPart (w : {w : InfinitePlace K // IsReal w}) (x : mixedPi K κ) :
      ‖realPart K κ w x‖ ^ 2 = ∑ j, realCoord K κ w j x ^ 2 := by
    rw [show realPart K κ w x = (WithLp.toLp 2
        (fun j : κ ↦ (((toMixedPi K κ).symm x) j).1 w) : EuclideanSpace ℝ κ) from rfl,
      EuclideanSpace.real_norm_sq_eq]
    rfl
  have sq_norm_complexPart (w : {w : InfinitePlace K // IsComplex w}) (x : mixedPi K κ) :
      ‖complexPart K κ w x‖ ^ 2 = ∑ j, ‖complexCoord K κ w j x‖ ^ 2 := by
    rw [show complexPart K κ w x = (WithLp.toLp 2
        (fun j : κ ↦ (((toMixedPi K κ).symm x) j).2 w) : EuclideanSpace ℂ κ) from rfl,
      EuclideanSpace.norm_sq_eq]
    simp only [PiLp.toLp_apply]
    rfl
  rw [Metric.isBounded_iff_subset_closedBall 0]
  set c : ℝ := max (ballRadius 1) (ballRadius 2) with hc
  have hc0 : 0 ≤ c := le_trans ((fun (n : ℕ) =>
    (show 0 < ballRadius n from Real.rpow_pos_of_pos
      (ENNReal.toReal_pos
        (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
          (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne' measure_ball_lt_top.ne) _)) 1).le (le_max_left _ _)
  set R : ℝ := Real.sqrt
    (((nrRealPlaces K + nrComplexPlaces K : ℕ) : ℝ) * Fintype.card κ * c ^ 2) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = ((nrRealPlaces K + nrComplexPlaces K : ℕ) : ℝ) * Fintype.card κ * c ^ 2 :=
    Real.sq_sqrt (by positivity)
  refine ⟨R, fun x hx ↦ ?_⟩
  rw [mem_closedBall_zero_iff, ← abs_norm, ← (show ‖x‖ ^ 2 ≤ R ^ 2 ↔ |‖x‖| ≤ R from by
    rw [sq_le_sq, abs_of_nonneg hR0])]
  rw [(show x ∈ mixedCube K κ ↔
      (∀ w j, |realCoord K κ w j (x)| ≤ ballRadius 1) ∧
        ∀ w j, ‖complexCoord K κ w j (x)‖ ≤ ballRadius 2 from by
      simp [mixedCube, Real.norm_eq_abs])] at hx
  have h1 : ∀ w, ‖realPart K κ w x‖ ^ 2 ≤ (Fintype.card κ : ℝ) * c ^ 2 := by
    intro w
    rw [sq_norm_realPart]
    calc ∑ j, realCoord K κ w j x ^ 2 ≤ ∑ _j : κ, c ^ 2 :=
          Finset.sum_le_sum fun j _ ↦ by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) ((hx.1 w j).trans (le_max_left _ _)) 2
      _ = (Fintype.card κ : ℝ) * c ^ 2 := by simp
  have h2 : ∀ w, ‖complexPart K κ w x‖ ^ 2 ≤ (Fintype.card κ : ℝ) * c ^ 2 := by
    intro w
    rw [sq_norm_complexPart]
    calc ∑ j, ‖complexCoord K κ w j x‖ ^ 2 ≤ ∑ _j : κ, c ^ 2 :=
          Finset.sum_le_sum fun j _ ↦
            pow_le_pow_left₀ (norm_nonneg _) ((hx.2 w j).trans (le_max_right _ _)) 2
      _ = (Fintype.card κ : ℝ) * c ^ 2 := by simp
  rw [hRsq, norm_sq_mixedPi]
  have e1 : ∑ w : {w : InfinitePlace K // IsReal w}, ‖realPart K κ w x‖ ^ 2
      ≤ (nrRealPlaces K : ℝ) * ((Fintype.card κ : ℝ) * c ^ 2) := by
    calc ∑ w : {w : InfinitePlace K // IsReal w}, ‖realPart K κ w x‖ ^ 2
        ≤ ∑ _w : {w : InfinitePlace K // IsReal w}, (Fintype.card κ : ℝ) * c ^ 2 :=
          Finset.sum_le_sum fun w _ ↦ h1 w
      _ = (nrRealPlaces K : ℝ) * ((Fintype.card κ : ℝ) * c ^ 2) := by
          simp [nrRealPlaces, mul_comm]
  have e2 : ∑ w : {w : InfinitePlace K // IsComplex w}, ‖complexPart K κ w x‖ ^ 2
      ≤ (nrComplexPlaces K : ℝ) * ((Fintype.card κ : ℝ) * c ^ 2) := by
    calc ∑ w : {w : InfinitePlace K // IsComplex w}, ‖complexPart K κ w x‖ ^ 2
        ≤ ∑ _w : {w : InfinitePlace K // IsComplex w}, (Fintype.card κ : ℝ) * c ^ 2 :=
          Finset.sum_le_sum fun w _ ↦ h2 w
      _ = (nrComplexPlaces K : ℝ) * ((Fintype.card κ : ℝ) * c ^ 2) := by
          simp [nrComplexPlaces, mul_comm]
  push_cast
  nlinarith [e1, e2]

open scoped Classical in
/-- **Bombieri–Gubler's Theorem C.3.8 for the body of Layer 5.4.** -/
theorem hasSliceBound_mixedCube :
    HasSliceBound (volume : Measure (mixedPi K κ)) gaussDensity (mixedCube K κ) := by
  have hmp : MeasurePreserving ((mixedPiIsometry K κ).symm) (volume : Measure (mixedPi K κ))
      (volume : Measure (EuclideanSpace ℝ (mixedIndex K κ))) :=
    LinearIsometryEquiv.measurePreserving _
  have h := HasSliceBound.of_measurePreserving (mixedPiIsometry K κ).symm.toLinearEquiv hmp
    (mixedPiIsometry K κ).continuous.measurable
    (show Measurable (gaussDensity : EuclideanSpace ℝ (mixedIndex K κ) → ℝ≥0∞) from by
      unfold gaussDensity
      fun_prop)
    ((open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal in (fun {ι κ : Type _} [Fintype ι] [DecidableEq κ] [Countable κ]
          (blk : ι → κ) => (show MeasurableSet (prodBall blk) from by
        rw [show prodBall blk = (WithLp.linearEquiv 2 ℝ (ι → ℝ)) ⁻¹' prodBallPi blk from rfl]
        exact (PiLp.volume_preserving_ofLp ι).measurable ((fun {ι κ : Type _} [instF : Fintype ι] [instD : DecidableEq κ]
            [instC : Countable κ] (blk : ι → κ) =>
          (show MeasurableSet (prodBallPi blk) from by
            have heq : prodBallPi blk = ⋂ k : κ, {x : ι → ℝ |
                ∑ j : {j : ι // blk j = k}, (x (Subtype.val j)) ^ 2
                  ≤ ballRadius (Fintype.card {j : ι // blk j = k}) ^ 2} := by
              ext x; simp [prodBallPi]
            rw [heq]
            exact MeasurableSet.iInter fun k => measurableSet_le (by fun_prop) measurable_const)) blk))))) (mixedBlock K κ)) (hasSliceBound_prodBall (mixedBlock K κ))
  have hdens : (fun x : mixedPi K κ ↦ gaussDensity ((mixedPiIsometry K κ).symm.toLinearEquiv x))
      = gaussDensity := by
    funext x
    rw [gaussDensity, gaussDensity,
      show ((mixedPiIsometry K κ).symm.toLinearEquiv) x = (mixedPiIsometry K κ).symm x from rfl,
      (mixedPiIsometry K κ).symm.norm_map]
  have hset : ((mixedPiIsometry K κ).symm.toLinearEquiv) ⁻¹' prodBall (mixedBlock K κ)
      = mixedCube K κ := by
    rw [← preimage_mixedCube_mixedPiIsometry, Set.preimage_preimage]
    simp
  rw [hdens, hset] at h
  exact h

open scoped Classical in
/-- **The slice bound of Layer 5.4**: every central slice of the body has volume at least one. -/
theorem one_le_volume_preimage_mixedCube (V : Submodule ℝ (mixedPi K κ)) :
    1 ≤ volume {y : V | (y : mixedPi K κ) ∈ mixedCube K κ} := by
  have hconv : Convex ℝ (mixedCube K κ) := by
    refine Convex.inter (convex_iInter fun w ↦ convex_iInter fun j ↦ ?_)
      (convex_iInter fun w ↦ convex_iInter fun j ↦ ?_)
    · exact (convex_closedBall _ _).linear_preimage (realCoord K κ w j)
    · exact (convex_closedBall _ _).linear_preimage (complexCoord K κ w j)
  have hneg {x : mixedPi K κ} (hx : x ∈ mixedCube K κ) : -x ∈ mixedCube K κ := by
    rw [(show x ∈ mixedCube K κ ↔
        (∀ w j, |realCoord K κ w j (x)| ≤ ballRadius 1) ∧
          ∀ w j, ‖complexCoord K κ w j (x)‖ ≤ ballRadius 2 from by
        simp [mixedCube, Real.norm_eq_abs])] at hx
    rw [(show -x ∈ mixedCube K κ ↔
        (∀ w j, |realCoord K κ w j (-x)| ≤ ballRadius 1) ∧
          ∀ w j, ‖complexCoord K κ w j (-x)‖ ≤ ballRadius 2 from by
        simp [mixedCube, Real.norm_eq_abs])]
    simpa using hx
  have hclosed : IsClosed (mixedCube K κ) := by
    let _i : Fintype κ := Fintype.ofFinite κ
    refine IsClosed.inter (isClosed_iInter fun w ↦ isClosed_iInter fun j ↦ ?_)
      (isClosed_iInter fun w ↦ isClosed_iInter fun j ↦ ?_)
    · exact Metric.isClosed_closedBall.preimage
        (realCoord K κ w j).continuous_of_finiteDimensional
    · exact Metric.isClosed_closedBall.preimage
        (complexCoord K κ w j).continuous_of_finiteDimensional
  exact one_le_volume_subtype_mem (E := mixedPi K κ) (Q := mixedCube K κ)
    hclosed.measurableSet hconv
    (fun _ hx ↦ hneg hx) hasSliceBound_mixedCube V

end NumberField.mixedEmbedding
