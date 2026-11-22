/- GID: D5/S3/Quantum/PureState/BinaryRecordMemory
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/BinaryRecordMemory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: CPTP memory bounds for heterogeneous binary pure records with repeated-label endpoints. -/

import D5.S3.Quantum.PureState.PhaseRecordMemory
import D5.S3.Quantum.PureState.BinaryPureRecordDecoding

/-!
# Finite-memory decoding of binary pure records

The Walsh carrier specializes the phase-record bound. Isometric transport handles the
original product carrier, and aggregation of duplicate labels handles overlap-one pairs.
-/

namespace PhaseRecordMemory

noncomputable section

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open JointRecordDecoding
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Subentropy.GuessingProbability

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

/-- The all-true Walsh coordinate realizes the minimum of the product profile. -/
theorem coordinateWeight_min {k : ℕ} (s : Fin k → ℝ) (hs0 : ∀ i, 0 ≤ s i)
    (x : Word k) : coordinateWeight s (fun _ => true) ≤ coordinateWeight s x := by
  apply Finset.prod_le_prod₀
  · intro i _
    exact bitWeight_nonneg _ _
  · intro i _
    cases (x i)
    · simpa [bitWeight] using Real.sqrt_le_sqrt (show (1 - s i) / 2 ≤ (1 + s i) / 2 by
        linarith [hs0 i])
    · exact le_rfl

theorem coordinateWeight_pos {k : ℕ} (s : Fin k → ℝ) (hs0 : ∀ i, 0 ≤ s i)
    (hs1 : ∀ i, s i < 1) (x : Word k) : 0 < coordinateWeight s x := by
  apply Finset.prod_pos
  intro i _
  have hp : 0 < (1 + s i) / 2 := by linarith [hs0 i]
  have hm : 0 < (1 - s i) / 2 := by linarith [hs1 i]
  cases hx : x i
  · simpa only [bitWeight, hx, Bool.false_eq_true, ↓reduceIte] using Real.sqrt_pos.2 hp
  · simpa only [bitWeight, hx, ↓reduceIte] using Real.sqrt_pos.2 hm

/-- The exact product coefficient `S m` for coordinate-dependent binary overlaps. -/
theorem coordinateWeight_gap_coefficient {k : ℕ} (s : Fin k → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1) :
    (∑ x, coordinateWeight s x) * coordinateWeight s (fun _ => true) =
      ∏ i, (1 - s i + Real.sqrt (1 - (s i) ^ 2)) / 2 := by
  simp only [coordinateWeight, sum_words, sum_bool, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hplus : 0 ≤ (1 + s i) / 2 := by linarith [hs0 i]
  have hminus : 0 ≤ (1 - s i) / 2 := by linarith [hs1 i]
  have hrad : 0 ≤ 1 - (s i) ^ 2 := by nlinarith [hs0 i, hs1 i]
  have hprod : Real.sqrt ((1 + s i) / 2) * Real.sqrt ((1 - s i) / 2) =
      Real.sqrt (1 - (s i) ^ 2) / 2 := by
    rw [← Real.sqrt_mul hplus, ← show Real.sqrt (4 : ℝ) = 2 by norm_num,
      ← Real.sqrt_div hrad]
    congr 1
    ring
  simp only [bitWeight, Bool.false_eq_true, ↓reduceIte]
  nlinarith [Real.sq_sqrt hminus, hprod]

/-- The quantitative penalty for a Walsh word sent through any canonical CPTP encoder. -/
theorem coordinateRecord_success_le {k : ℕ} (s : Fin k → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1)
    (Φ : QuantumChannel (Word k) μ) (D : Word k → Matrix μ μ ℂ)
    (hD : ∀ j, (D j).PosSemidef) (hsD : ∑ j, D j = 1) :
    successProbability (uniformPrior (Word k)) (fun j => Φ.mapState (coordinateRecordState s hs0 hs1 j)) D ≤
      min ((Fintype.card μ : ℝ) / 2 ^ k)
        ((∏ i, (1 + Real.sqrt (1 - (s i) ^ 2)) / 2) -
          (1 - (Fintype.card μ : ℝ) / 2 ^ k) *
            (∏ i, (1 - s i + Real.sqrt (1 - (s i) ^ 2)) / 2)) := by
  have h := phase_success_le walsh (coordinateWeight s) walsh_norm
    (coordinateWeight_sq_sum hs0 hs1) (coordinateWeight s (fun _ => true))
    (coordinateWeight_nonneg s _) (coordinateWeight_min s hs0) Φ D hD hsD
  have hg := (pGuess_phase walsh (coordinateWeight s) walsh_norm walsh_orthogonal
    (coordinateWeight_nonneg s) (coordinateWeight_sq_sum hs0 hs1)).symm.trans
      (pGuess_coordinateRecord s hs0 hs1)
  rw [hg, coordinateWeight_gap_coefficient s hs0 hs1] at h
  change successProbability (uniformPrior (Word k))
    (fun j => Φ.mapState (coordinateRecordState s hs0 hs1 j)) D ≤ _ at h
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat] using h

theorem coordinateRecord_optimum_attainable_iff {k : ℕ} (s : Fin k → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i < 1) :
    (∃ Φ : QuantumChannel (Word k) μ,
      pGuess (uniformPrior (Word k)) (coordinateRecordState s hs0 (fun i => (hs1 i).le)) ∈
        successProbabilitySet (uniformPrior (Word k))
          (fun j => Φ.mapState (coordinateRecordState s hs0 (fun i => (hs1 i).le) j))) ↔
      2 ^ k ≤ Fintype.card μ := by
  have h := phase_optimum_attainable_iff (μ := μ) walsh (coordinateWeight s) walsh_norm
    walsh_orthogonal (coordinateWeight_sq_sum hs0 (fun i => (hs1 i).le))
    (coordinateWeight_pos s hs0 hs1)
  let ρ := coordinateRecordState s hs0 (fun i => (hs1 i).le)
  change (∃ Φ : QuantumChannel (Word k) μ, pGuess (uniformPrior (Word k)) ρ ∈
    successProbabilitySet (uniformPrior (Word k)) (fun j => Φ.mapState (ρ j))) ↔ _ at h
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using h

/-- The penalty applies to an encoder whose input is the original heterogeneous product
carrier, for all strict local overlap moduli. -/
theorem coordinateProductRecord_success_le {k : ℕ} {B : Fin k → Type*}
    [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (v : (i : Fin k) → Bool → B i → ℂ) (hv : ∀ i b, star (v i b) ⬝ᵥ v i b = 1)
    (s : Fin k → ℝ) (hs : ∀ i, s i = ‖star (v i false) ⬝ᵥ v i true‖)
    (hlt : ∀ i, s i < 1)
    (Φ : QuantumChannel ((i : Fin k) → B i) μ) (D : Word k → Matrix μ μ ℂ)
    (hD : ∀ j, (D j).PosSemidef) (hsD : ∑ j, D j = 1) :
    successProbability (uniformPrior (Word k))
      (fun j => Φ.mapState (coordinateProductRecordState v hv j)) D ≤
      min ((Fintype.card μ : ℝ) / 2 ^ k)
        ((∏ i, (1 + Real.sqrt (1 - (s i) ^ 2)) / 2) -
          (1 - (Fintype.card μ : ℝ) / 2 ^ k) *
            (∏ i, (1 - s i + Real.sqrt (1 - (s i) ^ 2)) / 2)) := by
  have heq : s = fun i => ‖star (v i false) ⬝ᵥ v i true‖ := funext hs
  subst s
  obtain ⟨T, hT, hstate⟩ := exists_coordinateRecord_isometry v hv hlt
  obtain ⟨Ω, hΩ⟩ := isometryChannel T hT
  have hmap (j : Word k) := state_eq_of_channelMatrix Ω _ _ ((hΩ _).trans (hstate j).symm)
  simpa only [QuantumChannel.comp_mapState, hmap] using
    coordinateRecord_success_le _ (fun _ => norm_nonneg _) (fun i => (hlt i).le)
      (Φ.comp Ω) D hD hsD

/-- The exact threshold is the dimension of the occupied word span, independent of
the dimensions of the original local carriers. -/
theorem coordinateProductRecord_optimum_attainable_iff {k : ℕ} {B : Fin k → Type*}
    [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (v : (i : Fin k) → Bool → B i → ℂ) (hv : ∀ i b, star (v i b) ⬝ᵥ v i b = 1)
    (hs : ∀ i, ‖star (v i false) ⬝ᵥ v i true‖ < 1) :
    (∃ Φ : QuantumChannel ((i : Fin k) → B i) μ,
      pGuess (uniformPrior (Word k)) (coordinateProductRecordState v hv) ∈
        successProbabilitySet (uniformPrior (Word k))
          (fun j => Φ.mapState (coordinateProductRecordState v hv j))) ↔
      2 ^ k ≤ Fintype.card μ := by
  let s : Fin k → ℝ := fun i => ‖star (v i false) ⬝ᵥ v i true‖
  let ρ := coordinateRecordState s (fun _ => norm_nonneg _) (fun i => (hs i).le)
  let σ := coordinateProductRecordState v hv
  obtain ⟨T, hT, hstate⟩ := exists_coordinateRecord_isometry v hv hs
  have hset := success_set_partialIsometry (uniformPrior (Word k)) ρ σ T
    (by rw [hT, Matrix.mul_one]) (fun _ => by rw [hT, one_mul]) hstate
  have hguess : pGuess (uniformPrior (Word k)) σ = pGuess (uniformPrior (Word k)) ρ :=
    congrArg sSup hset
  have hthreshold := coordinateRecord_optimum_attainable_iff (μ := μ) s
    (fun _ => norm_nonneg _) hs
  change (∃ Φ : QuantumChannel (Word k) μ,
    pGuess (uniformPrior (Word k)) ρ ∈ successProbabilitySet (uniformPrior (Word k))
      (fun j => Φ.mapState (ρ j))) ↔ _ at hthreshold
  constructor
  · rintro ⟨Φ, hΦ⟩
    obtain ⟨Ω, hΩ⟩ := isometryChannel T hT
    have hmap (j : Word k) : Ω.mapState (ρ j) = σ j :=
      state_eq_of_channelMatrix Ω _ _ ((hΩ _).trans (hstate j).symm)
    refine hthreshold.mp ⟨Φ.comp Ω, ?_⟩
    change pGuess (uniformPrior (Word k)) σ ∈ successProbabilitySet
      (uniformPrior (Word k)) (fun j => Φ.mapState (σ j)) at hΦ
    rw [hguess] at hΦ
    simpa only [QuantumChannel.comp_mapState, hmap] using hΦ
  · intro hdim
    obtain ⟨Φ, hΦ⟩ := hthreshold.mpr hdim
    obtain ⟨Ω, hΩ⟩ := isometryLeftInverse T hT
    have hmap (j : Word k) : Ω.mapState (σ j) = ρ j := by
      apply state_eq_of_channelMatrix
      rw [hstate j, hΩ]
    refine ⟨Φ.comp Ω, ?_⟩
    change pGuess (uniformPrior (Word k)) σ ∈ successProbabilitySet
      (uniformPrior (Word k)) (fun j => (Φ.comp Ω).mapState (σ j))
    simpa only [QuantumChannel.comp_mapState, hmap, hguess] using hΦ

section RepeatedLabels

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]

/-- For identical states along one component of a uniform label, aggregation of that
component's guesses gives every reduced success value, with the exact uniform factor. -/
theorem repeatedLabel_success_set (ρ : X → DensityState μ) :
    successProbabilitySet (uniformPrior (X × Y)) (fun j => ρ j.1) =
      (fun a : ℝ => (Fintype.card Y : ℝ)⁻¹ * a) ''
        successProbabilitySet (uniformPrior X) ρ := by
  classical
  have haggregate (D : X × Y → Matrix μ μ ℂ) :
      successProbability (uniformPrior (X × Y)) (fun j => ρ j.1) D =
        (Fintype.card Y : ℝ)⁻¹ *
          successProbability (uniformPrior X) ρ (fun x => ∑ y, D (x, y)) := by
    unfold successProbability uniformPrior
    rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, mul_inv]
    simp only [Matrix.sum_mul, trace_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  ext a
  constructor
  · rintro ⟨D, hD, hsD, rfl⟩
    let E := fun x : X => ∑ y : Y, D (x, y)
    refine ⟨successProbability (uniformPrior X) ρ E, ⟨E, ?_, ?_, rfl⟩, (haggregate D).symm⟩
    · exact fun x => Matrix.posSemidef_sum _ fun y _ => hD (x, y)
    · simpa only [E, Fintype.sum_prod_type] using hsD
  · rintro ⟨_, ⟨E, hE, hsE, rfl⟩, rfl⟩
    let y₀ := Classical.choice ‹Nonempty Y›
    let D : X × Y → Matrix μ μ ℂ := fun j => if j.2 = y₀ then E j.1 else 0
    have hsum (x : X) : (∑ y, D (x, y)) = E x := by simp [D]
    refine ⟨D, ?_, ?_, ?_⟩
    · intro j
      dsimp only [D]
      split_ifs
      · exact hE j.1
      · exact Matrix.PosSemidef.zero
    · rw [Fintype.sum_prod_type]
      simpa only [hsum] using hsE
    · rw [haggregate, show (fun x => ∑ y, D (x, y)) = E from funext hsum]

/-- Duplicating each label by a uniform repeated bit string preserves the memory dimension
required to attain the full optimum, with the optimum value scaled by the repeat factor. -/
theorem repeatedLabel_optimum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : X → DensityState ι) (g : ℝ)
    (hg : IsGreatest (successProbabilitySet (uniformPrior X) ρ) g) :
    IsGreatest (successProbabilitySet (uniformPrior (X × Y)) (fun j : X × Y => ρ j.1))
        ((Fintype.card Y : ℝ)⁻¹ * g) ∧
      ((∃ Φ : QuantumChannel ι μ, (Fintype.card Y : ℝ)⁻¹ * g ∈
          successProbabilitySet (uniformPrior (X × Y))
            (fun j : X × Y => Φ.mapState (ρ j.1))) ↔
        ∃ Φ : QuantumChannel ι μ, g ∈
          successProbabilitySet (uniformPrior X) (fun j => Φ.mapState (ρ j))) := by
  have hpos : 0 < (Fintype.card Y : ℝ)⁻¹ := by positivity
  have hmono : StrictMono (fun a : ℝ => (Fintype.card Y : ℝ)⁻¹ * a) := by
    intro a b hab
    exact mul_lt_mul_of_pos_left hab hpos
  constructor
  · rw [repeatedLabel_success_set]
    refine ⟨⟨g, hg.1, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hmono.monotone (hg.2 ha)
  · constructor
    · rintro ⟨Φ, hΦ⟩
      rw [repeatedLabel_success_set (Y := Y) (fun x => Φ.mapState (ρ x))] at hΦ
      obtain ⟨a, ha, he⟩ := hΦ
      exact ⟨Φ, hmono.injective he ▸ ha⟩
    · rintro ⟨Φ, hΦ⟩
      refine ⟨Φ, ?_⟩
      rw [repeatedLabel_success_set (Y := Y) (fun x => Φ.mapState (ρ x))]
      exact ⟨g, hΦ, rfl⟩

end RepeatedLabels

private theorem uniform_success_set_reindex {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (ρ : Y → DensityState μ) :
    successProbabilitySet (uniformPrior X) (fun x => ρ (e x)) =
      successProbabilitySet (uniformPrior Y) ρ := by
  have hp (D : Y → Matrix μ μ ℂ) :
      successProbability (uniformPrior X) (fun x => ρ (e x)) (fun x => D (e x)) =
        successProbability (uniformPrior Y) ρ D := by
    unfold successProbability uniformPrior
    rw [Fintype.card_congr e]
    exact e.sum_comp (fun y => (Fintype.card Y : ℝ)⁻¹ *
      (trace (D y * CStarMatrix.ofMatrix.symm (ρ y).1)).re)
  ext a
  constructor
  · rintro ⟨D, hD, hsD, rfl⟩
    let E := fun y => D (e.symm y)
    have h := hp E
    simp only [E, Equiv.symm_apply_apply] at h
    exact ⟨E, fun y => hD (e.symm y), (e.symm.sum_comp D).trans hsD, h⟩
  · rintro ⟨D, hD, hsD, rfl⟩
    exact ⟨fun x => D (e x), fun x => hD (e x), (e.sum_comp D).trans hsD, (hp D).symm⟩

/-- For arbitrary binary overlaps, each repeated coordinate contributes a uniform guessing
factor of one half and no memory dimension. Here `p` selects precisely the active pairs. -/
theorem activeProductRecord_optimum_and_memory {k : ℕ} {B : Fin k → Type*}
    [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (v : (i : Fin k) → Bool → B i → ℂ) (hv : ∀ i b, star (v i b) ⬝ᵥ v i b = 1)
    (s : Fin k → ℝ) (hs : ∀ i, s i = ‖star (v i false) ⬝ᵥ v i true‖)
    (p : Fin k → Prop) [DecidablePred p] (hp : ∀ i, p i ↔ s i < 1) :
    let r := Fintype.card {i // ¬ p i}
    let g := ((2 : ℝ) ^ r)⁻¹ * ∏ i : {i // p i}, (1 + Real.sqrt (1 - (s i) ^ 2)) / 2
    IsGreatest (successProbabilitySet (uniformPrior (Word k)) (coordinateProductRecordState v hv)) g ∧
      ((∃ Φ : QuantumChannel ((i : Fin k) → B i) μ,
        g ∈ successProbabilitySet (uniformPrior (Word k))
          (fun j => Φ.mapState (coordinateProductRecordState v hv j))) ↔
        2 ^ (k - r) ≤ Fintype.card μ) := by
  intro r g
  let a := Fintype.card {i // p i}
  have hcount : k - r = a := by
    have hcomp : r = k - a := by
      simpa only [r, a, Fintype.card_fin] using Fintype.card_subtype_compl p
    have hle : a ≤ k := by
      simpa only [a, Fintype.card_fin] using
        Fintype.card_le_of_embedding (Function.Embedding.subtype p)
    omega
  rw [hcount]
  obtain ⟨e, V, hV, hVstate⟩ := exists_activeRecord_isometry v hv s hs p hp
  let s' : Fin a → ℝ := fun i => s (e.symm i)
  have hs0 (i : Fin a) : 0 ≤ s' i := by
    dsimp only [s']
    rw [hs]
    exact norm_nonneg _
  have hs1 (i : Fin a) : s' i < 1 := (hp (e.symm i)).mp (e.symm i).property
  let ρ : Word a → DensityState (Word a) := coordinateRecordState s' hs0 (fun i => (hs1 i).le)
  let σ := coordinateProductRecordState v hv
  let Y := {i // ¬ p i} → Bool
  let labels : Word k ≃ Word a × Y := (Equiv.piEquivPiSubtypeProd p (fun _ => Bool)).trans
    (Equiv.prodCongr (Equiv.arrowCongr e (Equiv.refl Bool)) (Equiv.refl Y))
  have hlabel (j : Word k) (i : Fin a) : (labels j).1 i = j (e.symm i) := rfl
  have htransport (j : Word k) : CStarMatrix.ofMatrix.symm (σ j).1 =
      V * CStarMatrix.ofMatrix.symm (ρ (labels j).1).1 * Vᴴ := by
    change CStarMatrix.ofMatrix.symm (σ j).1 =
      V * rankOneDensity (coordinateRecordVector s' (labels j).1) * Vᴴ
    rw [show (labels j).1 = fun i => j (e.symm i) from funext (hlabel j)]
    exact hVstate j
  let g' := pGuess (uniformPrior (Word a)) ρ
  have hgreat : IsGreatest (successProbabilitySet (uniformPrior (Word a)) ρ) g' := by
    have h := isGreatest_phase walsh (coordinateWeight s') walsh_norm walsh_orthogonal
      (coordinateWeight_nonneg s') (coordinateWeight_sq_sum hs0 (fun i => (hs1 i).le))
    change IsGreatest (successProbabilitySet (uniformPrior (Word a)) ρ) _ at h
    change IsGreatest _ (sSup (successProbabilitySet (uniformPrior (Word a)) ρ))
    rw [h.csSup_eq]
    exact h
  have hval : (Fintype.card Y : ℝ)⁻¹ * g' = g := by
    dsimp only [g', g, ρ, Y]
    rw [pGuess_coordinateRecord]
    have hprod := Fintype.prod_equiv e (fun i => (1 + Real.sqrt (1 - (s i) ^ 2)) / 2)
      (fun i => (1 + Real.sqrt (1 - (s' i) ^ 2)) / 2) (fun i => by simp [s'])
    rw [← hprod]
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, r]
  have hrepeat := repeatedLabel_optimum (Y := Y) (μ := μ) ρ g' hgreat
  rw [hval] at hrepeat
  constructor
  · change IsGreatest (successProbabilitySet (uniformPrior (Word k)) σ) g
    rw [success_set_partialIsometry (uniformPrior (Word k)) (fun j => ρ (labels j).1) σ V
      (by rw [hV, Matrix.mul_one]) (fun _ => by rw [hV, one_mul]) htransport]
    exact (uniform_success_set_reindex labels (fun j => ρ j.1)).symm ▸ hrepeat.1
  · change (∃ Φ : QuantumChannel ((i : Fin k) → B i) μ,
      g ∈ successProbabilitySet (uniformPrior (Word k)) (fun j => Φ.mapState (σ j))) ↔ _
    rw [isometric_memory_attainment (uniformPrior (Word k)) _ σ V hV htransport g]
    have hrelabel (Φ : QuantumChannel (Word a) μ) :=
      uniform_success_set_reindex labels (fun j => Φ.mapState (ρ j.1))
    simp_rw [hrelabel]
    rw [hrepeat.2]
    exact coordinateRecord_optimum_attainable_iff s' hs0 hs1

end

end PhaseRecordMemory
