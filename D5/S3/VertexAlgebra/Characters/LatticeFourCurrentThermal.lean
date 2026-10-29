/- GID: D5/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeFourCurrentThermal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute original four-current thermal resummation on the open coordinate polydisk.
-/

import D5.S3.VertexAlgebra.Characters.LatticeFourCurrentTrace
import D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentThermal
import D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop
import D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
import D5.S3.Combinatorics.Partitions.AnalyticOddOccupation
import Mathlib.Data.Finsupp.Encodable

/-! The labeled countable matching source is absolutely summable before
complex rearrangement. Its exact bounded grade fibers recover the original
four-block trace, including every zero-coordinate face. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.LatticeFourCurrentThermal

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeAllStateField
open LatticeActualConformalState LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeThetaCharacter LatticeFourCurrentTrace
open LatticeTwoCurrentThermal
open CanonicalFullChargeLoop
open CanonicalOccupationSewing
open _root_.D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
open _root_.D5.S3.Combinatorics.Partitions.AnalyticOddOccupation

open private min4 max4 edgeParam chargeWeight matchingShift charge_cutoff_nat
  from D5.S3.VertexAlgebra.Characters.LatticeFourCurrentTrace
open private unpaired gradeShift matching_parameter_bounds sideMem
  from D5.S3.VertexAlgebra.Characters.LatticeFourCurrentTrace
open private arcMem edges_ordered
  from D5.S3.VertexAlgebra.Characters.LatticeFourCurrentTrace
open private original_four_zero_charge_trace
  from D5.S3.VertexAlgebra.Characters.LatticeFourCurrentTrace
open private markedTerm marked_summable marked_sum marked_row
  from D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentThermal
open private chargeSize bilinear_charge_bound charge_gaussian_moment
  from D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop

abbrev Four := Fin 4

private abbrev edgeData (M : PM4) := edgeParam M → (ℕ × Fin 2 × ℕ)

private def sourceGrade (D : LatticeData) (M : PM4) (β : Charge D) (t : ℕ)
    (v : edgeData M) (j : Four) : ℕ :=
  (chargeEnergy D β).toNat + t +
    matchingShift M (fun e => (v e).1 + 1)
      (fun e => (v e).2.1) (fun e => (v e).2.2) j

private def sourceFiber (D : LatticeData) (n : Four → ℕ) (M : PM4) :=
  {x : Charge D × (Occ D × edgeData M) //
      ∀ j, sourceGrade D M x.1 (oscillatorEnergy x.2.1) x.2.2 j = n j}

private abbrev sourceIndex (D : LatticeData) :=
  Σ M : PM4, Charge D × (Occ D × edgeData M)

private instance source_index_countable (D : LatticeData) : Countable (sourceIndex D) := by
  classical
  unfold sourceIndex edgeData
  infer_instance

private def sourceTerm (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (z : Four → ℂ)
    (x : sourceIndex D) : ℂ := by
  classical
  let M := x.1
  let β := x.2.1
  let d := x.2.2.1
  let v := x.2.2.2
  exact (∏ j : Four, z j ^ sourceGrade D M β (oscillatorEnergy d) v j) *
    (∏ j ∈ unpaired M, (bilinear D (unitCharge D (i j)) β : ℂ)) *
    ∏ e : edgeParam M, ((v e).1 + 1 : ℂ) *
      (D.G (i e.1.1) (i e.1.2) : ℂ)

private def sourceGradeMap (D : LatticeData) : sourceIndex D → Four → ℕ :=
  fun x => sourceGrade D x.1 x.2.1 (oscillatorEnergy x.2.2.1) x.2.2.2

private def sideProduct (z : Four → ℂ) (ε : Fin 2) (e : Four × Four) : ℂ :=
  ∏ j : Four, if sideMem ε e j then z j else 1

private theorem side_power_factor (z : Four → ℂ) (ε : Fin 2)
    (e : Four × Four) (ell k : ℕ) :
    (∏ j : Four, z j ^ (ell * (k + if sideMem ε e j then 1 else 0))) =
      (∏ j : Four, z j) ^ (ell * k) * sideProduct z ε e ^ ell := by
  classical
  calc
    _ = ∏ j : Four,
        (z j ^ (ell * k)) *
          (z j ^ (ell * if sideMem ε e j then 1 else 0)) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [← pow_add]
      congr 1
      rw [Nat.mul_add]
    _ = (∏ j : Four, z j ^ (ell * k)) *
        (∏ j : Four, z j ^ (ell * if sideMem ε e j then 1 else 0)) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ j : Four, z j) ^ (ell * k) * sideProduct z ε e ^ ell := by
      rw [← Finset.prod_pow]
      congr 1
      unfold sideProduct
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro j hj
      by_cases h : sideMem ε e j
      · simp [h, pow_mul]
      · simp [h]

private theorem source_power_factor (D : LatticeData) (M : PM4)
    (β : Charge D) (t : ℕ) (v : edgeData M) (z : Four → ℂ) :
    (∏ j : Four, z j ^ sourceGrade D M β t v j) =
      (∏ j : Four, z j) ^ (chargeEnergy D β).toNat *
        (∏ j : Four, z j) ^ t *
        ∏ e : edgeParam M,
          (∏ j : Four, z j) ^ ((v e).2.2 * ((v e).1 + 1)) *
            sideProduct z (v e).2.1 e.1 ^ ((v e).1 + 1) := by
  classical
  unfold sourceGrade matchingShift
  calc
    _ = (∏ j : Four, z j ^ (chargeEnergy D β).toNat) *
        (∏ j : Four, z j ^ t) *
        (∏ j : Four, z j ^
          ∑ e : edgeParam M,
            ((v e).1 + 1) * ((v e).2.2 +
              if sideMem (v e).2.1 e.1 j then 1 else 0)) := by
      simp_rw [pow_add]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = (∏ j : Four, z j) ^ (chargeEnergy D β).toNat *
        (∏ j : Four, z j) ^ t *
        (∏ j : Four, z j ^
          ∑ e : edgeParam M,
            ((v e).1 + 1) * ((v e).2.2 +
              if sideMem (v e).2.1 e.1 j then 1 else 0)) := by
      rw [← Finset.prod_pow, ← Finset.prod_pow]
    _ = (∏ j : Four, z j) ^ (chargeEnergy D β).toNat *
        (∏ j : Four, z j) ^ t *
        ∏ e : edgeParam M,
          (∏ j : Four, z j) ^ ((v e).2.2 * ((v e).1 + 1)) *
            sideProduct z (v e).2.1 e.1 ^ ((v e).1 + 1) := by
      congr 1
      calc
        (∏ j : Four, z j ^
            ∑ e : edgeParam M,
              ((v e).1 + 1) * ((v e).2.2 +
                if sideMem (v e).2.1 e.1 j then 1 else 0)) =
            ∏ j : Four, ∏ e : edgeParam M,
              z j ^ (((v e).1 + 1) * ((v e).2.2 +
                if sideMem (v e).2.1 e.1 j then 1 else 0)) := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [← Finset.prod_pow_eq_pow_sum]
        _ = ∏ e : edgeParam M, ∏ j : Four,
              z j ^ (((v e).1 + 1) * ((v e).2.2 +
                if sideMem (v e).2.1 e.1 j then 1 else 0)) := by
          rw [Finset.prod_comm]
        _ = _ := by
          apply Finset.prod_congr rfl
          intro e he
          simpa [Nat.mul_comm] using
            (side_power_factor z (v e).2.1 e.1 ((v e).1 + 1) (v e).2.2)

private theorem source_term_factor (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (z : Four → ℂ)
    (x : sourceIndex D) :
    sourceTerm D hD i z x =
      ((∏ j : Four, z j) ^ (chargeEnergy D x.2.1).toNat *
        (∏ j : Four, z j) ^ oscillatorEnergy x.2.2.1 *
        (∏ e : edgeParam x.1,
          markedTerm (∏ j : Four, z j) (sideProduct z (x.2.2.2 e).2.1 e.1)
            ((x.2.2.2 e).1, (x.2.2.2 e).2.2)) *
        (∏ j ∈ unpaired x.1,
          (bilinear D (unitCharge D (i j)) x.2.1 : ℂ)) *
        (∏ e : edgeParam x.1,
          (D.G (i e.1.1) (i e.1.2) : ℂ))) := by
  classical
  dsimp only [sourceTerm]
  rw [source_power_factor]
  simp only [markedTerm, Finset.prod_mul_distrib]
  ring

private theorem source_fiber_bounds (D : LatticeData) (n : Four → ℕ)
    (M : PM4) (x : sourceFiber D n M) :
    (chargeEnergy D (x.1 : Charge D × (Occ D × edgeData M)).1).toNat ≤ min4 n ∧
      oscillatorEnergy (x.1 : Charge D × (Occ D × edgeData M)).2.1 ≤ min4 n ∧
      ∀ e : edgeParam M,
        ((x.1 : Charge D × (Occ D × edgeData M)).2.2 e).1 + 1 ≤ max4 n ∧
          ((x.1 : Charge D × (Occ D × edgeData M)).2.2 e).2.2 ≤ min4 n := by
  have hb := matching_parameter_bounds n
    (chargeEnergy D (x.1 : Charge D × (Occ D × edgeData M)).1).toNat
    (oscillatorEnergy (x.1 : Charge D × (Occ D × edgeData M)).2.1) M
    (fun e => ((x.1 : Charge D × (Occ D × edgeData M)).2.2 e).1 + 1)
    (fun e => ((x.1 : Charge D × (Occ D × edgeData M)).2.2 e).2.1)
    (fun e => ((x.1 : Charge D × (Occ D × edgeData M)).2.2 e).2.2)
    (by intro e; omega)
    (by intro j; exact (x.2 j).symm)
  simpa [sourceGrade] using hb

private structure BoundedSourceData (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (n : Four → ℕ) (M : PM4) where
  beta : {β : Charge D // β ∈ positiveChargeCutoff D hD ((min4 n : ℕ) : ℤ)}
  ell : edgeParam M → Fin (max4 n + 1)
  side : edgeParam M → Fin 2
  winding : edgeParam M → Fin (min4 n + 1)
  t : Fin (min4 n + 1)
  grade : ∀ j : Four,
    n j = (chargeEnergy D beta.1).toNat + t.1 +
      gradeShift D n beta.1 M ell side winding j
  positive : ∀ e : edgeParam M, 0 < (ell e).1

private def source_fiber_equiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (n : Four → ℕ) (M : PM4) :
    sourceFiber D n M ≃
      Σ b : BoundedSourceData D hD n M, IntegerFiber D b.t.1 := by
  classical
  let toBounded : sourceFiber D n M → BoundedSourceData D hD n M := fun x => by
    have hb := source_fiber_bounds D n M x
    have hcut : x.1.1 ∈ positiveChargeCutoff D hD ((min4 n : ℕ) : ℤ) :=
      (charge_cutoff_nat D hD (min4 n) x.1.1).2 hb.1
    exact
      { beta := ⟨x.1.1, hcut⟩
        ell := fun e => ⟨(x.1.2.2 e).1 + 1, by
          have he := (hb.2.2 e).1
          omega⟩
        side := fun e => (x.1.2.2 e).2.1
        winding := fun e => ⟨(x.1.2.2 e).2.2, by
          have he := (hb.2.2 e).2
          omega⟩
        t := ⟨oscillatorEnergy x.1.2.1, by omega⟩
        grade := by
          intro j
          simpa [sourceGrade, gradeShift] using (x.2 j).symm
        positive := by intro e; simp }
  let fromBounded :
      (Σ b : BoundedSourceData D hD n M, IntegerFiber D b.t.1) →
        sourceFiber D n M := fun y => by
    let b := y.1
    let fib : IntegerFiber D b.t.1 := y.2
    let d : Occ D := fib.1
    have hd : oscillatorEnergy d = b.t.1 := fib.2
    refine ⟨(b.beta.1, (d, fun e =>
      ((b.ell e).1 - 1, (b.side e, (b.winding e).1)))), ?_⟩
    intro j
    have hell (e : edgeParam M) : (b.ell e).1 - 1 + 1 = (b.ell e).1 := by
      have he := b.positive e
      omega
    have hgrade := b.grade j
    have hgrade' : n j = (chargeEnergy D b.beta.1).toNat + b.t.1 +
        matchingShift M (fun e => (b.ell e).1) b.side
          (fun e => (b.winding e).1) j := by
      simpa [gradeShift] using hgrade
    change sourceGrade D M b.beta.1 (oscillatorEnergy d)
      (fun e => ((b.ell e).1 - 1, (b.side e, (b.winding e).1))) j = n j
    simp only [sourceGrade, hell, hd]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hgrade'.symm
  refine
    { toFun := fun x => ⟨toBounded x, ⟨x.1.2.1, rfl⟩⟩
      invFun := fromBounded
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    simp only [toBounded, fromBounded]
    congr 2
  · intro y
    cases y with
    | mk b fib =>
      cases b with
      | mk beta ell side winding t grade positive =>
        have he (e : edgeParam M) : (ell e).1 - 1 + 1 = (ell e).1 := by
          have hp := positive e
          omega
        have ht : oscillatorEnergy fib.1 = t.1 := fib.2
        simp [toBounded, fromBounded, he, ht]
        exact (Subtype.heq_iff_coe_eq (fun d => by simp only [ht])).2 rfl

private instance bounded_source_finite (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (n : Four → ℕ) (M : PM4) : Finite (BoundedSourceData D hD n M) := by
    let enc : BoundedSourceData D hD n M →
        {β : Charge D // β ∈ positiveChargeCutoff D hD ((min4 n : ℕ) : ℤ)} ×
          (edgeParam M → Fin (max4 n + 1)) ×
          (edgeParam M → Fin 2) ×
          (edgeParam M → Fin (min4 n + 1)) × Fin (min4 n + 1) :=
      fun b => (b.beta, b.ell, b.side, b.winding, b.t)
    apply Finite.of_injective enc
    intro a b hab
    have hβ : a.beta = b.beta := congrArg (fun z => z.1) hab
    have hℓ : a.ell = b.ell := congrArg (fun z => z.2.1) hab
    have hs : a.side = b.side := congrArg (fun z => z.2.2.1) hab
    have hw : a.winding = b.winding := congrArg (fun z => z.2.2.2.1) hab
    have ht : a.t = b.t := congrArg (fun z => z.2.2.2.2) hab
    cases a
    cases b
    cases hβ
    cases hℓ
    cases hs
    cases hw
    cases ht
    rfl
private theorem source_fiber_finite (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (n : Four → ℕ) (M : PM4) :
    Finite (sourceFiber D n M) := by
  letI : Finite (Σ b : BoundedSourceData D hD n M, IntegerFiber D b.t.1) := by
    infer_instance
  exact Finite.of_equiv _ (source_fiber_equiv D hD n M).symm

private abbrev RawBounded (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : Four → ℕ) (M : PM4) :=
  {β : Charge D // β ∈ positiveChargeCutoff D hD ((min4 n : ℕ) : ℤ)} ×
    (edgeParam M → Fin (max4 n + 1)) × (edgeParam M → Fin 2) ×
    (edgeParam M → Fin (min4 n + 1)) × Fin (min4 n + 1)

private def RawBounded.valid (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (n : Four → ℕ) (M : PM4) (b : RawBounded D hD n M) : Prop :=
  (∀ j : Four, n j = (chargeEnergy D b.1.1).toNat + b.2.2.2.2.1 +
    gradeShift D n b.1.1 M b.2.1 b.2.2.1 b.2.2.2.1 j) ∧
      ∀ e : edgeParam M, 0 < (b.2.1 e).1

private def boundedRawEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : Four → ℕ) (M : PM4) :
    BoundedSourceData D hD n M ≃
      {b : RawBounded D hD n M // RawBounded.valid D hD n M b} where
  toFun b := ⟨(b.beta, b.ell, b.side, b.winding, b.t), b.grade, b.positive⟩
  invFun b := ⟨b.1.1, b.1.2.1, b.1.2.2.1, b.1.2.2.2.1, b.1.2.2.2.2,
    b.2.1, b.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def sourceCoefficient (D : LatticeData) (i : Four → Fin D.rank)
    (M : PM4) (β : Charge D) (v : edgeData M) : ℂ :=
  (∏ j ∈ unpaired M, (bilinear D (unitCharge D (i j)) β : ℂ)) *
    ∏ e : edgeParam M, ((v e).1 + 1 : ℂ) * (D.G (i e.1.1) (i e.1.2) : ℂ)

private theorem matching_fiber_coefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (M : PM4) :
    (∑' x : sourceFiber D n M, sourceCoefficient D i M x.1.1 x.1.2.2) =
      ∑ β : {β : Charge D // β ∈ positiveChargeCutoff D hD ((min4 n : ℕ) : ℤ)},
        ∑ ell : edgeParam M → Fin (max4 n + 1),
        ∑ ε : edgeParam M → Fin 2,
        ∑ k : edgeParam M → Fin (min4 n + 1),
        ∑ t : Fin (min4 n + 1), chargeWeight D i n β.1 M ell ε k t := by
  classical
  rw [← (source_fiber_equiv D hD n M).symm.tsum_eq]
  letI := Fintype.ofFinite (BoundedSourceData D hD n M)
  have he (b : BoundedSourceData D hD n M) (d : IntegerFiber D b.t.1) :
      sourceCoefficient D i M ((source_fiber_equiv D hD n M).symm ⟨b, d⟩).1.1
        ((source_fiber_equiv D hD n M).symm ⟨b, d⟩).1.2.2 =
      (∏ j ∈ unpaired M, (bilinear D (unitCharge D (i j)) b.beta.1 : ℂ)) *
        ∏ e : edgeParam M, ((b.ell e).1 : ℂ) *
          (D.G (i e.1.1) (i e.1.2) : ℂ) := by
    dsimp [source_fiber_equiv, sourceCoefficient]
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    have hp := b.positive e
    have hh : (b.ell e).1 - 1 + 1 = (b.ell e).1 := by omega
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun a : ℕ => (a : ℂ) * (D.G (i e.1.1) (i e.1.2) : ℂ)) hh
  rw [tsum_fintype, Fintype.sum_sigma]
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  rw [← tsum_fintype (L := SummationFilter.unconditional (BoundedSourceData D hD n M)),
    ← (boundedRawEquiv D hD n M).symm.tsum_eq]
  let f : RawBounded D hD n M → ℂ := fun b =>
    (Nat.card (IntegerFiber D b.2.2.2.2.1) : ℂ) *
      ((∏ j ∈ unpaired M, (bilinear D (unitCharge D (i j)) b.1.1 : ℂ)) *
        ∏ e : edgeParam M, ((b.2.1 e).1 : ℂ) *
          (D.G (i e.1.1) (i e.1.2) : ℂ))
  change (∑' c : {b : RawBounded D hD n M // RawBounded.valid D hD n M b}, f c.1) = _
  trans ∑' b : RawBounded D hD n M,
    Set.indicator {b | RawBounded.valid D hD n M b} f b
  · exact tsum_subtype {b | RawBounded.valid D hD n M b} f
  rw [tsum_fintype]
  simp only [Set.indicator, Set.mem_setOf_eq, RawBounded.valid, f]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro β hβ
  apply Finset.sum_congr rfl
  intro ell hell
  apply Finset.sum_congr rfl
  intro ε hε
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro t ht
  simp only [chargeWeight]
  split_ifs <;> simp_all <;> ring

private theorem occupation_norm (D : LatticeData) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => ‖q ^ oscillatorEnergy d‖) := by
  have hs := summable_norm_signed_integer_occupations (Fin D.rank) hq
  simpa [signedIntegerMonomial, integerEnergy, oscillatorEnergy] using hs

private theorem ordinary_monomial (D : LatticeData) (q : ℂ) (d : Occ D) :
    monomial (fun a : Index D => q ^ (a.2 + 1)) d = q ^ oscillatorEnergy d := by
  classical
  unfold monomial Finsupp.prod
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [oscillatorEnergy, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => Nat.mul_comm _ _)

/-- The unsigned ordinary oscillator sum has the integer-frequency Euler product. -/
theorem ordinary_oscillator_hasProd (D : LatticeData) (q : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun m : ℕ => ((1 - q ^ (m + 1))⁻¹) ^ D.rank)
      (∑' d : Occ D, q ^ oscillatorEnergy d) := by
  let z : Index D → ℂ := fun a => q ^ (a.2 + 1)
  have hn : Summable (fun d : Occ D => ‖monomial z d‖) := by
    simpa only [z, ordinary_monomial] using occupation_norm D q hq
  have hz (a : Index D) : ‖z a‖ < 1 := by
    dsimp [z]
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hp := hasProd_inverse_eq_occupation_sum z hn hz
  have hswap : HasProd (fun p : ℕ × Fin D.rank => (1 - q ^ (p.1 + 1))⁻¹)
      (∑' d : Occ D, monomial z d) :=
    (Equiv.prodComm ℕ (Fin D.rank)).hasProd_iff.mpr hp
  have hg : HasProd (fun m : ℕ => ((1 - q ^ (m + 1))⁻¹) ^ D.rank)
      (∑' d : Occ D, monomial z d) := by
    apply hswap.prod_fiberwise
    intro m
    simpa using (hasProd_fintype (fun _ : Fin D.rank => (1 - q ^ (m + 1))⁻¹))
  simpa only [z, ordinary_monomial] using hg

private theorem norm_fin_product {A : Type*} {r : ℕ} (f : Fin r → A → ℂ)
    (hf : ∀ a, Summable (fun b => ‖f a b‖)) :
    Summable (fun v : Fin r → A => ‖∏ a, f a (v a)‖) := by
  induction r with
  | zero => exact Summable.of_finite
  | succ r ih =>
    have ht := ih (fun a => f a.succ) (fun a => hf a.succ)
    have hp := (hf 0).mul_norm ht
    exact (Fin.insertNthEquiv (fun _ : Fin (r + 1) => A) 0).summable_iff.mp
      (by simpa [Function.comp_def, Fin.prod_univ_succ, Fin.insertNth_zero] using hp)

private theorem norm_finite_product {A B : Type*} [Fintype B]
    (f : B → A → ℂ) (hf : ∀ b, Summable (fun a => ‖f b a‖)) :
    Summable (fun v : B → A => ‖∏ b, f b (v b)‖) := by
  let e := Fintype.equivFin B
  let E : (B → A) ≃ (Fin (Fintype.card B) → A) :=
    Equiv.piCongrLeft' (fun _ : B => A) e
  have hs := norm_fin_product (fun k => f (e.symm k)) (fun k => hf (e.symm k))
  have ht := hs.comp_injective E.injective
  apply ht.congr
  intro v
  change ‖∏ k, f (e.symm k) (v (e.symm k))‖ = ‖∏ b, f b (v b)‖
  rw [e.symm.prod_comp (fun b => f b (v b))]

private theorem product_norm_lt_one (z : Four → ℂ) (hz : ∀ j, ‖z j‖ < 1) :
    ‖∏ j : Four, z j‖ < 1 := by
  classical
  rw [norm_prod]
  have hle : (∏ j : Four, ‖z j‖) ≤ ∏ j ∈ ({0} : Finset Four), ‖z j‖ :=
    Finset.prod_le_prod_of_subset_of_le_one₀ (by simp)
      (fun j _ => norm_nonneg _) (fun j _ _ => (hz j).le)
  have hle' : (∏ j : Four, ‖z j‖) ≤ ‖z 0‖ := by simpa using hle
  exact hle'.trans_lt (hz 0)

private theorem side_product_norm_lt_one (M : PM4) (e : edgeParam M)
    (ε : Fin 2) (z : Four → ℂ) (hz : ∀ j, ‖z j‖ < 1) :
    ‖sideProduct z ε e.1‖ < 1 := by
  classical
  have hside : ∃ j : Four, sideMem ε e.1 j := by
    by_cases h : ε.1 = 0
    · refine ⟨e.1.2, ?_⟩
      simp [sideMem, h, arcMem, edges_ordered M e.1 e.2]
    · refine ⟨e.1.1, ?_⟩
      simp [sideMem, h, arcMem]
  obtain ⟨j, hj⟩ := hside
  unfold sideProduct
  rw [norm_prod]
  have hle : (∏ a : Four, ‖if sideMem ε e.1 a then z a else 1‖) ≤
      ∏ a ∈ ({j} : Finset Four), ‖if sideMem ε e.1 a then z a else 1‖ :=
    Finset.prod_le_prod_of_subset_of_le_one₀ (by simp)
      (fun a _ => norm_nonneg _) (by
        intro a _ _
        by_cases h : sideMem ε e.1 a
        · simpa only [if_pos h] using (hz a).le
        · simp only [if_neg h, norm_one, le_refl])
  have hle' : (∏ a : Four, ‖if sideMem ε e.1 a then z a else 1‖) ≤ ‖z j‖ := by
    simpa [hj] using hle
  exact hle'.trans_lt (hz j)

private theorem charge_norm (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (S : Finset Four) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun β : Charge D =>
      ‖q ^ (chargeEnergy D β).toNat *
        ∏ j ∈ S, (bilinear D (unitCharge D (i j)) β : ℂ)‖) := by
  classical
  let C : ℝ := ∏ j ∈ S, ∑ a : Fin D.rank, ‖(D.G (i j) a : ℂ)‖
  have hs := (charge_gaussian_moment D hD ‖q‖ (norm_nonneg _) hq S.card).mul_right C
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro β
  have hb : (∏ j ∈ S, ‖(bilinear D (unitCharge D (i j)) β : ℂ)‖) ≤
      ∏ j ∈ S, ((∑ a : Fin D.rank, ‖(D.G (i j) a : ℂ)‖) * chargeSize D β) :=
    Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => bilinear_charge_bound D β (i j))
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hb
  rw [norm_mul, norm_pow, norm_prod]
  have hh := mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg q)
    (chargeEnergy D β).toNat)
  simpa only [C, mul_assoc, mul_comm, mul_left_comm] using hh

private def edgeIndexEquiv : (ℕ × Fin 2 × ℕ) ≃ (Fin 2 × (ℕ × ℕ)) where
  toFun v := (v.2.1, (v.1, v.2.2))
  invFun v := (v.2.1, (v.1, v.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private def edgeTerm (D : LatticeData) (i : Four → Fin D.rank)
    (z : Four → ℂ) (M : PM4) (e : edgeParam M) (v : ℕ × Fin 2 × ℕ) : ℂ :=
  (D.G (i e.1.1) (i e.1.2) : ℂ) *
    markedTerm (∏ j : Four, z j) (sideProduct z v.2.1 e.1) (v.1, v.2.2)

private theorem edge_norm (D : LatticeData) (i : Four → Fin D.rank)
    (z : Four → ℂ) (hz : ∀ j, ‖z j‖ < 1) (M : PM4) (e : edgeParam M) :
    Summable (fun v : ℕ × Fin 2 × ℕ => ‖edgeTerm D i z M e v‖) := by
  let q := ∏ j : Four, z j
  let g : Fin 2 × (ℕ × ℕ) → ℂ := fun v =>
    (D.G (i e.1.1) (i e.1.2) : ℂ) * markedTerm q (sideProduct z v.1 e.1) v.2
  have hs : Summable (fun v => ‖g v‖) := by
    apply (summable_prod_of_nonneg (fun v => norm_nonneg (g v))).2
    refine ⟨?_, Summable.of_finite⟩
    intro ε
    have ht := (marked_summable q (sideProduct z ε e.1)
      (product_norm_lt_one z hz) (side_product_norm_lt_one M e ε z hz)).mul_left
      ‖(D.G (i e.1.1) (i e.1.2) : ℂ)‖
    simpa only [g, norm_mul] using ht
  change Summable (fun v => ‖g (edgeIndexEquiv v)‖)
  exact hs.comp_injective edgeIndexEquiv.injective

private theorem matching_source_norm (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (z : Four → ℂ) (hz : ∀ j, ‖z j‖ < 1) (M : PM4) :
    Summable (fun x : Charge D × (Occ D × edgeData M) =>
      ‖sourceTerm D hD i z ⟨M, x⟩‖) := by
  classical
  let q := ∏ j : Four, z j
  have hc := charge_norm D hD i (unpaired M) q (product_norm_lt_one z hz)
  have ho := occupation_norm D q (product_norm_lt_one z hz)
  have he := norm_finite_product (fun e : edgeParam M => edgeTerm D i z M e)
    (fun e => edge_norm D i z hz M e)
  have hs := hc.mul_norm (ho.mul_norm he)
  apply hs.congr
  rintro ⟨β, d, v⟩
  rw [source_term_factor]
  simp only [edgeTerm, Finset.prod_mul_distrib, q]
  congr 1
  ring

private theorem source_norm (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (z : Four → ℂ) (hz : ∀ j, ‖z j‖ < 1) :
    Summable (fun x : sourceIndex D => ‖sourceTerm D hD i z x‖) := by
  apply (summable_sigma_of_nonneg (fun x => norm_nonneg (sourceTerm D hD i z x))).2
  exact ⟨matching_source_norm D hD i z hz, Summable.of_finite⟩

private def gradeFiberEquiv (D : LatticeData) (n : Four → ℕ) :
    {x : sourceIndex D // sourceGradeMap D x = n} ≃
      Σ M : PM4, sourceFiber D n M where
  toFun x := ⟨x.1.1, ⟨x.1.2, fun j => congrFun x.2 j⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, funext x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem grade_fiber_sum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (z : Four → ℂ) (n : Four → ℕ) :
    (∑' x : {x : sourceIndex D // sourceGradeMap D x = n},
      sourceTerm D hD i z x.1) =
      (∏ j : Four, z j ^ n j) * actualFourCurrentCycleTrace D hD i n := by
  classical
  letI (M : PM4) : Finite (sourceFiber D n M) := source_fiber_finite D hD n M
  letI (M : PM4) : Fintype (sourceFiber D n M) := Fintype.ofFinite _
  have he (M : PM4) (x : sourceFiber D n M) :
      sourceTerm D hD i z ((gradeFiberEquiv D n).symm ⟨M, x⟩).1 =
        (∏ j : Four, z j ^ n j) * sourceCoefficient D i M x.1.1 x.1.2.2 := by
    dsimp [gradeFiberEquiv, sourceTerm, sourceCoefficient]
    have hpow : (∏ j : Four, z j ^
        sourceGrade D M x.1.1 (oscillatorEnergy x.1.2.1) x.1.2.2 j) =
        ∏ j : Four, z j ^ n j := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [x.2 j]
    rw [hpow]
    ring
  rw [← (gradeFiberEquiv D n).symm.tsum_eq, tsum_fintype, Fintype.sum_sigma]
  simp_rw [he]
  simp only [← Finset.mul_sum]
  rw [actual_four_current_grade_trace]
  congr 1
  have hfinite (M : PM4) := tsum_fintype
    (L := SummationFilter.unconditional (sourceFiber D n M))
    (fun x : sourceFiber D n M => sourceCoefficient D i M x.1.1 x.1.2.2)
  simp_rw [← hfinite]
  simp_rw [matching_fiber_coefficient D hD i n]
  unfold boundedFourCurrentCoefficient
  rw [Finset.sum_comm]
  exact (Finset.sum_subtype (positiveChargeCutoff D hD ((min4 n : ℕ) : ℤ))
    (fun _ => Iff.rfl) (fun β => ∑ M : PM4,
      ∑ ell : edgeParam M → Fin (max4 n + 1),
        ∑ ε : edgeParam M → Fin 2,
          ∑ k : edgeParam M → Fin (min4 n + 1),
            ∑ t : Fin (min4 n + 1), chargeWeight D i n β M ell ε k t)).symm

/-- Absolute summability of the original full-grade four-current thermal
family on every face of the open coordinate polydisk. -/
theorem original_four_current_thermal_normSummable (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (z : Four → ℂ) (hz : ∀ j, ‖z j‖ < 1) :
    Summable (fun n : Four → ℕ => ‖(∏ j : Four, z j ^ n j) *
      actualFourCurrentCycleTrace D hD i n‖) := by
  have hs := source_norm D hD i z hz
  have hg := hs.hasSum.tsum_fiberwise (sourceGradeMap D)
  apply hg.summable.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [← grade_fiber_sum D hD i z n]
  exact norm_tsum_le_tsum_norm (hs.subtype _)

private theorem original_source_hasSum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (z : Four → ℂ) (hz : ∀ j, ‖z j‖ < 1) :
    HasSum (fun n : Four → ℕ => (∏ j : Four, z j ^ n j) *
      actualFourCurrentCycleTrace D hD i n)
        (∑' x : sourceIndex D, sourceTerm D hD i z x) := by
  have hs := (source_norm D hD i z hz).of_norm.hasSum.tsum_fiberwise (sourceGradeMap D)
  exact hs.congr_fun (fun n => (grade_fiber_sum D hD i z n).symm)

private theorem sum_fin_product {A : Type*} {r : ℕ} (f : Fin r → A → ℂ)
    (b : Fin r → ℂ) (hn : ∀ a, Summable (fun v => ‖f a v‖))
    (hf : ∀ a, HasSum (f a) (b a)) :
    HasSum (fun v : Fin r → A => ∏ a, f a (v a)) (∏ a, b a) := by
  induction r with
  | zero => simpa using (hasSum_fintype (fun v : Fin 0 → A => ∏ a, f a (v a)))
  | succ r ih =>
    have hi := ih (fun a => f a.succ) (fun a => b a.succ)
      (fun a => hn a.succ) (fun a => hf a.succ)
    have hs := norm_fin_product (fun a => f a.succ) (fun a => hn a.succ)
    have hp := (hf 0).mul hi ((hn 0).mul_norm hs).of_norm
    exact (Fin.insertNthEquiv (fun _ : Fin (r + 1) => A) 0).hasSum_iff.mp
      (by simpa [Function.comp_def, Fin.prod_univ_succ, Fin.insertNth_zero] using hp)

private theorem sum_finite_product {A B : Type*} [Fintype B]
    (f : B → A → ℂ) (b : B → ℂ) (hn : ∀ a, Summable (fun v => ‖f a v‖))
    (hf : ∀ a, HasSum (f a) (b a)) :
    HasSum (fun v : B → A => ∏ a, f a (v a)) (∏ a, b a) := by
  let e := Fintype.equivFin B
  let E : (B → A) ≃ (Fin (Fintype.card B) → A) :=
    Equiv.piCongrLeft' (fun _ : B => A) e
  have hs := sum_fin_product (fun k => f (e.symm k)) (fun k => b (e.symm k))
    (fun k => hn (e.symm k)) (fun k => hf (e.symm k))
  have ht := E.hasSum_iff.mpr hs
  have hb : (∏ k, b (e.symm k)) = ∏ a, b a := e.symm.prod_comp b
  rw [hb] at ht
  apply ht.congr_fun
  intro v
  exact (e.symm.prod_comp (fun a => f a (v a))).symm

/-- The positive-frequency Lambert kernel of a labeled edge; both sides of
the edge use natural powers and are defined on zero-coordinate faces. -/
def edgeKernel (z : Four → ℂ) (e : Four × Four) : ℂ :=
  ∑' r : ℕ, (r + 1 : ℂ) *
    (sideProduct z 0 e ^ (r + 1) + sideProduct z 1 e ^ (r + 1)) /
      (1 - (∏ j : Four, z j) ^ (r + 1))

/-- The unpaired-current charge moment in the original charge coordinates. -/
def chargeMoment (D : LatticeData) (i : Four → Fin D.rank) (S : Finset Four) (q : ℂ) : ℂ :=
  ∑' β : Charge D, q ^ (chargeEnergy D β).toNat *
    ∏ j ∈ S, (bilinear D (unitCharge D (i j)) β : ℂ)

/-- The ordinary unsigned oscillator Euler product times the ten labeled matching
moments and edge kernels, with no occupation signs or edge symmetrization. -/
def thermalValue (D : LatticeData) (i : Four → Fin D.rank) (z : Four → ℂ) : ℂ :=
  let q := ∏ j : Four, z j
  (∏' m : ℕ, ((1 - q ^ (m + 1))⁻¹) ^ D.rank) *
    ∑ M : PM4, chargeMoment D i (unpaired M) q *
      ∏ e : edgeParam M, (D.G (i e.1.1) (i e.1.2) : ℂ) * edgeKernel z e.1

private theorem edge_hasSum (D : LatticeData) (i : Four → Fin D.rank)
    (z : Four → ℂ) (hz : ∀ j, ‖z j‖ < 1) (M : PM4) (e : edgeParam M) :
    HasSum (edgeTerm D i z M e)
      ((D.G (i e.1.1) (i e.1.2) : ℂ) * edgeKernel z e.1) := by
  let q := ∏ j : Four, z j
  let L (ε : Fin 2) := ∑' r : ℕ,
    (r + 1 : ℂ) * sideProduct z ε e.1 ^ (r + 1) / (1 - q ^ (r + 1))
  let g : Fin 2 × (ℕ × ℕ) → ℂ := fun v => markedTerm q (sideProduct z v.1 e.1) v.2
  have hn : Summable (fun v => ‖g v‖) :=
    (summable_prod_of_nonneg (fun v => norm_nonneg (g v))).2
      ⟨fun ε => marked_summable q (sideProduct z ε e.1)
        (product_norm_lt_one z hz) (side_product_norm_lt_one M e ε z hz),
        Summable.of_finite⟩
  have hrows := hn.of_norm.hasSum.prod_fiberwise (fun ε =>
    marked_sum q (sideProduct z ε e.1) (product_norm_lt_one z hz)
      (side_product_norm_lt_one M e ε z hz))
  have hv : (∑' v, g v) = edgeKernel z e.1 := by
    rw [← hrows.tsum_eq, tsum_fintype, Fin.sum_univ_two]
    have h0 := ((marked_summable q (sideProduct z 0 e.1) (product_norm_lt_one z hz)
      (side_product_norm_lt_one M e 0 z hz)).of_norm.prod).congr
        (fun r => (marked_row q (sideProduct z 0 e.1) (product_norm_lt_one z hz) r).tsum_eq)
    have h1 := ((marked_summable q (sideProduct z 1 e.1) (product_norm_lt_one z hz)
      (side_product_norm_lt_one M e 1 z hz)).of_norm.prod).congr
        (fun r => (marked_row q (sideProduct z 1 e.1) (product_norm_lt_one z hz) r).tsum_eq)
    dsimp [edgeKernel, q]
    rw [← h0.tsum_add h1]
    apply tsum_congr
    intro r
    ring
  have ht := hn.of_norm.hasSum
  rw [hv] at ht
  have hout := (edgeIndexEquiv.hasSum_iff.mpr ht).mul_left
    (D.G (i e.1.1) (i e.1.2) : ℂ)
  change HasSum (fun v =>
    (D.G (i e.1.1) (i e.1.2) : ℂ) * g (edgeIndexEquiv v)) _
  exact hout

private theorem matching_source_hasSum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (z : Four → ℂ) (hz : ∀ j, ‖z j‖ < 1) (M : PM4) :
    HasSum (fun x : Charge D × (Occ D × edgeData M) => sourceTerm D hD i z ⟨M, x⟩)
      (chargeMoment D i (unpaired M) (∏ j : Four, z j) *
        ((∑' d : Occ D, (∏ j : Four, z j) ^ oscillatorEnergy d) *
          ∏ e : edgeParam M,
            (D.G (i e.1.1) (i e.1.2) : ℂ) * edgeKernel z e.1)) := by
  classical
  let q := ∏ j : Four, z j
  have hc := charge_norm D hD i (unpaired M) q (product_norm_lt_one z hz)
  have ho := occupation_norm D q (product_norm_lt_one z hz)
  have he := norm_finite_product (fun e : edgeParam M => edgeTerm D i z M e)
    (fun e => edge_norm D i z hz M e)
  have hs := sum_finite_product (fun e : edgeParam M => edgeTerm D i z M e)
    (fun e => (D.G (i e.1.1) (i e.1.2) : ℂ) * edgeKernel z e.1)
    (fun e => edge_norm D i z hz M e) (fun e => edge_hasSum D i z hz M e)
  have ht := ho.of_norm.hasSum.mul hs (ho.mul_norm he).of_norm
  have hu := hc.of_norm.hasSum.mul ht (hc.mul_norm (ho.mul_norm he)).of_norm
  apply hu.congr_fun
  rintro ⟨β, d, v⟩
  rw [source_term_factor]
  simp only [edgeTerm, Finset.prod_mul_distrib, q]
  ring

private theorem source_total_value (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (z : Four → ℂ) (hz : ∀ j, ‖z j‖ < 1) :
    (∑' x : sourceIndex D, sourceTerm D hD i z x) = thermalValue D i z := by
  classical
  have hs := (source_norm D hD i z hz).of_norm.hasSum.sigma
    (fun M => matching_source_hasSum D hD i z hz M)
  rw [← hs.tsum_eq, tsum_fintype]
  dsimp [thermalValue]
  rw [(ordinary_oscillator_hasProd D (∏ j : Four, z j)
    (product_norm_lt_one z hz)).tprod_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M hM
  ring

/-- Exact absolute thermal resummation of the four original current blocks,
including every zero-coordinate face of the open four-polydisk. -/
theorem original_four_current_thermal_hasSum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (z : Four → ℂ) (hz : ∀ j, ‖z j‖ < 1) :
    HasSum (fun n : Four → ℕ => (∏ j : Four, z j ^ n j) *
      actualFourCurrentCycleTrace D hD i n) (thermalValue D i z) := by
  rw [← source_total_value D hD i z hz]
  exact original_source_hasSum D hD i z hz

/-- At the origin the actual four-current thermal value is zero. -/
theorem thermal_value_all_zero (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (i : Four → Fin D.rank) :
    thermalValue D i (fun _ => 0) = 0 := by
  classical
  have htrace : actualFourCurrentCycleTrace D hD i (fun _ => 0) = 0 := by
    rw [original_four_zero_charge_trace]
    apply Finset.sum_eq_zero
    intro β hβ
    have hQ := (charge_cutoff_nat D hD 0 β).1 hβ
    have hn := chargeEnergy_nonneg D hD β
    have hβ0 : β = 0 := (chargeEnergy_eq_zero_iff D hD β).1 (by omega)
    subst β
    simp [bilinear]
  have hz : ∀ n : Four → ℕ,
      (∏ j : Four, (0 : ℂ) ^ n j) * actualFourCurrentCycleTrace D hD i n = 0 := by
    intro n
    by_cases h : ∀ j, n j = 0
    · have hn : n = fun _ => 0 := funext h
      subst n
      simp only [htrace, mul_zero]
    · push_neg at h
      obtain ⟨j, hj⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (zero_pow hj), zero_mul]
  have hs := original_four_current_thermal_hasSum D hD i (fun _ => 0) (by intro j; norm_num)
  have hs0 : HasSum (fun n : Four → ℕ =>
      (∏ j : Four, (0 : ℂ) ^ n j) * actualFourCurrentCycleTrace D hD i n) 0 :=
    hasSum_zero.congr_fun hz
  exact hs.unique hs0

end D5.S3.VertexAlgebra.LatticeFourCurrentThermal
