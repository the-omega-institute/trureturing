/- GID: D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordinary thermal resummation of the original finite two-current traces. -/

import D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentTrace
import D5.S3.VertexAlgebra.Sewing.CanonicalFullChargeLoop

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.LatticeTwoCurrentThermal
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeAllStateField
open LatticeActualConformalState LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeThetaCharacter LatticeTwoCurrentTrace LatticeSectorIntertwiner
open CanonicalOccupationSewing CanonicalFullChargeLoop

open private sum_fullFiber from D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentTrace

/-- The ordinary occupation character, without an involution insertion. -/
def oscillatorCharacter (D : LatticeData) (q : ℂ) : ℂ :=
  ∑' d : Occ D, q ^ level D d

/-- The all-charge natural-energy theta series. -/
def chargeTheta (D : LatticeData) (q : ℂ) : ℂ :=
  ∑' β : Charge D, q ^ (chargeEnergy D β).toNat

/-- The charge second moment in the two specified current directions. -/
def chargeMoment (D : LatticeData) (i j : Fin D.rank) (q : ℂ) : ℂ :=
  ∑' β : Charge D, (bilinear D (unitCharge D i) β : ℂ) *
    (bilinear D (unitCharge D j) β : ℂ) * q ^ (chargeEnergy D β).toNat

private theorem actual_block (D : LatticeData) (i : Fin D.rank) (n m : ℕ) :
    energyBlock D 0 (MvPolynomial.X (i,0)) 0 n m = actualCurrentBlock D i n m := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  simp [energyBlock, actualCurrentBlock, inclusion, currentState]

private theorem actual_trace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (n m : ℕ) :
    blockTrace D 0 (MvPolynomial.X (i,0)) (MvPolynomial.X (j,0)) 0 0 n m =
      actualCurrentCycleTrace D hD i j n m := by
  simp only [blockTrace, neg_zero, actual_block, actualCurrentCycleTrace]

private theorem trace_norm_summable (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (q1 q2 : ℂ) (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) :
    Summable (fun nm : ℕ × ℕ =>
      ‖q1^nm.1*q2^nm.2*actualCurrentCycleTrace D hD i j nm.1 nm.2‖) := by
  simpa only [actual_trace D hD] using
    (full_charge_loop_trace D hD 0 (MvPolynomial.X (i,0)) (MvPolynomial.X (j,0))
      0 0 q1 q2 hq1 hq2).1

private theorem canonical_current_zero (D : LatticeData) (i : Fin D.rank)
    (β : Charge D) (p : Oscillator D) :
    canonical D 0 β (MvPolynomial.X (i,0)) 0 p =
      (bilinear D (unitCharge D i) β : ℂ) • p := by
  change (((Y D (currentState D i))[[0]]) (Finsupp.single β p)) (0 + β) = _
  rw [current_state_field, neutralField_ncoeff, neutralMode_single]
  simp [neutralPolynomialMode]

private theorem canonical_vacuum (D : LatticeData) (β : Charge D)
    (p : Oscillator D) : canonical D 0 β 1 (-1) p = p := by
  change (((Y D (vacuum D))[[-1]]) (Finsupp.single β p)) (0 + β) = _
  rw [stateField_vacuum, identity_modes]
  simp

private theorem scalar_summable (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (q1 q2 : ℂ) (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) :
    Summable (fun β : Charge D => ‖(q1*q2)^(chargeEnergy D β).toNat‖) ∧
    Summable (fun β : Charge D =>
      ‖(bilinear D (unitCharge D i) β : ℂ) *
        (bilinear D (unitCharge D j) β : ℂ) * (q1*q2)^(chargeEnergy D β).toNat‖) ∧
    Summable (fun d : Occ D => ‖(q1*q2)^level D d‖) := by
  have hi : Function.Injective (fun β : Charge D =>
      (β, (0,0)) : Charge D → Charge D × (Occ D × Occ D)) := by
    intro a b h
    exact congrArg Prod.fst h
  have hv := (full_charge_loop_summable D hD 0 1 1 (-1) (-1)
    q1 q2 hq1 hq2).comp_injective hi
  have hc := (full_charge_loop_summable D hD 0 (MvPolynomial.X (i,0))
    (MvPolynomial.X (j,0)) 0 0 q1 q2 hq1 hq2).comp_injective hi
  have hq : ‖q1*q2‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hq2.le (norm_nonneg q1)).trans_lt (by simpa using hq1)
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.comp_def, loopTerm, level, b, energy,
      canonical_vacuum, mul_pow] using hv
  · simpa [Function.comp_def, loopTerm, level, b, energy,
      canonical_current_zero, MvPolynomial.coeff_smul, smul_eq_mul,
      mul_pow, mul_comm, mul_left_comm, mul_assoc] using hc
  · have hs := D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.
      summable_norm_signed_integer_occupations (Fin D.rank) hq
    simpa [D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.signedIntegerMonomial,
      D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.integerEnergy,
      level, oscillatorEnergy] using hs

private def markedTerm (q x : ℂ) (rk : ℕ × ℕ) : ℂ :=
  (rk.1+1 : ℂ) * x^(rk.1+1) * q^(rk.2*(rk.1+1))

private theorem marked_summable (q x : ℂ) (hq : ‖q‖ < 1) (hx : ‖x‖ < 1) :
    Summable (fun rk : ℕ × ℕ => ‖markedTerm q x rk‖) := by
  have hs : Summable (fun r : ℕ => ‖(r+1 : ℂ)*x^(r+1)‖) := by
    simpa only [pow_one, Function.comp_def] using
      (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hx).comp_injective Nat.succ_injective
  have ht := summable_norm_geometric_of_norm_lt_one hq
  have hp := hs.mul_of_nonneg ht (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine hp.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  rintro ⟨r,k⟩
  rw [markedTerm, norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [norm_pow]
  apply pow_le_pow_of_le_one (norm_nonneg _) hq.le
  exact Nat.le_mul_of_pos_right k (by omega)

private theorem marked_sum (q x : ℂ) (hq : ‖q‖ < 1) (hx : ‖x‖ < 1) :
    HasSum (markedTerm q x)
      (∑' r : ℕ, (r+1 : ℂ)*x^(r+1)/(1-q^(r+1))) := by
  have hs := (marked_summable q x hq hx).of_norm
  have he (r : ℕ) : (∑' k : ℕ, markedTerm q x (r,k)) =
      (r+1 : ℂ)*x^(r+1)/(1-q^(r+1)) := by
    have hqr : ‖q^(r+1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    have ht (k : ℕ) : markedTerm q x (r,k) =
        (r+1 : ℂ)*x^(r+1)*(q^(r+1))^k := by
      simp only [markedTerm, Nat.mul_comm k (r+1), pow_mul]
    simp_rw [ht]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hqr]
    rfl
  simpa only [hs.tsum_prod, he] using hs.hasSum.prod_fiberwise
    (fun r => (hs.prod_factor r).hasSum)

/-- Exact residual-energy fiber for the charge-dependent marked cutoff. -/
private def shiftedFiberEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a ℓ : ℕ) (hℓ : 0 < ℓ) :
    {z : Charge D × (ℕ × Occ D) //
      (chargeEnergy D z.1).toNat + level D z.2.2 + z.2.1*ℓ = a} ≃
    (Σ β : positiveChargeCutoff D hD (a : ℤ),
      Σ k : Fin ((a-(chargeEnergy D β.1).toNat)/ℓ+1),
        IntegerFiber D (a-(chargeEnergy D β.1).toNat-k.1*ℓ)) where
  toFun z := by
    have hz := z.2
    have hQ := chargeEnergy_nonneg D hD z.1.1
    refine ⟨⟨z.1.1, ?_⟩, ⟨z.1.2.1, ?_⟩, ⟨z.1.2.2, ?_⟩⟩
    · simp only [positiveChargeCutoff, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
        Int.toNat_natCast]
      omega
    · have hk : z.1.2.1 ≤ (a-(chargeEnergy D z.1.1).toNat)/ℓ :=
        (Nat.le_div_iff_mul_le hℓ).mpr (by omega)
      omega
    · change level D z.1.2.2 = _
      omega
  invFun z := by
    have hβ := z.1.2
    simp only [positiveChargeCutoff, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      Int.toNat_natCast] at hβ
    have hQ := chargeEnergy_nonneg D hD z.1.1
    have hk : z.2.1.1*ℓ ≤ a-(chargeEnergy D z.1.1).toNat :=
      (Nat.le_div_iff_mul_le hℓ).mp (by have := z.2.1.2; omega)
    refine ⟨(z.1.1,z.2.1.1,z.2.2.1), ?_⟩
    have hd := z.2.2.2
    change level D z.2.2.1 = _ at hd
    omega
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by
    apply Sigma.ext (Subtype.ext rfl)
    apply heq_of_eq
    apply Sigma.ext (Fin.ext rfl)
    apply heq_of_eq
    rfl

private theorem shiftedFiber_sum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a ℓ : ℕ) (hℓ : 0 < ℓ) (c : Charge D → ℂ) :
    (∑' z : {z : Charge D × (ℕ × Occ D) //
      (chargeEnergy D z.1).toNat + level D z.2.2 + z.2.1*ℓ = a}, c z.1.1) =
      ∑ β ∈ positiveChargeCutoff D hD (a : ℤ), c β *
        ∑ k ∈ Finset.range ((a-(chargeEnergy D β).toNat)/ℓ+1),
          occupationMultiplicity D (a-(chargeEnergy D β).toNat-k*ℓ) := by
  classical
  rw [← (shiftedFiberEquiv D hD a ℓ hℓ).symm.tsum_eq]
  rw [tsum_fintype, Fintype.sum_sigma]
  apply (Finset.sum_coe_sort _ _).symm.trans
  apply Finset.sum_congr rfl
  intro β hβ
  simp only [Fintype.sum_sigma, Finset.sum_const, nsmul_eq_mul,
    occupationMultiplicity, Nat.card_eq_fintype_card, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

private def naturalFiberEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℕ) :
    {z : Charge D × Occ D // (chargeEnergy D z.1).toNat + level D z.2 = n} ≃
      EnergyFiber D (n : ℤ) where
  toFun z := ⟨z.1, by
    have hz := z.2
    have hQ := chargeEnergy_nonneg D hD z.1.1
    simp only [energy, level] at *
    omega⟩
  invFun z := ⟨z.1, by
    have hz := z.2
    have hQ := chargeEnergy_nonneg D hD z.1.1
    simp only [energy, level] at *
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem naturalFiber_sum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (n : ℕ) (c : Charge D → ℂ) :
    (∑' z : {z : Charge D × Occ D //
      (chargeEnergy D z.1).toNat + level D z.2 = n}, c z.1.1) =
      ∑ β ∈ positiveChargeCutoff D hD (n : ℤ),
        c β * occupationMultiplicity D (n-(chargeEnergy D β).toNat) := by
  classical
  letI := energyFiber_finite D hD (n : ℤ)
  letI := Fintype.ofFinite (EnergyFiber D (n : ℤ))
  rw [← (naturalFiberEquiv D hD n).symm.tsum_eq, tsum_fintype]
  rw [sum_fullFiber D hD n (fun β _ => c β)]
  simp [occupationMultiplicity, Nat.card_eq_fintype_card, mul_comm]

private def energyIndex (D : LatticeData) (z : Charge D × Occ D) : ℕ :=
  (chargeEnergy D z.1).toNat + level D z.2

private def baseTerm (D : LatticeData) (q : ℂ) (c : Charge D → ℂ)
    (z : Charge D × Occ D) : ℂ := c z.1 * q^energyIndex D z

private theorem base_summable (D : LatticeData) (q : ℂ) (c : Charge D → ℂ)
    (hc : Summable (fun β : Charge D => ‖c β*q^(chargeEnergy D β).toNat‖))
    (ho : Summable (fun d : Occ D => ‖q^level D d‖)) :
    Summable (fun z : Charge D × Occ D => ‖baseTerm D q c z‖) := by
  simpa only [baseTerm, energyIndex, pow_add, mul_assoc] using hc.mul_norm ho

private theorem base_sum (D : LatticeData) (q : ℂ) (c : Charge D → ℂ)
    (hc : Summable (fun β : Charge D => ‖c β*q^(chargeEnergy D β).toNat‖))
    (ho : Summable (fun d : Occ D => ‖q^level D d‖)) :
    HasSum (baseTerm D q c)
      ((∑' β : Charge D, c β*q^(chargeEnergy D β).toNat) * oscillatorCharacter D q) := by
  have hs := hc.of_norm.hasSum.mul ho.of_norm.hasSum
    (summable_mul_of_summable_norm hc ho)
  simpa only [baseTerm, energyIndex, oscillatorCharacter, pow_add, mul_assoc] using hs

private def diagonalCoefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (c : Charge D → ℂ) (n : ℕ) : ℂ :=
  ∑ β ∈ positiveChargeCutoff D hD (n : ℤ),
    c β * occupationMultiplicity D (n-(chargeEnergy D β).toNat)

private theorem diagonal_sum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (q : ℂ) (c : Charge D → ℂ)
    (hc : Summable (fun β : Charge D => ‖c β*q^(chargeEnergy D β).toNat‖))
    (ho : Summable (fun d : Occ D => ‖q^level D d‖)) :
    HasSum (fun n : ℕ => q^n * diagonalCoefficient D hD c n)
      ((∑' β : Charge D, c β*q^(chargeEnergy D β).toNat) * oscillatorCharacter D q) := by
  have hs := (base_sum D q c hc ho).tsum_fiberwise (energyIndex D)
  apply hs.congr_fun
  intro n
  change _ = ∑' z : {z : Charge D × Occ D // energyIndex D z = n}, baseTerm D q c z.1
  simp_rw [baseTerm, show ∀ z : {z : Charge D × Occ D // energyIndex D z = n},
    energyIndex D z.1 = n from fun z => z.2]
  rw [tsum_mul_right]
  rw [naturalFiber_sum D hD n c]
  exact mul_comm _ _

private def markedCoefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a r : ℕ) : ℂ :=
  ∑ β ∈ positiveChargeCutoff D hD (a : ℤ),
    ∑ k ∈ Finset.range ((a-(chargeEnergy D β).toNat)/(r+1)+1),
      occupationMultiplicity D (a-(chargeEnergy D β).toNat-k*(r+1))

private def crossEnergy (D : LatticeData)
    (z : (Charge D × Occ D) × (ℕ × ℕ)) : ℕ × ℕ :=
  (energyIndex D z.1 + z.2.2*(z.2.1+1), z.2.1)

private def crossFiberEquiv (D : LatticeData) (a r : ℕ) :
    {z : (Charge D × Occ D) × (ℕ × ℕ) // crossEnergy D z = (a,r)} ≃
      {z : Charge D × (ℕ × Occ D) //
        (chargeEnergy D z.1).toNat + level D z.2.2 + z.2.1*(r+1) = a} where
  toFun z := ⟨(z.1.1.1,z.1.2.2,z.1.1.2), by
    have ha := congrArg Prod.fst z.2
    have hr := congrArg Prod.snd z.2
    dsimp [crossEnergy, energyIndex] at ha hr
    simpa only [hr] using ha⟩
  invFun z := ⟨((z.1.1,z.1.2.2),(r,z.1.2.1)), Prod.ext z.2 rfl⟩
  left_inv z := by
    apply Subtype.ext
    have hr := congrArg Prod.snd z.2
    dsimp [crossEnergy] at hr
    exact Prod.ext rfl (Prod.ext hr.symm rfl)
  right_inv _ := rfl

private theorem cross_sum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (q x : ℂ) (hq : ‖q‖ < 1) (hx : ‖x‖ < 1)
    (hc : Summable (fun β : Charge D => ‖q^(chargeEnergy D β).toNat‖))
    (ho : Summable (fun d : Occ D => ‖q^level D d‖)) :
    HasSum (fun ar : ℕ × ℕ => q^ar.1 * (ar.2+1 : ℂ) * x^(ar.2+1) *
      markedCoefficient D hD ar.1 ar.2)
      (chargeTheta D q * oscillatorCharacter D q *
        ∑' r : ℕ, (r+1 : ℂ)*x^(r+1)/(1-q^(r+1))) := by
  have hc' : Summable (fun β : Charge D => ‖(1:ℂ)*q^(chargeEnergy D β).toNat‖) := by
    simpa only [one_mul] using hc
  have hb := base_sum D q (fun _ => 1) hc' ho
  have hm := marked_sum q x hq hx
  have hj := (base_summable D q (fun _ => 1) hc' ho).mul_norm (marked_summable q x hq hx)
  have hs := (hb.mul hm hj.of_norm).tsum_fiberwise (crossEnergy D)
  simp only [one_mul, ← chargeTheta] at hs
  apply hs.congr_fun
  rintro ⟨a,r⟩
  rw [← (crossFiberEquiv D a r).symm.tsum_eq]
  have ht (z : {z : Charge D × (ℕ × Occ D) //
      (chargeEnergy D z.1).toNat + level D z.2.2 + z.2.1*(r+1) = a}) :
      baseTerm D q (fun _ => 1) ((crossFiberEquiv D a r).symm z).1.1 *
        markedTerm q x ((crossFiberEquiv D a r).symm z).1.2 =
          q^a * (r+1 : ℂ) * x^(r+1) * (1:ℂ) := by
    change 1*q^((chargeEnergy D z.1.1).toNat+level D z.1.2.2) *
      ((r+1 : ℂ)*x^(r+1)*q^(z.1.2.1*(r+1))) = _
    rw [← z.2, pow_add]
    ring
  simp_rw [ht]
  rw [tsum_mul_left, shiftedFiber_sum D hD a (r+1) (by omega) (fun _ => 1)]
  simp only [one_mul, markedCoefficient]

private theorem diagonal_embed (f : ℕ → ℂ) (v : ℂ) (hf : HasSum f v) :
    HasSum (fun nm : ℕ × ℕ => if nm.1 = nm.2 then f nm.1 else 0) v := by
  have hi : Function.Injective (fun n : ℕ => (n,n)) := by
    intro n m h; exact congrArg Prod.fst h
  apply (hi.hasSum_iff (fun nm h => ?_)).mp
  · simpa only [Function.comp_def, if_pos rfl] using hf
  · by_cases he : nm.1 = nm.2
    · exact (h ⟨nm.1, Prod.ext rfl he⟩).elim
    · simp only [if_neg he]

private theorem upper_embed (f : ℕ × ℕ → ℂ) (v : ℂ) (hf : HasSum f v) :
    HasSum (fun nm : ℕ × ℕ =>
      if nm.1 < nm.2 then f (nm.1,nm.2-nm.1-1) else 0) v := by
  have hi : Function.Injective (fun ar : ℕ × ℕ => (ar.1,ar.1+(ar.2+1))) := by
    intro a b h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Prod.ext <;> dsimp at * <;> omega
  apply (hi.hasSum_iff (fun nm h => ?_)).mp
  · convert hf using 1
    ext ar
    simp only [Function.comp_def]
    rw [if_pos (by omega)]
    congr 1
    apply Prod.ext rfl
    omega
  · by_cases he : nm.1 < nm.2
    · exact (h ⟨(nm.1,nm.2-nm.1-1), by apply Prod.ext rfl; dsimp; omega⟩).elim
    · simp only [if_neg he]

private theorem lower_embed (f : ℕ × ℕ → ℂ) (v : ℂ) (hf : HasSum f v) :
    HasSum (fun nm : ℕ × ℕ =>
      if nm.2 < nm.1 then f (nm.2,nm.1-nm.2-1) else 0) v := by
  simpa only [Function.comp_def] using
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (upper_embed f v hf)

/-- The ordinary two-current trace series is absolutely summable on the entire
split open bidisk and has its evaluated charge, oscillator and Lambert value. -/
theorem ordinary_two_current_thermal (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (q1 q2 : ℂ) (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) :
    Summable (fun nm : ℕ × ℕ =>
      ‖q1^nm.1*q2^nm.2*actualCurrentCycleTrace D hD i j nm.1 nm.2‖) ∧
    HasSum (fun nm : ℕ × ℕ =>
      q1^nm.1*q2^nm.2*actualCurrentCycleTrace D hD i j nm.1 nm.2)
      (oscillatorCharacter D (q1*q2) *
        (chargeMoment D i j (q1*q2) + (D.G i j : ℂ)*chargeTheta D (q1*q2)*
          ∑' k : ℕ, (k+1 : ℂ)*(q1^(k+1)+q2^(k+1))/(1-(q1*q2)^(k+1)))) := by
  have hq : ‖q1*q2‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hq2.le (norm_nonneg q1)).trans_lt (by simpa using hq1)
  obtain ⟨hc,hm,ho⟩ := scalar_summable D hD i j q1 q2 hq1 hq2
  refine ⟨trace_norm_summable D hD i j q1 q2 hq1 hq2, ?_⟩
  let c : Charge D → ℂ := fun β =>
    (bilinear D (unitCharge D i) β : ℂ)*(bilinear D (unitCharge D j) β : ℂ)
  have hd := diagonal_embed _ _ (diagonal_sum D hD (q1*q2) c hm ho)
  have hu := upper_embed _ _ ((cross_sum D hD (q1*q2) q2 hq hq2 hc ho).mul_left (D.G i j : ℂ))
  have hl := lower_embed _ _ ((cross_sum D hD (q1*q2) q1 hq hq1 hc ho).mul_left (D.G i j : ℂ))
  have hsum := (hd.add hu).add hl
  have hs1 := (marked_sum (q1*q2) q1 hq hq1).summable
  have hs2 := (marked_sum (q1*q2) q2 hq hq2).summable
  have hk : (∑' k : ℕ, (k+1 : ℂ)*(q1^(k+1)+q2^(k+1))/(1-(q1*q2)^(k+1))) =
      (∑' k : ℕ, (k+1 : ℂ)*q1^(k+1)/(1-(q1*q2)^(k+1))) +
      (∑' k : ℕ, (k+1 : ℂ)*q2^(k+1)/(1-(q1*q2)^(k+1))) := by
    simp_rw [mul_add, add_div]
    exact tsum_add hs1 hs2
  convert hsum using 1
  · ext nm
    rcases nm with ⟨n,m⟩
    simp only [Pi.add_apply]
    rw [actual_two_current_grade_trace]
    by_cases he : n = m
    · subst m
      simp only [if_pos rfl, lt_self_iff_false, if_false, add_zero,
        diagonalCoefficient, c, mul_pow]
    · rw [if_neg he]
      rcases lt_or_gt_of_ne he with h | h
      · have hr : m-n-1+1 = Nat.dist n m := by
          rw [Nat.dist_eq_sub_of_le h.le]; omega
        have hm' : m = n+(m-n-1+1) := by omega
        simp only [if_neg he, if_pos h, if_neg (not_lt_of_ge h.le), zero_add,
          add_zero, Nat.min_eq_left h.le]
        simp only [markedCoefficient, hr]
        rw [hm', pow_add, mul_pow]
        ring
      · have hr : n-m-1+1 = Nat.dist n m := by
          rw [Nat.dist_eq_sub_of_le_right h.le]; omega
        have hn' : n = m+(n-m-1+1) := by omega
        simp only [if_neg he, if_pos h, if_neg (not_lt_of_ge h.le), zero_add,
          add_zero, Nat.min_eq_right h.le]
        simp only [markedCoefficient, hr]
        rw [hn', pow_add, mul_pow]
        ring
  · rw [hk]
    change _ = chargeMoment D i j (q1*q2)*oscillatorCharacter D (q1*q2) + _ + _
    ring

#print axioms ordinary_two_current_thermal

end D5.S3.VertexAlgebra.LatticeTwoCurrentThermal
