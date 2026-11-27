/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qMovingCurrentZero
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Moving current pairs and their zero modes on polynomial and momentum states. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingPairIterate
import Batteries.Tactic.OpenPrivate

/-! The moving current pairs on the full P48q polynomial and momentum state. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingCurrentZero

open LatticeGeneratingFieldLocality (Carrier)
open LatticeAllStateField (vacuum)
open LatticeAllStateReconstruction (mu)
open P48qTwistedChargeAction (Momentum lattice)
open P48qThirdTwistedField (Cartan FixedDualBases Fock Mode State annihilatorDual creator frequency)
open P48qTwistedStateEnergy (momentumWeight numberTerm numberTerm_apply oscillator oscillator_eq_sum
  totalLZero totalLZero_apply)
open ThirdEigenspacePairing (p48qBasis p48qOppositeBasis p48qForm p48q_pair_bases)
open ThirdTwistedIterate (currentAlong oneThirdBinomial)
open ThirdTwistedQuadratic (residue)
open MvPolynomial
open scoped BigOperators Matrix

open private zetaPrimitive formSymmetric from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private numberTerm_support from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy
open private current_product oneThirdBinomial_two from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingPairIterate

noncomputable section

/-- The residue-one direction is in the `ζ²` eigenspace in the signed cover
convention of the full state. For a negative index `k`, its creator has frequency `-k`. -/
def firstDirection (i : Fin 16) : Cartan := p48qOppositeBasis zetaPrimitive i

/-- The residue-two direction is its opposite Gram-dual direction. -/
def secondDirection (i : Fin 16) : Cartan := p48qBasis zetaPrimitive i

theorem pair_directions (i j : Fin 16) :
    p48qForm (firstDirection i) (secondDirection j) = if i = j then 1 else 0 :=
  (formSymmetric.eq _ _).trans (by
    simpa only [firstDirection, secondDirection, eq_comm] using
      p48q_pair_bases zetaPrimitive j i)

/-- The absolute cover frequency determines the polynomial variable of a nonzero mode. -/
def coverVariable (i : Fin 16) (k : ℤ) : Mode := (i, k.natAbs - 1)

theorem frequency_coverVariable (i : Fin 16) {k : ℤ} (hk : k ≠ 0) :
    frequency (coverVariable i k) = k.natAbs :=
  Nat.sub_add_cancel (Int.natAbs_pos.mpr hk)

private theorem coverVariable_neg (i : Fin 16) (k : ℤ) :
    coverVariable i (-k) = coverVariable i k := by
  simp only [coverVariable, Int.natAbs_neg]

private theorem natAbs_mod_of_residue_one {k : ℤ} (hk : k ∈ residue 1) :
    k.natAbs % 3 = if k < 0 then 2 else 1 := by
  change k % 3 = 1 at hk
  by_cases h : k < 0
  · rw [ite_eq_left h]
    have habs := Int.ofNat_natAbs_of_nonpos h.le
    omega
  · rw [ite_eq_right h]
    have habs := Int.natAbs_of_nonneg (le_of_not_gt h)
    omega

private theorem ne_zero_of_residue_one {k : ℤ} (hk : k ∈ residue 1) : k ≠ 0 := by
  change k % 3 = 1 at hk
  omega

/-- On the first grid the negative mode uses the first basis as creator, while
the positive mode uses it as Gram-dual annihilator. The second basis has the opposite roles. -/
theorem directions_coverVariable (B : FixedDualBases) (i : Fin 16) {k : ℤ}
    (hk : k ∈ residue 1) :
    creator B (coverVariable i k) =
        (if k < 0 then firstDirection i else secondDirection i) ∧
    annihilatorDual B (coverVariable i k) =
        (if k < 0 then secondDirection i else firstDirection i) := by
  have hfreq := frequency_coverVariable i (ne_zero_of_residue_one hk)
  have hmod := natAbs_mod_of_residue_one hk
  simp only [creator, annihilatorDual, hfreq, hmod]
  by_cases h : k < 0 <;> simp [h, coverVariable, firstDirection, secondDirection]

/-- The first current has `r = 1`, and the opposite current has `r = 2`.
Each allowed mode acts in place on every momentum sector. -/
def currentMode (r : ℤ) (i : Fin 16) (k : ℤ) : Module.End ℂ State :=
  if k % 3 = r then
    if k < 0 then
      Finsupp.mapRange.linearMap (LinearMap.mulLeft ℂ (X (coverVariable i k) : Fock))
    else if 0 < k then
      Finsupp.mapRange.linearMap
        (((k.natAbs : ℂ) / 3) • (pderiv (coverVariable i k)).toLinearMap)
    else 0
  else 0

theorem currentMode_negative_apply (i : Fin 16) {r k : ℤ} (hr : k % 3 = r) (hk : k < 0)
    (w : State) (p : Momentum) :
    currentMode r i k w p = X (coverVariable i k) * w p := by
  simp only [currentMode, ite_eq_left hr, ite_eq_left hk, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_apply, LinearMap.mulLeft_apply]

theorem currentMode_positive_apply (i : Fin 16) {r k : ℤ} (hr : k % 3 = r) (hk : 0 < k)
    (w : State) (p : Momentum) :
    currentMode r i k w p = ((k.natAbs : ℂ) / 3) • pderiv (coverVariable i k) (w p) := by
  simp only [currentMode, ite_eq_left hr, ite_eq_right hk.not_gt, ite_eq_left hk,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe]

/-- Normal ordering on the same signed grid as `ThirdTwistedQuadratic.orderedPair`. -/
def orderedPair (i : Fin 16) (m k : ℤ) : Module.End ℂ State :=
  if k < 0 then currentMode 1 i k * currentMode 2 i (3 * m - k)
  else currentMode 2 i (3 * m - k) * currentMode 1 i k

theorem orderedPair_eq_zero_off_residue (i : Fin 16) (m k : ℤ) (hk : k ∉ residue 1) :
    orderedPair i m k = 0 := by
  change ¬ k % 3 = 1 at hk
  by_cases h : k < 0 <;> simp [orderedPair, currentMode, hk, h]

/-- Both sign cases give creation after annihilation in the same variable. -/
theorem orderedPair_zero_apply (i : Fin 16) {k : ℤ} (hk : k ∈ residue 1)
    (w : State) (p : Momentum) :
    orderedPair i 0 k w p = numberTerm (coverVariable i k) (w p) := by
  have hfreq := frequency_coverVariable i (ne_zero_of_residue_one hk)
  change k % 3 = 1 at hk
  have hopp : (-k) % 3 = 2 := by omega
  rw [numberTerm_apply, hfreq]
  by_cases h : k < 0
  · have hpos : 0 < -k := by omega
    simp only [orderedPair, Int.mul_zero, zero_sub, ite_eq_left h, Module.End.mul_apply,
      currentMode_negative_apply i hk h, currentMode_positive_apply i hopp hpos,
      Int.natAbs_neg, coverVariable_neg, mul_smul_comm]
  · have hpos : 0 < k := by omega
    have hneg : -k < 0 := by omega
    simp only [orderedPair, Int.mul_zero, zero_sub, ite_eq_right h, Module.End.mul_apply,
      currentMode_negative_apply i hopp hneg, currentMode_positive_apply i hk hpos,
      coverVariable_neg, mul_smul_comm]

/-- Variables of the `i`th pair, with integral frequencies removed. -/
def pairVariables (i : Fin 16) : Set Mode := {j | j.1 = i ∧ frequency j % 3 ≠ 0}

private def signedIndex (j : Mode) : ℤ :=
  if frequency j % 3 = 1 then (frequency j : ℤ) else -(frequency j : ℤ)

private theorem coverVariable_mem (i : Fin 16) {k : ℤ} (hk : k ∈ residue 1) :
    coverVariable i k ∈ pairVariables i := by
  refine ⟨rfl, ?_⟩
  rw [frequency_coverVariable i (ne_zero_of_residue_one hk), natAbs_mod_of_residue_one hk]
  by_cases h : k < 0 <;> simp [h]

private theorem signedIndex_coverVariable (i : Fin 16) {k : ℤ} (hk : k ∈ residue 1) :
    signedIndex (coverVariable i k) = k := by
  rw [signedIndex, frequency_coverVariable i (ne_zero_of_residue_one hk),
    natAbs_mod_of_residue_one hk]
  by_cases h : k < 0
  · simpa only [ite_eq_left h, ite_eq_right (by decide : (2 : ℕ) ≠ 1)] using
      (Int.eq_neg_natAbs_of_nonpos h.le).symm
  · simpa only [ite_eq_right h, eq_self, ite_true] using
      Int.natAbs_of_nonneg (le_of_not_gt h)

private theorem signedIndex_mem {j : Mode} (hj : frequency j % 3 ≠ 0) :
    signedIndex j ∈ residue 1 := by
  change signedIndex j % 3 = 1
  unfold signedIndex
  split <;> omega

private theorem coverVariable_signedIndex (i : Fin 16) {j : Mode} (hj : j.1 = i) :
    coverVariable i (signedIndex j) = j := by
  rcases j with ⟨a, n⟩
  change a = i at hj
  subst a
  simp only [signedIndex]
  split <;> simp only [coverVariable, frequency, Int.natAbs_neg, Int.natAbs_natCast,
    Nat.add_sub_cancel]

/-- The signed first grid counts each moving variable of this pair exactly once. -/
theorem coverVariable_bijOn (i : Fin 16) :
    (residue 1).BijOn (coverVariable i) (pairVariables i) := by
  refine ⟨fun _ hk => coverVariable_mem i hk, ?_, ?_⟩
  · intro k hk l hl h
    simpa only [signedIndex_coverVariable i hk, signedIndex_coverVariable i hl] using
      congrArg signedIndex h
  · intro j hj
    exact ⟨signedIndex j, signedIndex_mem hj.2, coverVariable_signedIndex i hj.1⟩

/-- Variables occurring in one of the finitely many occupied momentum sectors. -/
def stateVars (w : State) : Finset Mode := w.support.biUnion fun p => (w p).vars

/-- The possible nonzero signed indices for this pair on `w`. -/
def zeroIndices (i : Fin 16) (w : State) : Finset ℤ :=
  ((stateVars w).filter fun j => j.1 = i ∧ frequency j % 3 ≠ 0).image signedIndex

theorem orderedPair_zero_support (i : Fin 16) (w : State) :
    Function.support (fun k => orderedPair i 0 k w) ⊆ (zeroIndices i w : Set ℤ) := by
  classical
  intro k hk
  change orderedPair i 0 k w ≠ 0 at hk
  have hr : k ∈ residue 1 := by
    by_contra hout
    exact hk (by rw [orderedPair_eq_zero_off_residue i 0 k hout, LinearMap.zero_apply])
  obtain ⟨p, hp⟩ : ∃ p : Momentum, orderedPair i 0 k w p ≠ 0 := by
    by_contra! h
    apply hk
    apply Finsupp.ext
    intro p
    simpa only [Finsupp.zero_apply] using h p
  rw [orderedPair_zero_apply i hr] at hp
  have hv : coverVariable i k ∈ (w p).vars := numberTerm_support (w p) hp
  have hwp : p ∈ w.support := by
    apply Finsupp.mem_support_iff.mpr
    intro hz
    exact hp (by rw [hz, map_zero])
  change k ∈ zeroIndices i w
  rw [zeroIndices, Finset.mem_image]
  refine ⟨coverVariable i k, Finset.mem_filter.mpr ⟨?_, coverVariable_mem i hr⟩,
    signedIndex_coverVariable i hr⟩
  exact Finset.mem_biUnion.mpr ⟨p, hwp, hv⟩

theorem orderedPair_zero_finite (i : Fin 16) (w : State) :
    (residue 1 ∩ Function.support (fun k => orderedPair i 0 k w)).Finite :=
  (zeroIndices i w).finite_toSet.subset fun _ hk => orderedPair_zero_support i w hk.2

/-- The unshifted, normal-ordered zero coefficient on the full state. -/
def orderedZero (i : Fin 16) : Module.End ℂ State where
  toFun w := ∑ᶠ k ∈ residue 1, orderedPair i 0 k w
  map_add' w v := by
    simp only [map_add]
    exact finsum_mem_add_distrib' (orderedPair_zero_finite i w) (orderedPair_zero_finite i v)
  map_smul' c w := by
    simp only [map_smul, RingHom.id_apply]
    simpa only [DistribSMul.toAddMonoidHom_apply] using
      ((DistribSMul.toAddMonoidHom State c).map_finsum_mem'
        (orderedPair_zero_finite i w)).symm

theorem orderedZero_apply (i : Fin 16) (w : State) (p : Momentum) :
    orderedZero i w p =
      ∑ j ∈ (w p).vars with j.1 = i ∧ frequency j % 3 ≠ 0, numberTerm j (w p) := by
  calc
    orderedZero i w p = ∑ᶠ k ∈ residue 1, orderedPair i 0 k w p := by
      change (∑ᶠ k ∈ residue 1, orderedPair i 0 k w) p = _
      simpa only [LinearMap.toAddMonoidHom_coe, Finsupp.lapply_apply] using
        (Finsupp.lapply p : State →ₗ[ℂ] Fock).toAddMonoidHom.map_finsum_mem'
          (orderedPair_zero_finite i w)
    _ = ∑ᶠ j ∈ pairVariables i, numberTerm j (w p) :=
      finsum_mem_eq_of_bijOn (coverVariable i) (coverVariable_bijOn i)
        fun k hk => orderedPair_zero_apply i hk w p
    _ = _ := by
      apply finsum_mem_eq_sum_of_subset
      · intro j hj
        exact Finset.mem_filter.mpr ⟨numberTerm_support (w p) hj.2, hj.1⟩
      · intro j hj
        exact (Finset.mem_filter.mp hj).2

/-- The vacuum correction of one normalized moving pair. -/
def pairLZero (i : Fin 16) : Module.End ℂ State :=
  orderedZero i + (1 / 9 : ℂ) • LinearMap.id

def movingLZero : Module.End ℂ State := ∑ i : Fin 16, pairLZero i

/-- On each momentum sector the sixteen pairs give the fractional Euler sum
and the shift `16/9`. Variables of integral frequency are absent from this sum. -/
theorem movingLZero_apply (w : State) (p : Momentum) :
    movingLZero w p =
      (∑ j ∈ (w p).vars with frequency j % 3 ≠ 0, numberTerm j (w p)) +
        (16 / 9 : ℂ) • w p := by
  let S := (w p).vars.filter fun j => frequency j % 3 ≠ 0
  have hsum (i : Fin 16) : orderedZero i w p =
      ∑ j ∈ S with j.1 = i, numberTerm j (w p) := by
    rw [orderedZero_apply]
    simp only [S, Finset.filter_filter, and_comm]
  have hpartition :
      (∑ i : Fin 16, ∑ j ∈ S with j.1 = i, numberTerm j (w p)) =
        ∑ j ∈ S, numberTerm j (w p) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hshift : (∑ _i : Fin 16, (1 / 9 : ℂ) • w p) = (16 / 9 : ℂ) • w p := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul]
    rw [show ((16 : ℕ) : ℂ) * (1 / 9) = 16 / 9 by norm_num]
  calc
    movingLZero w p = ∑ i : Fin 16, pairLZero i w p := by
      simp only [movingLZero, LinearMap.sum_apply, Finsupp.finsetSum_apply]
    _ = (∑ i : Fin 16, ∑ j ∈ S with j.1 = i, numberTerm j (w p)) +
        ∑ _i : Fin 16, (1 / 9 : ℂ) • w p := by
      simp only [pairLZero, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        Finsupp.add_apply, Finsupp.smul_apply, hsum, Finset.sum_add_distrib]
    _ = _ := by rw [hpartition, hshift]

/-- The moving calculation agrees with the moving block of the total energy. -/
theorem totalLZero_apply_split (w : State) (p : Momentum) :
    totalLZero w p =
      (∑ j ∈ (w p).vars with frequency j % 3 = 0, numberTerm j (w p)) +
        (momentumWeight p : ℂ) • w p + movingLZero w p := by
  have hosc : oscillator (w p) = ∑ j ∈ (w p).vars, numberTerm j (w p) := by
    rw [oscillator_eq_sum]
    simp only [numberTerm_apply]
  rw [totalLZero_apply, movingLZero_apply, hosc]
  rw [← Finset.sum_filter_add_sum_filter_not (w p).vars (fun j => frequency j % 3 = 0)
    (fun j => numberTerm j (w p))]
  abel

/-- The native currents along the actual opposite Gram basis vectors. -/
abbrev firstCurrent (i : Fin 16) : Carrier lattice := currentAlong lattice (firstDirection i)

abbrev secondCurrent (i : Fin 16) : Carrier lattice := currentAlong lattice (secondDirection i)

abbrev TwistedStateField := Carrier lattice →ₗ[ℂ] ℤ → Module.End ℂ State

/-- The zero-coefficient instance of `ThirdTwistedIterate.nativePairIterate` on `State`. -/
def PairIterateAtZero (i : Fin 16) (Ytw : TwistedStateField) : Prop :=
  ∀ w : State,
    (∑ᶠ k ∈ residue 1,
      (if k < 0 then Ytw (firstCurrent i) k * Ytw (secondCurrent i) (-k)
       else Ytw (secondCurrent i) (-k) * Ytw (firstCurrent i) k) w) =
      ∑ᶠ j : ℕ, oneThirdBinomial j •
        Ytw (mu lattice (firstCurrent i) ((j : ℤ) - 1) (secondCurrent i)) (3 * (1 - (j : ℤ))) w

/-- A field extending the concrete currents and satisfying the zero-coefficient
iterate acts on the native pair state by the shifted zero mode. -/
theorem nativePair_zero_of_iterate (i : Fin 16) (Ytw : TwistedStateField)
    (hFirst : ∀ k : ℤ, k ∈ residue 1 → Ytw (firstCurrent i) k = currentMode 1 i k)
    (hSecond : ∀ k : ℤ, k ∈ residue 2 → Ytw (secondCurrent i) k = currentMode 2 i k)
    (hVac : Ytw (vacuum lattice) (-3) = LinearMap.id)
    (hIterate : PairIterateAtZero i Ytw) :
    Ytw (mu lattice (firstCurrent i) (-1) (secondCurrent i)) 3 = pairLZero i := by
  apply LinearMap.ext
  intro w
  let term (j : ℕ) : State := oneThirdBinomial j •
    Ytw (mu lattice (firstCurrent i) ((j : ℤ) - 1) (secondCurrent i)) (3 * (1 - (j : ℤ))) w
  have hleft : orderedZero i w =
      ∑ᶠ k ∈ residue 1,
        (if k < 0 then Ytw (firstCurrent i) k * Ytw (secondCurrent i) (-k)
         else Ytw (secondCurrent i) (-k) * Ytw (firstCurrent i) k) w := by
    change (∑ᶠ k ∈ residue 1, orderedPair i 0 k w) = _
    refine finsum_mem_congr rfl fun k hk => ?_
    have hOpp : -k ∈ residue 2 := by
      change k % 3 = 1 at hk
      change (-k) % 3 = 2
      omega
    simp only [orderedPair, Int.mul_zero, zero_sub, hFirst k hk, hSecond (-k) hOpp]
  have hproduct (n : ℤ) (hn : 0 ≤ n) :
      mu lattice (firstCurrent i) n (secondCurrent i) = if n = 1 then vacuum lattice else 0 := by
    have hpair : (lattice.G.map (Int.castRingHom ℂ)).toBilin'
        (firstDirection i) (secondDirection i) = 1 := by
      change p48qForm (firstDirection i) (secondDirection i) = 1
      simpa only [eq_self, ite_true] using pair_directions i i
    simpa only [hpair, one_smul] using
      current_product lattice (firstDirection i) (secondDirection i) n hn
  have hsupport : Function.support term ⊆ (↑({0, 2} : Finset ℕ) : Set ℕ) := by
    intro j hj
    by_contra h
    have hj0 : j ≠ 0 := fun hz => h (by simp [hz])
    have hj2 : j ≠ 2 := fun hz => h (by simp [hz])
    apply hj
    dsimp only [term]
    rw [hproduct _ (by omega), ite_eq_right (show (j : ℤ) - 1 ≠ 1 by omega)]
    simp
  have h0 : term 0 = Ytw (mu lattice (firstCurrent i) (-1) (secondCurrent i)) 3 w := by
    simp [term, oneThirdBinomial]
  have h2 : term 2 = -((1 / 9 : ℂ) • w) := by
    have hp : mu lattice (firstCurrent i) 1 (secondCurrent i) = vacuum lattice := by
      simpa only [eq_self, ite_true] using hproduct 1 (by decide)
    change oneThirdBinomial 2 • Ytw (mu lattice (firstCurrent i) 1 (secondCurrent i)) (-3) w = _
    rw [oneThirdBinomial_two, hp, hVac, LinearMap.id_apply, neg_div, neg_smul]
  have h := hleft.trans (hIterate w)
  change orderedZero i w = ∑ᶠ j : ℕ, term j at h
  rw [finsum_eq_sum_of_support_subset term hsupport, Finset.sum_pair (by decide : (0 : ℕ) ≠ 2),
    h0, h2] at h
  simp only [pairLZero, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, h]
  abel

/-- Under the pair iterate for all sixteen pairs, the native moving quadratic
block acts by the computed full-state moving zero mode. -/
theorem nativeMoving_zero_of_iterate (Ytw : TwistedStateField)
    (hFirst : ∀ (i : Fin 16) (k : ℤ), k ∈ residue 1 →
      Ytw (firstCurrent i) k = currentMode 1 i k)
    (hSecond : ∀ (i : Fin 16) (k : ℤ), k ∈ residue 2 →
      Ytw (secondCurrent i) k = currentMode 2 i k)
    (hVac : Ytw (vacuum lattice) (-3) = LinearMap.id)
    (hIterate : ∀ i : Fin 16, PairIterateAtZero i Ytw) :
    Ytw (∑ i : Fin 16, mu lattice (firstCurrent i) (-1) (secondCurrent i)) 3 = movingLZero := by
  rw [map_sum]
  simp only [movingLZero, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ =>
    nativePair_zero_of_iterate i Ytw (hFirst i) (hSecond i) hVac (hIterate i)

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingCurrentZero
