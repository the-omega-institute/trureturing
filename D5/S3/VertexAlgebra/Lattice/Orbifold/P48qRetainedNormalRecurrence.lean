/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qRetainedNormalRecurrence
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed insertion and derivative recurrence for retained jet words. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeChargedWickFactorization
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qIntegratedNormalMode
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation

/-! The signed coefficient recurrence for the native retained words at a fixed source cutoff. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qRetainedNormalRecurrence

open LatticeGeneratingFieldLocality (Charge bilinear)
open P48qTwistedChargeAction (lattice g Momentum)
open P48qThirdTwistedField (Cartan Fock State chargeVector fixedDualBases
  creationCoordinate positiveAnnihilator)
open P48qTwistedHeisenberg (mode modeLinear mode_negative_apply mode_eq_zero_above_coverBound)
open P48qFixedCurrentIterate (coverBound)
open P48qJetNormalOrdering (Jet jetWeight normalOrderedCoeff normalOrderedCoeff_bddBelow
  normalOrderedCoeff_cons_apply)
open P48qSignedNormalWord (insertMode insertMode_apply)
open P48qAllJetWickField (oscillatorJet totalLevel)
open P48qNativeChargedWickFactorization (letterJet letterSeries retainedJetCoeff
  nativeRetainedSeries)
open P48qNativeCreationWordExpansion (Letter letterLevel letterWeight)
open P48qFiniteWickSum (retainedSeries)
open P48qIntegratedNormalMode (integratedNormalMode)
open PowerSeries (coeff)

open private creationPolynomial mode_positive_single mode_zero_single from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation
open private constantCoeff_letterSeries retainedJetCoeff_perm letterScalar coeff_letterSeries
  sum_chargeCoordinates from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeChargedWickFactorization
open private derivative_retainedSeries weightedSum from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteWickSum

local notation "shift" => ThirdTwistedChargeAction.shift lattice g

/-- The native retained coefficient with its source alphabet fixed at cutoff `D`. -/
def retainedCoefficient (D n : ℕ) (a b : Charge lattice) (h : ℤ)
    (p : Momentum) (P : Fock) : Fock :=
  coeff n
    (retainedSeries (letterJet (d := D)) (letterSeries a)
      (retainedJetCoeff (a + b) h p P) [])

/-- Negative modes act on the output, and nonnegative modes act on the original input. -/
def retainedJetModeReadout (c : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock)
    (xs : List Jet) (u : Cartan) (m : ℤ) : Fock :=
  if m < 0 then
    (mode u m
      (normalOrderedCoeff c (h + m - 3 * (totalLevel xs : ℤ)) xs
        (Finsupp.single p P))) (shift c p)
  else
    (normalOrderedCoeff c (h + m - 3 * (totalLevel xs : ℤ)) xs
      (mode u m (Finsupp.single p P))) (shift c p)

/-- A finite interval for a retained tail on a fixed input, uniform in the inserted direction. -/
private def retainedJetModeIndices (c : Charge lattice) (h : ℤ) (p : Momentum)
    (P : Fock) (xs : List Jet) : Finset ℤ :=
  Finset.Icc
    (min 0 ((normalOrderedCoeff_bddBelow c xs (Finsupp.single p P)).choose -
      h + 3 * (totalLevel xs : ℤ)))
    (coverBound (Finsupp.single p P) : ℤ)

private theorem insertMode_retained_apply
    (c : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock)
    (xs : List Jet) (u : Cartan) (m : ℤ) :
    insertMode (u, m) (normalOrderedCoeff c (h + m - 3 * (totalLevel xs : ℤ)) xs)
        (Finsupp.single p P) (shift c p) =
      retainedJetModeReadout c h p P xs u m := by
  rw [insertMode_apply, retainedJetModeReadout]
  split_ifs <;> rfl

private theorem insertMode_retained_support
    (c : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock)
    (xs : List Jet) (u : Cartan) :
    Function.support (fun m : ℤ =>
      insertMode (u, m) (normalOrderedCoeff c (h + m - 3 * (totalLevel xs : ℤ)) xs)
        (Finsupp.single p P)) ⊆ (retainedJetModeIndices c h p P xs : Set ℤ) := by
  intro m hm
  change _ ≠ 0 at hm
  change m ∈ retainedJetModeIndices c h p P xs
  rw [retainedJetModeIndices, Finset.mem_Icc]
  by_cases hneg : m < 0
  · have hnonzero : normalOrderedCoeff c (h + m - 3 * (totalLevel xs : ℤ)) xs
        (Finsupp.single p P) ≠ 0 := by
      intro hz
      apply hm
      simp [insertMode_apply, hneg, Module.End.mul_apply, hz]
    have hlo := (normalOrderedCoeff_bddBelow c xs (Finsupp.single p P)).choose_spec
      hnonzero
    exact ⟨min_le_of_right_le (by omega), by omega⟩
  · refine ⟨min_le_of_left_le (le_of_not_gt hneg), le_of_not_gt fun hhigh => ?_⟩
    apply hm
    simp [insertMode_apply, hneg, Module.End.mul_apply,
      mode_eq_zero_above_coverBound (Finsupp.single p P) u m hhigh]

private theorem retainedJetModeReadout_support
    (c : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock)
    (xs : List Jet) (u : Cartan) :
    Function.support (retainedJetModeReadout c h p P xs u) ⊆
      (retainedJetModeIndices c h p P xs : Set ℤ) := by
  intro m hm
  apply insertMode_retained_support c h p P xs u
  intro hz
  apply hm
  rw [← insertMode_retained_apply]
  exact (congrArg (fun w : State => w (shift c p)) hz).trans Finsupp.zero_apply

theorem retainedJetModeReadout_hasFiniteSupport
    (c : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock) (xs : List Jet) (u : Cartan) :
    Function.HasFiniteSupport (retainedJetModeReadout c h p P xs u) :=
  (retainedJetModeIndices c h p P xs).finite_toSet.subset
    (retainedJetModeReadout_support c h p P xs u)

/-- The retained head uses the actual signed insertion at the shifted momentum. -/
theorem retainedJetCoeff_cons_eq_signed_insertion
    (c : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock)
    (j : Jet) (xs : List Jet) :
    retainedJetCoeff c h p P (j :: xs) =
      ∑ᶠ m : ℤ, jetWeight j.2 m • retainedJetModeReadout c h p P xs j.1 m := by
  rw [retainedJetCoeff, normalOrderedCoeff_cons_apply]
  have hindex (m : ℤ) :
      h - 3 * (totalLevel (j :: xs) : ℤ) + 3 * ((j.2 : ℕ) : ℤ) + m =
      h + m - 3 * (totalLevel xs : ℤ) := by
    simp only [totalLevel, Nat.cast_add]
    omega
  simp only [hindex]
  let eval : State →ₗ[ℂ] Fock := Finsupp.lapply (shift c p)
  change eval (∑ᶠ m : ℤ, jetWeight j.2 m •
    insertMode (j.1, m) (normalOrderedCoeff c (h + m - 3 * (totalLevel xs : ℤ)) xs)
      (Finsupp.single p P)) = _
  have hs : Function.HasFiniteSupport (fun m : ℤ => jetWeight j.2 m •
      insertMode (j.1, m) (normalOrderedCoeff c (h + m - 3 * (totalLevel xs : ℤ)) xs)
        (Finsupp.single p P)) := by
    refine (retainedJetModeIndices c h p P xs).finite_toSet.subset ?_
    intro m hm
    change _ ≠ 0 at hm
    apply insertMode_retained_support c h p P xs j.1
    intro hz
    exact hm ((congrArg (jetWeight j.2 m • ·) hz).trans (smul_zero _))
  rw [map_finsum eval hs]
  apply finsum_congr
  intro m
  rw [map_smul]
  exact congrArg (jetWeight j.2 m • ·) (insertMode_retained_apply c h p P xs j.1 m)

/-- The signed mode on a fixed-cutoff coefficient. The zero-mode eigenvalue is at `p`. -/
def retainedModeShift (D n : ℕ) (a b : Charge lattice) (h : ℤ)
    (p : Momentum) (P : Fock) (m : ℤ) : Fock :=
  match m with
  | .negSucc s =>
      creationPolynomial fixedDualBases a s * retainedCoefficient D n a b (h + m) p P
  | .ofNat 0 =>
      ((bilinear lattice a p.1 : ℂ) / 3) • retainedCoefficient D n a b h p P
  | .ofNat (s + 1) =>
      retainedCoefficient D n a b (h + m) p (positiveAnnihilator fixedDualBases a s P)

theorem retainedModeShift_negSucc
    (D n : ℕ) (a b : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock) (s : ℕ) :
    retainedModeShift D n a b h p P (.negSucc s) =
      creationPolynomial fixedDualBases a s *
        retainedCoefficient D n a b (h - (s + 1 : ℕ)) p P := by
  change creationPolynomial fixedDualBases a s * retainedCoefficient D n a b
    (h + Int.negSucc s) p P = _
  rw [show h + Int.negSucc s = h - (s + 1 : ℕ) by omega]

theorem retainedModeShift_zero
    (D n : ℕ) (a b : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock) :
    retainedModeShift D n a b h p P 0 =
      ((bilinear lattice a p.1 : ℂ) / 3) • retainedCoefficient D n a b h p P := rfl

theorem retainedModeShift_posNat
    (D n : ℕ) (a b : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock) (s : ℕ) :
    retainedModeShift D n a b h p P (.ofNat (s + 1)) =
      retainedCoefficient D n a b (h + (s + 1 : ℕ)) p
        (positiveAnnihilator fixedDualBases a s P) := rfl

/-- A coefficient with one jet already marked in the retained prefix. -/
def pointedRetainedCoefficient (D n : ℕ) (a b : Charge lattice) (h : ℤ)
    (p : Momentum) (P : Fock) (j : Jet) : Fock :=
  coeff n
    (retainedSeries (letterJet (d := D)) (letterSeries a)
      (retainedJetCoeff (a + b) h p P) [j])

private theorem coeff_derivative_letterSeries {D : ℕ} (a : Charge lattice)
    (r : ℕ) (j : Letter D) :
    coeff r (PowerSeries.derivative (letterSeries a j)) =
      if r = j.2.val then algebraMap ℂ Fock (a j.1 : ℂ) else 0 := by
  rw [PowerSeries.coeff_derivative, coeff_letterSeries, letterScalar, letterLevel]
  by_cases hr : r = j.2.val
  · subst r
    simp only [ite_true, letterWeight, letterLevel]
    rw [show (j.2.val : Fock) + 1 = algebraMap ℂ Fock ((j.2.val + 1 : ℕ) : ℂ) by
      rw [map_natCast, Nat.cast_succ], ← map_mul]
    have hlevel : ((j.2.val + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero j.2.val
    rw [div_mul_cancel₀ _ hlevel]
  · have hne : r + 1 ≠ j.2.val + 1 := by omega
    simp only [ite_eq_right hr, ite_eq_right hne, map_zero, zero_mul]

/-- The coefficient derivative points a letter and cancels its level denominator. -/
theorem retainedCoefficient_derivative
    (D n : ℕ) (hn : n < D) (a b : Charge lattice) (h : ℤ)
    (p : Momentum) (P : Fock) :
    ((n + 1 : ℕ) : ℂ) • retainedCoefficient D (n + 1) a b h p P =
      ∑ r : Fin (n + 1), ∑ i : Fin lattice.rank, (a i : ℂ) •
        pointedRetainedCoefficient D (n - r.val) a b h p P (oscillatorJet (i, r.val)) := by
  classical
  rw [retainedCoefficient, Algebra.smul_def, map_natCast, Nat.cast_succ, mul_comm,
    ← PowerSeries.coeff_derivative, derivative_retainedSeries _ _ _
      (constantCoeff_letterSeries a) (retainedJetCoeff_perm (a + b) h p P)]
  simp only [map_sum, List.nil_append]
  have hcoeff (j : Letter D) :
      coeff n (PowerSeries.derivative (letterSeries a j) *
        retainedSeries (letterJet (d := D)) (letterSeries a) (retainedJetCoeff (a + b) h p P)
          [letterJet j]) =
      ∑ r : Fin (n + 1),
        (if r.val = j.2.val then algebraMap ℂ Fock (a j.1 : ℂ) else 0) *
          pointedRetainedCoefficient D (n - r.val) a b h p P (letterJet j) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      ← Fin.sum_univ_eq_sum_range]
    simp only [coeff_derivative_letterSeries, pointedRetainedCoefficient]
  change (∑ j : Letter D, coeff n (PowerSeries.derivative (letterSeries a j) *
    retainedSeries (letterJet (d := D)) (letterSeries a) (retainedJetCoeff (a + b) h p P)
      [letterJet j])) = _
  simp only [hcoeff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  let l : Fin D := ⟨r.val, by have hr := r.isLt; omega⟩
  rw [Fintype.sum_prod_type_right, Finset.sum_eq_single l]
  · simp only [l, ite_true, ← Algebra.smul_def]
    rfl
  · intro j _ hj
    have hne : r.val ≠ j.val := fun he => hj (Fin.ext he.symm)
    simp only [hne, ite_false, zero_mul, Finset.sum_const_zero]
  · simp

private abbrev BoundedWord (D n : ℕ) := Σ k : Fin (n + 1), Fin k.val → Letter D

private def jetsOfWord {D n : ℕ} (q : BoundedWord D n) : List Jet :=
  P48qFiniteWickSum.word (letterJet (d := D)) q.2

/-- A fixed coefficient is a linear combination of readouts of the bounded words. -/
private def wordReadout (D n : ℕ) (a : Charge lattice) :
    (BoundedWord D n → Fock) →ₗ[ℂ] Fock where
  toFun K := ∑ q : BoundedWord D n,
    (q.1.val.factorial : ℂ)⁻¹ •
      (coeff n (P48qFiniteWickSum.weight (letterSeries a) q.2) * K q)
  map_add' K L := by
    simp only [Pi.add_apply, mul_add, smul_add, Finset.sum_add_distrib]
  map_smul' r K := by
    simp only [Pi.smul_apply, mul_smul_comm, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro q _
    rw [smul_comm]

private theorem coeff_retainedSeries
    (D n : ℕ) (a : Charge lattice) (K : List Jet → Fock) (pre : List Jet) :
    coeff n (retainedSeries (letterJet (d := D)) (letterSeries a) K pre) =
      wordReadout D n a (fun q => K (pre ++ jetsOfWord q)) := by
  classical
  unfold retainedSeries P48qFiniteWickSum.wordSeries
  rw [P48qFiniteWickSum.coeff_sumByDegree, ← Fin.sum_univ_eq_sum_range]
  change (∑ k : Fin (n + 1), coeff n
    (P48qFiniteWickSum.factorialSum (letterJet (d := D)) (letterSeries a) k.val
      (fun w => PowerSeries.C (K (pre ++ w))))) = _
  simp only [P48qFiniteWickSum.factorialSum, ← Algebra.smul_def, PowerSeries.coeff_smul,
    weightedSum, map_sum, PowerSeries.coeff_mul_C, Finset.smul_sum]
  change _ = ∑ q : BoundedWord D n, _
  rw [Fintype.sum_sigma]
  rfl

private theorem retainedJetModeReadout_negSucc (a b : Charge lattice) (h : ℤ)
    (p : Momentum) (P : Fock) (xs : List Jet) (s : ℕ) :
    retainedJetModeReadout (a + b) h p P xs (chargeVector a) (.negSucc s) =
      creationPolynomial fixedDualBases a s *
        retainedJetCoeff (a + b) (h + Int.negSucc s) p P xs := by
  rw [retainedJetModeReadout, ite_eq_left (Int.negSucc_lt_zero s), mode_negative_apply,
    retainedJetCoeff, creationPolynomial, Finset.sum_mul]
  simp only [P48qTwistedHeisenberg.creCoordinates, creationCoordinate, smul_mul_assoc]

private theorem wordReadout_mode
    (D n : ℕ) (a b : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock) (m : ℤ) :
    wordReadout D n a
        (fun q => retainedJetModeReadout (a + b) h p P (jetsOfWord q) (chargeVector a) m) =
      retainedModeShift D n a b h p P m := by
  cases m with
  | negSucc s =>
    simp only [retainedJetModeReadout_negSucc]
    change _ = creationPolynomial fixedDualBases a s * retainedCoefficient D n a b
      (h + Int.negSucc s) p P
    rw [retainedCoefficient, coeff_retainedSeries]
    simp only [List.nil_append]
    change (∑ q : BoundedWord D n, _) = creationPolynomial fixedDualBases a s * (∑ q, _)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [mul_smul_comm, mul_left_comm]
  | ofNat k =>
    cases k with
    | zero =>
      have hread (q : BoundedWord D n) :
          retainedJetModeReadout (a + b) h p P (jetsOfWord q) (chargeVector a) 0 =
            ((bilinear lattice a p.1 : ℂ) / 3) •
              retainedJetCoeff (a + b) h p P (jetsOfWord q) := by
        simp only [retainedJetModeReadout, lt_irrefl, ite_false, add_zero,
          mode_zero_single, map_smul, Finsupp.smul_apply, retainedJetCoeff]
      change wordReadout D n a
        (fun q => retainedJetModeReadout (a + b) h p P (jetsOfWord q) (chargeVector a) 0) =
          ((bilinear lattice a p.1 : ℂ) / 3) • retainedCoefficient D n a b h p P
      simp only [hread, retainedCoefficient, coeff_retainedSeries,
        List.nil_append]
      exact map_smul (wordReadout D n a) _ _
    | succ s =>
      have hnonneg : ¬ Int.ofNat (s + 1) < 0 := not_lt_of_ge (Int.natCast_nonneg _)
      simp only [retainedJetModeReadout, ite_eq_right hnonneg, mode_positive_single,
        retainedModeShift_posNat, retainedCoefficient, coeff_retainedSeries, List.nil_append,
        retainedJetCoeff]
      rfl

private def modeReadoutLinear (c : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock)
    (xs : List Jet) (m : ℤ) : Cartan →ₗ[ℂ] Fock :=
  let eval : State →ₗ[ℂ] Fock := Finsupp.lapply (shift c p)
  let B := normalOrderedCoeff c (h + m - 3 * (totalLevel xs : ℤ)) xs
  let w : State := Finsupp.single p P
  if m < 0 then
    (eval.comp (LinearMap.applyₗ (R := ℂ) (B w))).comp (modeLinear m)
  else
    ((eval.comp B).comp (LinearMap.applyₗ (R := ℂ) w)).comp (modeLinear m)

private theorem modeReadoutLinear_apply (c : Charge lattice) (h : ℤ) (p : Momentum)
    (P : Fock) (xs : List Jet) (m : ℤ) (u : Cartan) :
    modeReadoutLinear c h p P xs m u = retainedJetModeReadout c h p P xs u m := by
  rw [modeReadoutLinear, retainedJetModeReadout]
  split_ifs <;> rfl

private theorem wordMode_hasFiniteSupport
    (D n : ℕ) (c : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock)
    (u : Cartan) (v : ℤ → ℂ) :
    Function.HasFiniteSupport
      (fun m : ℤ => fun q : BoundedWord D n =>
        v m • retainedJetModeReadout c h p P (jetsOfWord q) u m) := by
  classical
  let S : Finset ℤ := Finset.univ.biUnion
    (fun q : BoundedWord D n => retainedJetModeIndices c h p P (jetsOfWord q))
  refine S.finite_toSet.subset ?_
  intro m hm
  change m ∈ S
  by_contra hnot
  apply hm
  funext q
  have hz : retainedJetModeReadout c h p P (jetsOfWord q) u m = 0 := by
    by_contra hq
    exact hnot (Finset.mem_biUnion.mpr
      ⟨q, Finset.mem_univ _, retainedJetModeReadout_support c h p P (jetsOfWord q) u hq⟩)
  change v m • retainedJetModeReadout c h p P (jetsOfWord q) u m = 0
  rw [hz, smul_zero]

/-- The finite support also holds after summing the bounded retained words. -/
theorem retainedModeShift_hasFiniteSupport
    (D n : ℕ) (a b : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock) :
    Function.HasFiniteSupport (retainedModeShift D n a b h p P) := by
  have hs := wordMode_hasFiniteSupport D n (a + b) h p P (chargeVector a) (fun _ => 1)
  refine hs.subset ?_
  intro m hm hz
  apply hm
  rw [← wordReadout_mode]
  have hz' : (fun q : BoundedWord D n =>
      retainedJetModeReadout (a + b) h p P (jetsOfWord q) (chargeVector a) m) = 0 := by
    simpa only [one_smul] using hz
  rw [hz', map_zero]

private theorem charge_sum_word (a c : Charge lattice) (h : ℤ) (p : Momentum)
    (P : Fock) (xs : List Jet) (r : ℕ) :
    (∑ i : Fin lattice.rank, (a i : ℂ) • retainedJetCoeff c h p P
        (oscillatorJet (i, r) :: xs)) =
      ∑ᶠ m : ℤ, jetWeight ⟨r + 1, Nat.succ_pos r⟩ m •
        retainedJetModeReadout c h p P xs (chargeVector a) m := by
  classical
  let S := retainedJetModeIndices c h p P xs
  let v := jetWeight ⟨r + 1, Nat.succ_pos r⟩
  have hs (u : Cartan) :
      Function.support (fun m : ℤ => v m • retainedJetModeReadout c h p P xs u m) ⊆
        (S : Set ℤ) := by
    intro m hm
    apply retainedJetModeReadout_support c h p P xs u
    intro hz
    exact hm (by simp [hz])
  have hjet (i : Fin lattice.rank) :
      retainedJetCoeff c h p P (oscillatorJet (i, r) :: xs) =
        ∑ m ∈ S, v m • retainedJetModeReadout c h p P xs (Pi.single i 1) m :=
    (retainedJetCoeff_cons_eq_signed_insertion c h p P (oscillatorJet (i, r)) xs).trans
      (finsum_eq_finsetSum_of_support_subset _ (hs (Pi.single i 1)))
  rw [finsum_eq_finsetSum_of_support_subset _ (hs (chargeVector a))]
  simp only [hjet, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  simp only [smul_comm (a _ : ℂ) (v m), ← Finset.smul_sum]
  congr 1
  simp only [← modeReadoutLinear_apply, ← map_smul, ← map_sum]
  rw [sum_chargeCoordinates a]

/-- Sum the marked direction and transfer its finite signed sum through the word weights. -/
theorem pointedRetainedCoefficient_charge_sum
    (D n r : ℕ) (a b : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock) :
    ∑ i : Fin lattice.rank, (a i : ℂ) •
        pointedRetainedCoefficient D n a b h p P (oscillatorJet (i, r)) =
      ∑ᶠ m : ℤ, jetWeight ⟨r + 1, Nat.succ_pos r⟩ m •
        retainedModeShift D n a b h p P m := by
  let v := jetWeight ⟨r + 1, Nat.succ_pos r⟩
  let A (m : ℤ) (q : BoundedWord D n) :=
    v m • retainedJetModeReadout (a + b) h p P (jetsOfWord q) (chargeVector a) m
  have hs : Function.HasFiniteSupport A :=
    wordMode_hasFiniteSupport D n (a + b) h p P (chargeVector a) v
  have hsum :
      (∑ i : Fin lattice.rank, (a i : ℂ) •
        (fun q : BoundedWord D n => retainedJetCoeff (a + b) h p P
          (oscillatorJet (i, r) :: jetsOfWord q))) = ∑ᶠ m : ℤ, A m := by
    funext q
    change _ = (LinearMap.proj q : (BoundedWord D n → Fock) →ₗ[ℂ] Fock) (∑ᶠ m, A m)
    rw [map_finsum _ hs]
    simpa only [Finset.sum_apply, Pi.smul_apply, LinearMap.proj_apply] using
      charge_sum_word a (a + b) h p P (jetsOfWord q) r
  simp only [pointedRetainedCoefficient, coeff_retainedSeries, List.singleton_append,
    ← map_smul, ← map_sum, hsum, map_finsum (wordReadout D n a) hs]
  apply finsum_congr
  intro m
  change wordReadout D n a
    (v m • fun q => retainedJetModeReadout (a + b) h p P (jetsOfWord q) (chargeVector a) m) = _
  rw [map_smul, wordReadout_mode]

/-- The differentiated integrated weight of the signed mode at source level `r + 1`. -/
theorem retainedModeWeight
    (r : ℕ) (m : ℤ) :
    ((r + 1 : ℕ) : ℂ) * coeff (r + 1) (integratedNormalMode m) =
      jetWeight ⟨r + 1, Nat.succ_pos r⟩ m := by
  rw [P48qIntegratedNormalMode.coeff_integratedNormalMode_pos m (Nat.succ_pos r)]
  exact mul_div_cancel₀ _ (by exact_mod_cast Nat.succ_ne_zero r)

/-- Point one positive source occurrence while keeping the alphabet fixed at `D`. -/
theorem retainedCoefficient_recurrence
    (D n : ℕ) (hn : n < D) (a b : Charge lattice) (h : ℤ)
    (p : Momentum) (P : Fock) :
    ((n + 1 : ℕ) : ℂ) • retainedCoefficient D (n + 1) a b h p P =
      ∑ r : Fin (n + 1), ∑ᶠ m : ℤ,
        ((((r.1 + 1 : ℕ) : ℂ) * coeff (r.1 + 1) (integratedNormalMode m)) •
          retainedModeShift D (n - r.1) a b h p P m) := by
  rw [retainedCoefficient_derivative D n hn]
  simp only [pointedRetainedCoefficient_charge_sum, retainedModeWeight]

/-- The native diagonal coefficient reads the fixed-cutoff series at `D = n`. -/
theorem nativeRetainedSeries_coeff_eq_retainedCoefficient
    (a b : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock) (d : ℕ) :
    coeff d (nativeRetainedSeries a b h p P d) =
      retainedCoefficient d d a b h p P := rfl

/-- The diagonal coefficient uses the same cutoff on every term of the recurrence. -/
theorem nativeRetainedSeries_recurrence
    (n : ℕ) (a b : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock) :
    ((n + 1 : ℕ) : ℂ) •
        coeff (n + 1) (nativeRetainedSeries a b h p P (n + 1)) =
      ∑ r : Fin (n + 1), ∑ᶠ m : ℤ,
        ((((r.1 + 1 : ℕ) : ℂ) * coeff (r.1 + 1) (integratedNormalMode m)) •
          retainedModeShift (n + 1) (n - r.1) a b h p P m) := by
  rw [nativeRetainedSeries_coeff_eq_retainedCoefficient]
  exact retainedCoefficient_recurrence (n + 1) n (Nat.lt_succ_self n) a b h p P

#print axioms retainedJetModeReadout_hasFiniteSupport
#print axioms retainedJetCoeff_cons_eq_signed_insertion
#print axioms retainedCoefficient_derivative

#print axioms retainedModeShift_hasFiniteSupport
#print axioms pointedRetainedCoefficient_charge_sum
#print axioms retainedCoefficient_recurrence
#print axioms nativeRetainedSeries_recurrence

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qRetainedNormalRecurrence
