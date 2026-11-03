/- GID: D5/S3/Quantum/Fermionic/BcGhostBorcherds
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostBorcherds
   mirror-E: none(waiver:algebraic-ghost-borcherds)
   anchors: []
   utility: none
   digest: Full signed all-integer Borcherds identity on the original occupation ghost carrier. -/

/- Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
The finite coefficient and Pascal argument adapts LatticeAllStateJacobi and
its attributed PolynomialFockJacobi supplier, using the actual signed ghost
iterate and locality laws. The original vertexAlg source is
ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea,
VertexAlg/VertexBasic/VertexOperator.lean. See Matsuo--Nagatomo,
hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1.
-/

/-
proof_shape: borcherds: content
escape_witness: The signed positive delta expansion, the actual pointwise
truncation seed and the supported three-index Pascal recurrence propagate
the signed iterate seed to every integer triple, including negative indices.
admission_basis: escape-witness
-/

import D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate
import D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
import D5.S3.VertexAlgebra.BinomialKernelDelta

/-! Full signed three-index identity for the original ghost fields. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostStateField
open D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
open D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate
open D5.S3.VertexAlgebra.FieldNormalProduct
open D5.S3.VertexAlgebra.FieldNormalProductLocality
open D5.S3.VertexAlgebra.StateFieldResidueReconstruction (integerBinomial epsilon)
open D5.S3.VertexAlgebra.FieldDeltaBinomial
open D5.S3.VertexAlgebra.BinomialKernelDelta

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostBorcherds

private abbrev mu (a : Fock) (n : ℤ) (b : Fock) : Fock :=
  ((BcGhostStateField.Y a) [[n]]) b

def jacobiLeftTerm (p q r : ℤ) (a b c : Fock) (i : ℕ) : Fock :=
  integerBinomial p i • mu (mu a (r+i) b) (p+q-i) c

def jacobiRightFirstTerm (p q r : ℤ) (a b c : Fock) (i : ℕ) : Fock :=
  (((-1 : ℂ)^i)*integerBinomial r i) • mu a (p+r-i) (mu b (q+i) c)

def jacobiRightSecondTerm (s : ℂ) (p q r : ℤ) (a b c : Fock) (i : ℕ) : Fock :=
  (((-1 : ℂ)^i)*integerBinomial r i) •
    (epsilon r * s) • mu b (q+r-i) (mu a (p+i) c)

private def signedCommutator (s : ℂ) (A B : VertexOperator ℂ Fock) :
    ℤ → ℤ → Module.End ℂ Fock := fun m n =>
  (A [[m]]) * (B [[n]]) - s • ((B [[n]]) * (A [[m]]))

/- The discrepancy, high-r seed, and integer Pascal recurrence below are the
   concrete signed adaptation of the pinned LatticeAllStateJacobi finite-sum
   proof.  The m = 0 seed is supplied by the native signed iterate theorem;
   high r uses this actual pointwise truncation bound together with signed
   locality, so no private residue-field constructor is used here. -/
set_option maxHeartbeats 4000000 in
theorem borcherds (a b c : Fock) (pa pb : ℕ)
    (ha : parity a = (-1 : ℂ) ^ pa • a)
    (hb : parity b = (-1 : ℂ) ^ pb • b) (p q r : ℤ) :
    Function.HasFiniteSupport (jacobiLeftTerm p q r a b c) ∧
    Function.HasFiniteSupport (jacobiRightFirstTerm p q r a b c) ∧
    Function.HasFiniteSupport (jacobiRightSecondTerm ((-1 : ℂ) ^ (pa*pb)) p q r a b c) ∧
    (∑ᶠ offset : ℕ, jacobiLeftTerm p q r a b c offset) =
      ∑ᶠ offset : ℕ,
        (((-1 : ℂ)^offset) * integerBinomial r offset) •
          (mu a (p+r-offset) (mu b (q+offset) c) -
            (epsilon r * ((-1 : ℂ) ^ (pa*pb))) •
              mu b (q+r-offset) (mu a (p+offset) c)) :=
by
  classical
  let superSign : ℂ := (-1 : ℂ) ^ (pa * pb)
  let discrepancy (first second parameter : ℤ) : Fock := (∑ᶠ offset : ℕ, jacobiLeftTerm first second parameter a b c offset) - (∑ᶠ offset : ℕ, jacobiRightFirstTerm first second
    parameter a b c offset) + (∑ᶠ offset : ℕ, jacobiRightSecondTerm superSign first second parameter a b c offset)
  have binomial (value : ℤ → ℤ → Module.End ℂ (Fock)) (order : ℕ)
      (first second : ℤ) : ((deltaEnd ^ order) value) first second =
        ∑ offset ∈ Finset.range (order + 1),
          (((-1 : ℂ)^offset) * (order.choose offset : ℂ)) •
            value (first+(order : ℤ)-offset) (second+offset) :=
    D5.S3.VertexAlgebra.FieldDeltaBinomial.delta_binomial value order first second
  obtain ⟨localityOrder, localityLaw⟩ := stateField_locality a b pa pb ha hb
  let supportCutoff : ℕ := (-((HahnModule.of ℂ).symm ((Y a) b)).order).toNat
  let cutoff : ℕ := localityOrder + supportCutoff
  have killedLocal : (deltaEnd ^ localityOrder) (signedCommutator superSign (Y a) (Y b)) = 0 := by
    rw [Module.End.pow_apply]
    change delta^[localityOrder] (fun m n =>
      ((Y a) [[m]]) * ((Y b) [[n]]) - ((-1 : ℂ) ^ (pa * pb)) •
        (((Y b) [[n]]) * ((Y a) [[m]]))) = 0
    exact localityLaw
  have highSeed : ∀ first second parameter : ℤ, (cutoff : ℤ) ≤ parameter →
      discrepancy first second parameter = 0 := by
    change ∀ first second parameter : ℤ, (cutoff : ℤ) ≤ parameter →
      (∑ᶠ offset : ℕ, jacobiLeftTerm first second parameter a b c offset) -
        (∑ᶠ offset : ℕ, jacobiRightFirstTerm first second parameter a b c offset) +
        (∑ᶠ offset : ℕ, jacobiRightSecondTerm superSign first second parameter a b c offset) = 0
    have positiveProduct (degree : ℕ) (first second : ℤ) (vector : Fock) :
        (∑ᶠ offset : ℕ, jacobiRightFirstTerm first second degree a b vector offset) -
          (∑ᶠ offset : ℕ, jacobiRightSecondTerm superSign first second degree a b vector offset) =
            ((deltaEnd ^ degree) (signedCommutator superSign (Y a) (Y b))) first second vector := by
      have chooseNat (offset : ℕ) : integerBinomial degree offset = (degree.choose offset : ℂ) := by
        simp [integerBinomial, Ring.choose_natCast]
      have firstSum : (∑ᶠ offset : ℕ, jacobiRightFirstTerm first second degree a b vector offset) =
          ∑ offset ∈ Finset.range (degree + 1),
            (((-1 : ℂ) ^ offset) * (degree.choose offset : ℂ)) •
              ((Y a) [[first + degree - offset]]) (((Y b) [[second + offset]]) vector) := by
        unfold jacobiRightFirstTerm mu
        simp_rw [chooseNat]
        apply finsum_eq_sum_of_support_subset
        intro offset member
        by_contra outside
        have zeroChoose : degree.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
        exact member (by simp [zeroChoose])
      have secondSum : (∑ᶠ offset : ℕ, jacobiRightSecondTerm superSign first second degree a b vector offset) =
          (epsilon (degree : ℤ) * superSign) •
            ∑ offset ∈ Finset.range (degree + 1),
              (((-1 : ℂ) ^ offset) * (degree.choose offset : ℂ)) •
                ((Y b) [[second + degree - offset]]) (((Y a) [[first + offset]]) vector) := by
        unfold jacobiRightSecondTerm mu
        simp_rw [chooseNat]
        rw [Finset.smul_sum]
        simp_rw [smul_comm (epsilon (degree : ℤ) * superSign)]
        apply finsum_eq_sum_of_support_subset
        intro offset member
        by_contra outside
        have zeroChoose : degree.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
        exact member (by simp [zeroChoose])
      rw [firstSum, secondSum, binomial, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, signedCommutator, Module.End.mul_apply,
        LinearMap.sub_apply, smul_sub, Finset.sum_sub_distrib]
      apply congrArg (fun z : Fock =>
        (∑ offset ∈ Finset.range (degree + 1),
          (((-1 : ℂ) ^ offset) * (degree.choose offset : ℂ)) •
            ((Y a) [[first + degree - offset]]) (((Y b) [[second + offset]]) vector)) -
          z)
      rw [Finset.smul_sum, ← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro offset member
      have within : offset ≤ degree := by simpa using Finset.mem_range.mp member
      simp only [Nat.add_sub_cancel, Nat.choose_symm within, smul_smul, epsilon,
        zpow_natCast]
      have signs : (-1 : ℂ) ^ degree *
          ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ)) =
            (-1 : ℂ) ^ offset * (degree.choose offset : ℂ) := by
        have split : (-1 : ℂ) ^ degree =
            (-1 : ℂ) ^ offset * (-1 : ℂ) ^ (degree - offset) := by
          rw [← pow_add, Nat.add_sub_of_le within]
        rw [split]
        have squared : ((-1 : ℂ) ^ (degree - offset)) ^ 2 = 1 := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        calc
          _ = (-1 : ℂ) ^ offset * (((-1 : ℂ) ^ (degree - offset)) ^ 2) *
              (degree.choose offset : ℂ) := by ring
          _ = _ := by rw [squared]; ring
      have signedSigns : ((-1 : ℂ) ^ degree * superSign) *
          ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ)) =
          ((-1 : ℂ) ^ offset * (degree.choose offset : ℂ)) * superSign := by
        calc
          _ = superSign * ((-1 : ℂ) ^ degree *
              ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ))) := by ring
          _ = _ := by rw [signs]; ring
      rw [signedSigns]
      push_cast [Int.natCast_sub within]
      rw [show second + (degree : ℤ) - ((degree : ℤ) - offset) = second + offset by omega,
        show first + ((degree : ℤ) - offset) = first + degree - offset by omega]
    intro first second parameter high
    have stateZero (offset : ℕ) : mu a (parameter + offset) b = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      have hbound : (supportCutoff : ℤ) ≤ parameter := by
        dsimp [cutoff, supportCutoff] at high ⊢
        omega
      dsimp [supportCutoff] at hbound
      omega
    have leftZero : (∑ᶠ offset : ℕ, jacobiLeftTerm first second parameter a b c offset) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro offset
      rw [jacobiLeftTerm, stateZero]
      simp [mu]
    have rightZero : (∑ᶠ offset : ℕ, jacobiRightFirstTerm first second parameter a b c offset) -
        (∑ᶠ offset : ℕ, jacobiRightSecondTerm superSign first second parameter a b c offset) = 0 := by
      obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ parameter by dsimp [cutoff] at high; omega)
      rw [positiveProduct]
      have vanish : (deltaEnd ^ degree) (signedCommutator superSign (Y a) (Y b)) = 0 := by
        obtain ⟨extra, equality⟩ := Nat.exists_eq_add_of_le (show localityOrder ≤ degree by omega)
        rw [equality, pow_add, (Commute.refl deltaEnd).pow_pow localityOrder extra |>.eq,
          Module.End.mul_apply, killedLocal, map_zero]
      rw [vanish]
      rfl
    rw [leftZero, sub_eq_zero.mp rightZero]
    abel
  have zeroSeed (q r : ℤ) : discrepancy 0 q r = 0 := by
    change (∑ᶠ offset : ℕ, jacobiLeftTerm 0 q r a b c offset) -
        (∑ᶠ offset : ℕ, jacobiRightFirstTerm 0 q r a b c offset) +
        (∑ᶠ offset : ℕ, jacobiRightSecondTerm superSign 0 q r a b c offset) = 0
    have left : (∑ᶠ offset : ℕ, jacobiLeftTerm 0 q r a b c offset) = mu (mu a r b) q c := by
      rw [finsum_eq_single _ 0]
      · simp [jacobiLeftTerm, integerBinomial]
      · intro offset different
        simp [jacobiLeftTerm, integerBinomial,
          Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero different)]
    have iterate := stateField_iterate a b c pa pb ha hb r q
    dsimp at iterate
    obtain ⟨leftFinite, rightFinite, iterateLaw⟩ := iterate
    have secondRewrite :
        (∑ᶠ offset : ℕ, jacobiRightSecondTerm superSign 0 q r a b c offset) =
          (epsilon r * superSign) •
            (∑ᶠ offset : ℕ,
              (((-1 : ℂ) ^ offset) * integerBinomial r offset) •
                ((Y b) [[q + r - (offset : ℤ)]])
                  (((Y a) [[(offset : ℤ)]]) c)) := by
      have rightFinite' : Function.HasFiniteSupport (fun offset : ℕ =>
          (((-1 : ℂ) ^ offset) * integerBinomial r offset) •
            ((Y b) [[q + r - (offset : ℤ)]]) (((Y a) [[(offset : ℤ)]]) c)) := by
        simpa only [integerBinomial, add_comm r q] using rightFinite
      rw [smul_finsum' (epsilon r * superSign) rightFinite']
      apply finsum_congr
      intro offset
      simp only [jacobiRightSecondTerm, mu, zero_add]
      exact smul_comm _ _ _
    have right : mu (mu a r b) q c =
        (∑ᶠ offset : ℕ, jacobiRightFirstTerm 0 q r a b c offset) -
          (∑ᶠ offset : ℕ, jacobiRightSecondTerm superSign 0 q r a b c offset) := by
      rw [secondRewrite]
      simpa [jacobiRightFirstTerm, mu, superSign, integerBinomial, epsilon, add_comm r q] using iterateLaw
    rw [left, right]
    abel
  have recurrence (p q r : ℤ) : discrepancy (p + 1) q r = discrepancy p (q + 1) r + discrepancy p q (r + 1) := by
    let weight (parameter : ℤ) (offset : ℕ) := (-1 : ℂ) ^ offset * integerBinomial parameter offset
    have pascal (parameter : ℤ) (offset : ℕ) : integerBinomial (parameter + 1) (offset + 1) = integerBinomial parameter offset + integerBinomial parameter (offset + 1) := by
      unfold integerBinomial; rw [Ring.choose_succ_succ, Int.cast_add]
    have weightedPascal (parameter : ℤ) (offset : ℕ) : weight (parameter + 1) (offset + 1) = weight parameter (offset + 1) - weight parameter offset := by
      exact chooseSign_pascal parameter offset
    have chooseZero (parameter : ℤ) : integerBinomial parameter 0 = 1 := by simp [integerBinomial]
    have weightZero (parameter : ℤ) : weight parameter 0 = 1 := by simp [weight, chooseZero]
    have sumPascal (parameter : ℤ) (sequence : ℕ → Fock) (finite : Function.HasFiniteSupport sequence) : (∑ᶠ offset : ℕ, integerBinomial (parameter + 1) offset • sequence offset) =
      (∑ᶠ offset : ℕ, integerBinomial parameter offset • sequence offset) + (∑ᶠ offset : ℕ, integerBinomial parameter offset • sequence (offset + 1)) := by
      have tailFinite := finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
      have nextFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          integerBinomial (parameter + 1) offset • sequence offset) :=
        finite.smul_right (integerBinomial (parameter + 1))
      have currentFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          integerBinomial parameter offset • sequence offset) :=
        finite.smul_right (integerBinomial parameter)
      rw [finsum_split _ nextFinite, finsum_split _ currentFinite]; simp only [chooseZero, one_smul]; simp_rw [pascal, add_smul]
      have firstTail : Function.HasFiniteSupport (fun offset : ℕ =>
          integerBinomial parameter offset • sequence (offset + 1)) :=
        tailFinite.smul_right (integerBinomial parameter)
      have secondTail : Function.HasFiniteSupport (fun offset : ℕ =>
          integerBinomial parameter (offset + 1) • sequence (offset + 1)) :=
        tailFinite.smul_right (fun offset => integerBinomial parameter (offset + 1))
      rw [finsum_add_distrib firstTail secondTail]; abel
    have sumWeightedPascal (parameter : ℤ) (sequence : ℕ → Fock) (finite : Function.HasFiniteSupport sequence) : (∑ᶠ offset : ℕ, weight (parameter + 1) offset • sequence offset) =
      (∑ᶠ offset : ℕ, weight parameter offset • sequence offset) - (∑ᶠ offset : ℕ, weight parameter offset • sequence (offset + 1)) := by
      have tailFinite := finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
      have nextFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          weight (parameter + 1) offset • sequence offset) :=
        finite.smul_right (weight (parameter + 1))
      have currentFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          weight parameter offset • sequence offset) := finite.smul_right (weight parameter)
      rw [finsum_split _ nextFinite, finsum_split _ currentFinite]; simp only [weightZero, one_smul]; simp_rw [weightedPascal, sub_smul]
      have firstTail : Function.HasFiniteSupport (fun offset : ℕ =>
          weight parameter (offset + 1) • sequence (offset + 1)) :=
        tailFinite.smul_right (fun offset => weight parameter (offset + 1))
      have secondTail : Function.HasFiniteSupport (fun offset : ℕ =>
          weight parameter offset • sequence (offset + 1)) :=
        tailFinite.smul_right (weight parameter)
      rw [finsum_sub_distrib firstTail secondTail]; abel
    have firstFinite (start finish : ℤ) : Function.HasFiniteSupport (fun offset : ℕ =>
        mu (mu a (r + offset) b) (start + finish - offset) c) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y a) b)).order - r).toNat, ?_⟩; intro offset member
      contrapose! member
      rw [Function.notMem_support]
      have vanish : mu a (r + offset) b = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      rw [vanish]; simp [mu]
    have secondFinite (start finish parameter : ℤ) : Function.HasFiniteSupport (fun offset : ℕ =>
        mu a (start + parameter - offset) (mu b (finish + offset) c)) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y b) c)).order - finish).toNat, ?_⟩
      intro offset member
      contrapose! member
      rw [Function.notMem_support]
      have vanish : mu b (finish + offset) c = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      rw [vanish]; simp [mu]
    have thirdFinite (start finish parameter : ℤ) : Function.HasFiniteSupport (fun offset : ℕ =>
        mu b (finish + parameter - offset) (mu a (start + offset) c)) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y a) c)).order - start).toNat, ?_⟩
      intro offset member
      contrapose! member
      rw [Function.notMem_support]
      have vanish : mu a (start + offset) c = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      rw [vanish]; simp [mu]
    have leftLaw : (∑ᶠ offset : ℕ, jacobiLeftTerm (p + 1) q r a b c offset) = (∑ᶠ offset : ℕ, jacobiLeftTerm p (q + 1) r a b c offset) + (∑ᶠ offset : ℕ, jacobiLeftTerm p q (r + 1)
      a b c offset) := by
      let sequence (offset : ℕ) := mu (mu a (r + offset) b) (p + 1 + q - offset) c
      have initial (offset : ℕ) : jacobiLeftTerm (p + 1) q r a b c offset = integerBinomial (p + 1) offset • sequence offset := by rfl
      have current (offset : ℕ) : jacobiLeftTerm p (q + 1) r a b c offset = integerBinomial p offset • sequence offset := by
        dsimp only [jacobiLeftTerm, sequence]; rw [show p + (q + 1) - (offset : ℤ) = p + 1 + q - offset by omega]
      have shifted (offset : ℕ) : jacobiLeftTerm p q (r + 1) a b c offset = integerBinomial p offset • sequence (offset + 1) := by
        dsimp only [jacobiLeftTerm, sequence]; push_cast
        rw [show r + ((offset : ℤ) + 1) = r + 1 + offset by omega, show p + 1 + q - ((offset : ℤ) + 1) = p + q - offset by omega]
      simp_rw [initial, current, shifted]; exact sumPascal p sequence (firstFinite (p + 1) q)
    have firstRightLaw : (∑ᶠ offset : ℕ, jacobiRightFirstTerm (p + 1) q r a b c offset) = (∑ᶠ offset : ℕ, jacobiRightFirstTerm p (q + 1) r a b c offset) + (∑ᶠ offset : ℕ,
      jacobiRightFirstTerm p q (r + 1) a b c offset) := by
      let sequence (offset : ℕ) := mu a (p + (r + 1) - offset) (mu b (q + offset) c)
      have initial (offset : ℕ) : jacobiRightFirstTerm (p + 1) q r a b c offset = weight r offset • sequence offset := by
        dsimp only [jacobiRightFirstTerm, weight, sequence]; rw [show p + 1 + r = p + (r + 1) by omega]
      have current (offset : ℕ) : jacobiRightFirstTerm p q (r + 1) a b c offset = weight (r + 1) offset • sequence offset := by rfl
      have shifted (offset : ℕ) : jacobiRightFirstTerm p (q + 1) r a b c offset = weight r offset • sequence (offset + 1) := by
        dsimp only [jacobiRightFirstTerm, weight, sequence]; push_cast
        rw [show p + (r + 1) - ((offset : ℤ) + 1) = p + r - offset by omega, show q + ((offset : ℤ) + 1) = q + 1 + offset by omega]
      simp_rw [initial, current, shifted]; exact sub_eq_iff_eq_add'.mp (sumWeightedPascal r sequence (secondFinite p q (r + 1))).symm
    have sign : epsilon (r + 1) = -epsilon r := by rw [epsilon, epsilon, zpow_add₀ (by norm_num)]; norm_num
    have secondRightLaw : (∑ᶠ offset : ℕ, jacobiRightSecondTerm superSign (p + 1) q r a b c offset) = (∑ᶠ offset : ℕ, jacobiRightSecondTerm superSign p (q + 1) r a b c offset) + (∑ᶠ offset : ℕ,
      jacobiRightSecondTerm superSign p q (r + 1) a b c offset) := by
      let sequence (offset : ℕ) := mu b (q + (r + 1) - offset) (mu a (p + offset) c)
      have initial (offset : ℕ) : jacobiRightSecondTerm superSign p (q + 1) r a b c offset = (epsilon r * superSign) • (weight r offset • sequence offset) := by
        dsimp only [jacobiRightSecondTerm, weight, sequence, superSign]; rw [show q + 1 + r = q + (r + 1) by omega, smul_comm]
      have current (offset : ℕ) : jacobiRightSecondTerm superSign p q (r + 1) a b c offset = -(epsilon r * superSign) • (weight (r + 1) offset • sequence offset) := by
        dsimp only [jacobiRightSecondTerm, weight, sequence, superSign]; rw [sign, smul_comm, neg_mul]
      have shifted (offset : ℕ) : jacobiRightSecondTerm superSign (p + 1) q r a b c offset = (epsilon r * superSign) • (weight r offset • sequence (offset + 1)) := by
        dsimp only [jacobiRightSecondTerm, weight, sequence, superSign]; push_cast
        rw [show q + (r + 1) - ((offset : ℤ) + 1) = q + r - offset by omega, show p + ((offset : ℤ) + 1) = p + 1 + offset by omega, smul_comm]
      simp_rw [initial, current, shifted, ← smul_finsum]; rw [sumWeightedPascal r sequence (thirdFinite p q (r + 1))]; module
    unfold discrepancy; rw [leftLaw, firstRightLaw, secondRightLaw]; abel
  have allIndices : ∀ p q r : ℤ, discrepancy p q r = 0 := by
    have positive (degree : ℕ) : ∀ q r : ℤ, discrepancy degree q r = 0 := by
      induction degree with
      | zero => exact zeroSeed
      | succ degree inductionHypothesis =>
        intro q r; rw [Nat.cast_add, Nat.cast_one, recurrence, inductionHypothesis, inductionHypothesis, add_zero]
    have negative (distance : ℕ) : ∀ magnitude : ℕ, ∀ q : ℤ, discrepancy (-(magnitude : ℤ)) q ((cutoff : ℤ) - distance) = 0 := by
      induction distance with
      | zero =>
        intro magnitude q; exact highSeed _ _ _ (by omega)
      | succ distance outerHypothesis =>
        intro magnitude
        induction magnitude with
        | zero => intro q; exact zeroSeed _ _
        | succ magnitude innerHypothesis =>
          intro q
          have law := recurrence (-((magnitude + 1 : ℕ) : ℤ)) (q - 1) ((cutoff : ℤ) - (distance + 1 : ℕ))
          rw [show -((magnitude + 1 : ℕ) : ℤ) + 1 = -(magnitude : ℤ) by omega, show q - 1 + 1 = q by omega, show (cutoff : ℤ) - (distance + 1 : ℕ) + 1 = (cutoff : ℤ) - distance by
            omega, innerHypothesis, outerHypothesis, add_zero] at law
          exact law.symm
    intro p q r
    by_cases nonnegative : 0 ≤ p
    · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
      exact positive degree q r
    · by_cases high : (cutoff : ℤ) ≤ r
      · exact highSeed p q r high
      · let magnitude := (-p).toNat
        let distance := ((cutoff : ℤ) - r).toNat
        have pEquality : p = -(magnitude : ℤ) := by dsimp [magnitude]; omega
        have rEquality : r = (cutoff : ℤ) - distance := by dsimp [distance]; omega
        rw [pEquality, rEquality]; exact negative distance magnitude q
  have leftSupport : Function.HasFiniteSupport (jacobiLeftTerm p q r a b c) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y a) b)).order - r).toNat, ?_⟩; intro offset member
    contrapose! member
    rw [Function.notMem_support]
    have vanish : mu a (r + offset) b = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
    dsimp only [jacobiLeftTerm]; rw [vanish]; simp [mu]
  have firstSupport : Function.HasFiniteSupport (jacobiRightFirstTerm p q r a b c) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y b) c)).order - q).toNat, ?_⟩; intro offset member
    contrapose! member
    rw [Function.notMem_support]
    have vanish : mu b (q + offset) c = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
    dsimp only [jacobiRightFirstTerm]; rw [vanish]; simp [mu]
  have secondSupport : Function.HasFiniteSupport (jacobiRightSecondTerm superSign p q r a b c) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y a) c)).order - p).toNat, ?_⟩; intro offset member
    contrapose! member
    rw [Function.notMem_support]
    have vanish : mu a (p + offset) c = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
    dsimp only [jacobiRightSecondTerm]; rw [vanish]; simp [mu]
  refine ⟨leftSupport, firstSupport, secondSupport, ?_⟩; simp_rw [smul_sub]
  change (∑ᶠ offset : ℕ, jacobiLeftTerm p q r a b c offset) = ∑ᶠ offset : ℕ, (jacobiRightFirstTerm p q r a b c offset - jacobiRightSecondTerm superSign p q r a b c offset)
  rw [finsum_sub_distrib firstSupport secondSupport]
  have law := allIndices p q r
  change (∑ᶠ offset : ℕ, jacobiLeftTerm p q r a b c offset) - (∑ᶠ offset : ℕ, jacobiRightFirstTerm p q r a b c offset) + (∑ᶠ offset : ℕ, jacobiRightSecondTerm superSign p q r a b c offset) =
    0 at law
  apply sub_eq_zero.mp
  calc
    _ = (∑ᶠ offset : ℕ, jacobiLeftTerm p q r a b c offset) - (∑ᶠ offset : ℕ, jacobiRightFirstTerm p q r a b c offset) + (∑ᶠ offset : ℕ, jacobiRightSecondTerm superSign p q r a b c offset) :=
      by abel
    _ = 0 := law


end D5.S3.Quantum.Fermionic.BcGhostBorcherds
end
