/- GID: D5/S3/VertexAlgebra/LatticeAllStateJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeAllStateJacobi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual fields satisfy the full integer Borcherds identity with three finite supports. -/

import D5.S3.VertexAlgebra.LatticeAllStateLocality
import D5.S3.VertexAlgebra.BinomialKernelDelta

/- Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license; the full terms are in this repository root LICENSE.
The pinned supplier tree contains no LICENSE or NOTICE file.
Authors: Scott Carnahan; actual lattice adaptation as documented below. -/
/- Actual lattice residue closure and all-integer Borcherds identity.
The Borcherds finite-sum/Pascal proof is adapted from PolynomialFockJacobi
at immutable bfd9ff0f15397a4fb933f36d701a60d325d84b08,
sha256 4835d521f0adc06d6799a4ef1f72d0936be53abbd3f2bbb666ecf2e6f8aab1fa.
The proof is re-elaborated on the actual carrier, using the generic sealed
StateFieldResidueReconstruction and actual creation/translation/locality.
No Fock theorem or unproved transfer is imported.
Carnahan/native finite coefficient proof attribution is retained in the
original immutable supplier; Matsuo--Nagatomo, Theorem 5.4.1.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace D5.S3.VertexAlgebra.LatticeAllStateJacobi
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open FieldNormalProduct FieldNormalProductLocality
open StateFieldResidueReconstruction (integerBinomial residueCoefficient residueLeft residueRight)
open LatticeAllStateReconstruction
open scoped VertexOperator
noncomputable section
def jacobiLeftTerm (D : LatticeData) (p q r : ℤ) (a b c : Carrier D) (i : ℕ) : Carrier D :=
  integerBinomial p i • mu D (mu D a (r+i) b) (p+q-i) c

def jacobiRightFirstTerm (D : LatticeData) (p q r : ℤ) (a b c : Carrier D) (i : ℕ) : Carrier D :=
  (((-1 : ℂ)^i)*integerBinomial r i) • mu D a (p+r-i) (mu D b (q+i) c)

def jacobiRightSecondTerm (D : LatticeData) (p q r : ℤ) (a b c : Carrier D) (i : ℕ) : Carrier D :=
  (((-1 : ℂ)^i)*integerBinomial r i) • (StateFieldResidueReconstruction.epsilon r • mu D b (q+r-i) (mu D a (p+i) c))

theorem borcherds (D : LatticeData) (a b c : Carrier D) (p q r : ℤ) : Function.HasFiniteSupport (jacobiLeftTerm D p q r a b c) ∧ Function.HasFiniteSupport (jacobiRightFirstTerm D p q r a b c) ∧
  Function.HasFiniteSupport (jacobiRightSecondTerm D p q r a b c) ∧ (∑ᶠ offset : ℕ, jacobiLeftTerm D p q r a b c offset) = ∑ᶠ offset : ℕ, (((-1 : ℂ) ^ offset) * integerBinomial r
  offset) • (mu D a (p + r - offset) (mu D b (q + offset) c) - StateFieldResidueReconstruction.epsilon r • mu D b (q + r - offset) (mu D a (p + offset) c)) := by
  classical
  let discrepancy (first second parameter : ℤ) : Carrier D := (∑ᶠ offset : ℕ, jacobiLeftTerm D first second parameter a b c offset) - (∑ᶠ offset : ℕ, jacobiRightFirstTerm D first second
    parameter a b c offset) + (∑ᶠ offset : ℕ, jacobiRightSecondTerm D first second parameter a b c offset)
  have binomial (value : ℤ → ℤ → Module.End ℂ (Carrier D)) (order : ℕ)
      (first second : ℤ) : ((deltaEnd ^ order) value) first second =
        ∑ offset ∈ Finset.range (order + 1),
          (((-1 : ℂ)^offset) * (order.choose offset : ℂ)) •
            value (first+(order : ℤ)-offset) (second+offset) :=
    FieldDeltaBinomial.delta_binomial value order first second
  obtain ⟨cutoff, localityLaw⟩ := LatticeAllStateLocality.stateField_locality D a b
  have killed : (deltaEnd ^ cutoff) (FieldNormalProductLocality.commutator (Y D a) (Y D b)) = 0 := by
    rw [Module.End.pow_apply]
    exact localityLaw
  have highSeed : ∀ first second parameter : ℤ, (cutoff : ℤ) ≤ parameter → discrepancy first second parameter = 0 := by
    change ∀ first second parameter : ℤ, (cutoff : ℤ) ≤ parameter → (∑ᶠ offset : ℕ, jacobiLeftTerm D first second parameter a b c offset) - (∑ᶠ offset : ℕ, jacobiRightFirstTerm D first
      second parameter a b c offset) + (∑ᶠ offset : ℕ, jacobiRightSecondTerm D first second parameter a b c offset) = 0
    have positiveProduct (degree : ℕ) (p q : ℤ) (vector : Carrier D) : (∑ᶠ offset : ℕ, jacobiRightFirstTerm D p q degree a b vector offset) - (∑ᶠ offset : ℕ, jacobiRightSecondTerm D p q
      degree a b vector offset) = ((deltaEnd ^ degree) (FieldNormalProductLocality.commutator (Y D a) (Y D b))) p q vector := by
      have chooseNat (offset : ℕ) : integerBinomial degree offset = (degree.choose offset : ℂ) := by simp [integerBinomial, Ring.choose_natCast]
      have firstSum : (∑ᶠ offset : ℕ, jacobiRightFirstTerm D p q degree a b vector offset) = ∑ offset ∈ Finset.range (degree + 1), (((-1 : ℂ) ^ offset) * (degree.choose offset : ℂ))
        • ((Y D a) [[p + degree - offset]]) (((Y D b) [[q + offset]]) vector) := by
        unfold jacobiRightFirstTerm  mu; simp_rw [chooseNat]; apply finsum_eq_sum_of_support_subset; intro offset member
        by_contra outside
        have zeroChoose : degree.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
        exact member (by simp [zeroChoose])
      have secondSum : (∑ᶠ offset : ℕ, jacobiRightSecondTerm D p q degree a b vector offset) = StateFieldResidueReconstruction.epsilon degree • ∑ offset ∈ Finset.range (degree + 1), (((-1 : ℂ) ^ offset) *
        (degree.choose offset : ℂ)) • ((Y D b) [[q + degree - offset]]) (((Y D a) [[p + offset]]) vector) := by
        unfold jacobiRightSecondTerm  mu; simp_rw [chooseNat]; rw [Finset.smul_sum]; simp_rw [smul_comm (StateFieldResidueReconstruction.epsilon (degree : ℤ))]
        apply finsum_eq_sum_of_support_subset; intro offset member; by_contra outside
        have zeroChoose : degree.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
        exact member (by simp [zeroChoose])
      rw [firstSum, secondSum, binomial, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, FieldNormalProductLocality.commutator, Module.End.mul_apply, LinearMap.sub_apply, smul_sub, Finset.sum_sub_distrib]
      apply congrArg ((∑ offset ∈ Finset.range (degree + 1), (((-1 : ℂ) ^ offset) * (degree.choose offset : ℂ)) • ((Y D a) [[p + degree - offset]]) (((Y D b) [[q + offset]]) vector)) -
        ·)
      rw [Finset.smul_sum, ← Finset.sum_range_reflect]; apply Finset.sum_congr rfl; intro offset member
      have within : offset ≤ degree := by simpa using Finset.mem_range.mp member
      simp only [Nat.add_sub_cancel, Nat.choose_symm within, smul_smul, StateFieldResidueReconstruction.epsilon, zpow_natCast]
      have signs : (-1 : ℂ) ^ degree * ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ)) = (-1 : ℂ) ^ offset * (degree.choose offset : ℂ) := by
        have split : (-1 : ℂ) ^ degree = (-1 : ℂ) ^ offset * (-1 : ℂ) ^ (degree - offset) := by rw [← pow_add, Nat.add_sub_of_le within]
        rw [split]
        have squared : ((-1 : ℂ) ^ (degree - offset)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        calc
          _ = (-1 : ℂ) ^ offset * (((-1 : ℂ) ^ (degree - offset)) ^ 2) * (degree.choose offset : ℂ) := by ring
          _ = _ := by rw [squared]; ring
      rw [signs]; push_cast [Int.natCast_sub within]
      rw [show q + (degree : ℤ) - ((degree : ℤ) - offset) = q + offset by omega, show p + ((degree : ℤ) - offset) = p + degree - offset by omega]
    have residueProduct (parameter mode : ℤ) (vector : Carrier D) : (((residueField D parameter a b).operator) [[mode]]) vector = (∑ᶠ offset : ℕ, jacobiRightFirstTerm D 0 mode parameter a b
      vector offset) - (∑ᶠ offset : ℕ, jacobiRightSecondTerm D 0 mode parameter a b vector offset) := by
      rw [(residueField D parameter a b).coefficient]
      dsimp only [residueCoefficient, residueLeft, residueRight, jacobiRightFirstTerm, jacobiRightSecondTerm, mu]; simp only [zero_add]
      rw [smul_finsum' (StateFieldResidueReconstruction.epsilon parameter) ((residueField D parameter a b).right_finite mode vector)]; simp_rw [smul_comm (StateFieldResidueReconstruction.epsilon parameter)]
      rw [add_comm parameter mode]
    have residueZero (parameter : ℤ) (high : (cutoff : ℤ) ≤ parameter) : (residueField D parameter a b).operator = 0 := by
      obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ parameter by omega)
      have vanish : (deltaEnd ^ degree) (FieldNormalProductLocality.commutator (Y D a) (Y D b)) = 0 := by
        obtain ⟨extra, equality⟩ := Nat.exists_eq_add_of_le (show cutoff ≤ degree by omega)
        rw [equality, pow_add, (Commute.refl deltaEnd).pow_pow cutoff extra |>.eq, Module.End.mul_apply, killed, map_zero]
      apply HVertexOperator.coeff_inj; funext power; apply LinearMap.ext; intro vector
      rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff, residueProduct, positiveProduct, vanish]
      simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero]
    intro p q r high
    have stateZero (offset : ℕ) : mu D a (r + offset) b = 0 := by
      have closure := residue_closure D a b (r + offset)
      rw [residueZero (r + offset) (by omega)] at closure
      have created := LatticeAllStateField.stateField_creation D (mu D a (r + offset) b)
      rw [closure] at created; simpa only [map_zero, Pi.zero_apply, LinearMap.zero_apply] using created.symm
    have leftZero : (∑ᶠ offset : ℕ, jacobiLeftTerm D p q r a b c offset) = 0 := by apply finsum_eq_zero_of_forall_eq_zero; intro offset; rw [jacobiLeftTerm, stateZero]; simp [mu]
    have rightZero : (∑ᶠ offset : ℕ, jacobiRightFirstTerm D p q r a b c offset) - (∑ᶠ offset : ℕ, jacobiRightSecondTerm D p q r a b c offset) = 0 := by
      obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r by omega); rw [positiveProduct]
      have vanish : (deltaEnd ^ degree) (FieldNormalProductLocality.commutator (Y D a) (Y D b)) = 0 := by
        obtain ⟨extra, equality⟩ := Nat.exists_eq_add_of_le (show cutoff ≤ degree by omega)
        rw [equality, pow_add, (Commute.refl deltaEnd).pow_pow cutoff extra |>.eq, Module.End.mul_apply, killed, map_zero]
      rw [vanish]; rfl
    rw [leftZero, sub_eq_zero.mp rightZero]; abel
  have zeroSeed (q r : ℤ) : discrepancy 0 q r = 0 := by
    change (∑ᶠ offset : ℕ, jacobiLeftTerm D 0 q r a b c offset) - (∑ᶠ offset : ℕ, jacobiRightFirstTerm D 0 q r a b c offset) + (∑ᶠ offset : ℕ, jacobiRightSecondTerm D 0 q r a b c offset)
      = 0
    have left : (∑ᶠ offset : ℕ, jacobiLeftTerm D 0 q r a b c offset) = mu D (mu D a r b) q c := by
      rw [finsum_eq_single _ 0]
      · simp [jacobiLeftTerm, integerBinomial]
      · intro offset different
        simp [jacobiLeftTerm, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero different)]
    have right : mu D (mu D a r b) q c = (∑ᶠ offset : ℕ, jacobiRightFirstTerm D 0 q r a b c offset) - (∑ᶠ offset : ℕ, jacobiRightSecondTerm D 0 q r a b c offset) := by
      change ((Y D (mu D a r b)) [[q]]) c = _; rw [residue_closure, (residueField D r a b).coefficient]
      dsimp only [residueCoefficient, residueLeft, residueRight, jacobiRightFirstTerm, jacobiRightSecondTerm, mu]; simp only [zero_add]
      rw [smul_finsum' (StateFieldResidueReconstruction.epsilon r) ((residueField D r a b).right_finite q c)]; simp_rw [smul_comm (StateFieldResidueReconstruction.epsilon r)]; rw [add_comm r q]
    rw [left, right]; abel
  have recurrence (p q r : ℤ) : discrepancy (p + 1) q r = discrepancy p (q + 1) r + discrepancy p q (r + 1) := by
    let weight (parameter : ℤ) (offset : ℕ) := (-1 : ℂ) ^ offset * integerBinomial parameter offset
    let zeroSucc : Option ℕ ≃ ℕ := {
      toFun value := match value with | none => 0 | some offset => offset + 1
      invFun value := match value with | 0 => none | offset + 1 => some offset
      left_inv value := by cases value <;> rfl
      right_inv value := by cases value <;> rfl }
    have splitSum (term : ℕ → Carrier D) (finite : Function.HasFiniteSupport term) : ∑ᶠ offset : ℕ, term offset = term 0 + ∑ᶠ offset : ℕ, term (offset + 1) := by
      rw [← finsum_comp_equiv zeroSucc, finsum_option]
      · rfl
      · exact finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
    have pascal (parameter : ℤ) (offset : ℕ) : integerBinomial (parameter + 1) (offset + 1) = integerBinomial parameter offset + integerBinomial parameter (offset + 1) := by
      unfold integerBinomial; rw [Ring.choose_succ_succ, Int.cast_add]
    have weightedPascal (parameter : ℤ) (offset : ℕ) : weight (parameter + 1) (offset + 1) = weight parameter (offset + 1) - weight parameter offset := by
      dsimp only [weight]; rw [pascal, pow_succ]; ring
    have chooseZero (parameter : ℤ) : integerBinomial parameter 0 = 1 := by simp [integerBinomial]
    have weightZero (parameter : ℤ) : weight parameter 0 = 1 := by simp [weight, chooseZero]
    have sumPascal (parameter : ℤ) (sequence : ℕ → Carrier D) (finite : Function.HasFiniteSupport sequence) : (∑ᶠ offset : ℕ, integerBinomial (parameter + 1) offset • sequence offset) =
      (∑ᶠ offset : ℕ, integerBinomial parameter offset • sequence offset) + (∑ᶠ offset : ℕ, integerBinomial parameter offset • sequence (offset + 1)) := by
      have tailFinite := finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
      have nextFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          integerBinomial (parameter + 1) offset • sequence offset) :=
        finite.smul_right (integerBinomial (parameter + 1))
      have currentFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          integerBinomial parameter offset • sequence offset) :=
        finite.smul_right (integerBinomial parameter)
      rw [splitSum _ nextFinite, splitSum _ currentFinite]; simp only [chooseZero, one_smul]; simp_rw [pascal, add_smul]
      have firstTail : Function.HasFiniteSupport (fun offset : ℕ =>
          integerBinomial parameter offset • sequence (offset + 1)) :=
        tailFinite.smul_right (integerBinomial parameter)
      have secondTail : Function.HasFiniteSupport (fun offset : ℕ =>
          integerBinomial parameter (offset + 1) • sequence (offset + 1)) :=
        tailFinite.smul_right (fun offset => integerBinomial parameter (offset + 1))
      rw [finsum_add_distrib firstTail secondTail]; abel
    have sumWeightedPascal (parameter : ℤ) (sequence : ℕ → Carrier D) (finite : Function.HasFiniteSupport sequence) : (∑ᶠ offset : ℕ, weight (parameter + 1) offset • sequence offset) =
      (∑ᶠ offset : ℕ, weight parameter offset • sequence offset) - (∑ᶠ offset : ℕ, weight parameter offset • sequence (offset + 1)) := by
      have tailFinite := finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
      have nextFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          weight (parameter + 1) offset • sequence offset) :=
        finite.smul_right (weight (parameter + 1))
      have currentFinite : Function.HasFiniteSupport (fun offset : ℕ =>
          weight parameter offset • sequence offset) := finite.smul_right (weight parameter)
      rw [splitSum _ nextFinite, splitSum _ currentFinite]; simp only [weightZero, one_smul]; simp_rw [weightedPascal, sub_smul]
      have firstTail : Function.HasFiniteSupport (fun offset : ℕ =>
          weight parameter (offset + 1) • sequence (offset + 1)) :=
        tailFinite.smul_right (fun offset => weight parameter (offset + 1))
      have secondTail : Function.HasFiniteSupport (fun offset : ℕ =>
          weight parameter offset • sequence (offset + 1)) :=
        tailFinite.smul_right (weight parameter)
      rw [finsum_sub_distrib firstTail secondTail]; abel
    have firstFinite (start finish : ℤ) : Function.HasFiniteSupport (fun offset : ℕ =>
        mu D (mu D a (r + offset) b) (start + finish - offset) c) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y D a) b)).order - r).toNat, ?_⟩; intro offset member
      contrapose! member
      rw [Function.notMem_support]
      have vanish : mu D a (r + offset) b = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      rw [vanish]; simp [mu]
    have secondFinite (start finish parameter : ℤ) : Function.HasFiniteSupport (fun offset : ℕ =>
        mu D a (start + parameter - offset) (mu D b (finish + offset) c)) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y D b) c)).order - finish).toNat, ?_⟩
      intro offset member
      contrapose! member
      rw [Function.notMem_support]
      have vanish : mu D b (finish + offset) c = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      rw [vanish]; simp [mu]
    have thirdFinite (start finish parameter : ℤ) : Function.HasFiniteSupport (fun offset : ℕ =>
        mu D b (finish + parameter - offset) (mu D a (start + offset) c)) := by
      refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y D a) c)).order - start).toNat, ?_⟩
      intro offset member
      contrapose! member
      rw [Function.notMem_support]
      have vanish : mu D a (start + offset) c = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
      rw [vanish]; simp [mu]
    have leftLaw : (∑ᶠ offset : ℕ, jacobiLeftTerm D (p + 1) q r a b c offset) = (∑ᶠ offset : ℕ, jacobiLeftTerm D p (q + 1) r a b c offset) + (∑ᶠ offset : ℕ, jacobiLeftTerm D p q (r + 1)
      a b c offset) := by
      let sequence (offset : ℕ) := mu D (mu D a (r + offset) b) (p + 1 + q - offset) c
      have initial (offset : ℕ) : jacobiLeftTerm D (p + 1) q r a b c offset = integerBinomial (p + 1) offset • sequence offset := by rfl
      have current (offset : ℕ) : jacobiLeftTerm D p (q + 1) r a b c offset = integerBinomial p offset • sequence offset := by
        dsimp only [jacobiLeftTerm, sequence]; rw [show p + (q + 1) - (offset : ℤ) = p + 1 + q - offset by omega]
      have shifted (offset : ℕ) : jacobiLeftTerm D p q (r + 1) a b c offset = integerBinomial p offset • sequence (offset + 1) := by
        dsimp only [jacobiLeftTerm, sequence]; push_cast
        rw [show r + ((offset : ℤ) + 1) = r + 1 + offset by omega, show p + 1 + q - ((offset : ℤ) + 1) = p + q - offset by omega]
      simp_rw [initial, current, shifted]; exact sumPascal p sequence (firstFinite (p + 1) q)
    have firstRightLaw : (∑ᶠ offset : ℕ, jacobiRightFirstTerm D (p + 1) q r a b c offset) = (∑ᶠ offset : ℕ, jacobiRightFirstTerm D p (q + 1) r a b c offset) + (∑ᶠ offset : ℕ,
      jacobiRightFirstTerm D p q (r + 1) a b c offset) := by
      let sequence (offset : ℕ) := mu D a (p + (r + 1) - offset) (mu D b (q + offset) c)
      have initial (offset : ℕ) : jacobiRightFirstTerm D (p + 1) q r a b c offset = weight r offset • sequence offset := by
        dsimp only [jacobiRightFirstTerm, weight, sequence]; rw [show p + 1 + r = p + (r + 1) by omega]
      have current (offset : ℕ) : jacobiRightFirstTerm D p q (r + 1) a b c offset = weight (r + 1) offset • sequence offset := by rfl
      have shifted (offset : ℕ) : jacobiRightFirstTerm D p (q + 1) r a b c offset = weight r offset • sequence (offset + 1) := by
        dsimp only [jacobiRightFirstTerm, weight, sequence]; push_cast
        rw [show p + (r + 1) - ((offset : ℤ) + 1) = p + r - offset by omega, show q + ((offset : ℤ) + 1) = q + 1 + offset by omega]
      simp_rw [initial, current, shifted]; exact sub_eq_iff_eq_add'.mp (sumWeightedPascal r sequence (secondFinite p q (r + 1))).symm
    have sign : StateFieldResidueReconstruction.epsilon (r + 1) = -StateFieldResidueReconstruction.epsilon r := by rw [StateFieldResidueReconstruction.epsilon, StateFieldResidueReconstruction.epsilon, zpow_add₀ (by norm_num)]; norm_num
    have secondRightLaw : (∑ᶠ offset : ℕ, jacobiRightSecondTerm D (p + 1) q r a b c offset) = (∑ᶠ offset : ℕ, jacobiRightSecondTerm D p (q + 1) r a b c offset) + (∑ᶠ offset : ℕ,
      jacobiRightSecondTerm D p q (r + 1) a b c offset) := by
      let sequence (offset : ℕ) := mu D b (q + (r + 1) - offset) (mu D a (p + offset) c)
      have initial (offset : ℕ) : jacobiRightSecondTerm D p (q + 1) r a b c offset = StateFieldResidueReconstruction.epsilon r • (weight r offset • sequence offset) := by
        dsimp only [jacobiRightSecondTerm, weight, sequence]; rw [show q + 1 + r = q + (r + 1) by omega, smul_comm]
      have current (offset : ℕ) : jacobiRightSecondTerm D p q (r + 1) a b c offset = -StateFieldResidueReconstruction.epsilon r • (weight (r + 1) offset • sequence offset) := by
        dsimp only [jacobiRightSecondTerm, weight, sequence]; rw [sign, smul_comm]
      have shifted (offset : ℕ) : jacobiRightSecondTerm D (p + 1) q r a b c offset = StateFieldResidueReconstruction.epsilon r • (weight r offset • sequence (offset + 1)) := by
        dsimp only [jacobiRightSecondTerm, weight, sequence]; push_cast
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
  have leftSupport : Function.HasFiniteSupport (jacobiLeftTerm D p q r a b c) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y D a) b)).order - r).toNat, ?_⟩; intro offset member
    contrapose! member
    rw [Function.notMem_support]
    have vanish : mu D a (r + offset) b = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
    dsimp only [jacobiLeftTerm]; rw [vanish]; simp [mu]
  have firstSupport : Function.HasFiniteSupport (jacobiRightFirstTerm D p q r a b c) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y D b) c)).order - q).toNat, ?_⟩; intro offset member
    contrapose! member
    rw [Function.notMem_support]
    have vanish : mu D b (q + offset) c = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
    dsimp only [jacobiRightFirstTerm]; rw [vanish]; simp [mu]
  have secondSupport : Function.HasFiniteSupport (jacobiRightSecondTerm D p q r a b c) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_); refine ⟨(-((HahnModule.of ℂ).symm ((Y D a) c)).order - p).toNat, ?_⟩; intro offset member
    contrapose! member
    rw [Function.notMem_support]
    have vanish : mu D a (p + offset) c = 0 := by apply VertexOperator.ncoeff_eq_zero_of_lt_order; omega
    dsimp only [jacobiRightSecondTerm]; rw [vanish]; simp [mu]
  refine ⟨leftSupport, firstSupport, secondSupport, ?_⟩; simp_rw [smul_sub]
  change (∑ᶠ offset : ℕ, jacobiLeftTerm D p q r a b c offset) = ∑ᶠ offset : ℕ, (jacobiRightFirstTerm D p q r a b c offset - jacobiRightSecondTerm D p q r a b c offset)
  rw [finsum_sub_distrib firstSupport secondSupport]
  have law := allIndices p q r
  change (∑ᶠ offset : ℕ, jacobiLeftTerm D p q r a b c offset) - (∑ᶠ offset : ℕ, jacobiRightFirstTerm D p q r a b c offset) + (∑ᶠ offset : ℕ, jacobiRightSecondTerm D p q r a b c offset) =
    0 at law
  apply sub_eq_zero.mp
  calc
    _ = (∑ᶠ offset : ℕ, jacobiLeftTerm D p q r a b c offset) - (∑ᶠ offset : ℕ, jacobiRightFirstTerm D p q r a b c offset) + (∑ᶠ offset : ℕ, jacobiRightSecondTerm D p q r a b c offset) :=
      by abel
    _ = 0 := law


end
end D5.S3.VertexAlgebra.LatticeAllStateJacobi
