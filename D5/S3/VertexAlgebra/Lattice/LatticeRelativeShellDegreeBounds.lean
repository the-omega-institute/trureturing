/- GID: D5/S3/VertexAlgebra/Lattice/LatticeRelativeShellDegreeBounds
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeRelativeShellDegreeBounds
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Original relative mass-shell coefficients have bounded signed null-frame degree. -/

import D5.S3.Quantum.Fermionic.BcGhostQuartetCount
import D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeMassShell

/-! A coefficient bound on the literal original relative mass shell, obtained
through the actual tensor representation and null-frame polynomial substitution. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.LatticeRelativeShellDegreeBounds

open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostCharge
open D5.S3.Quantum.Fermionic.BcGhostQuartetCount (count)
open D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
  (relativeEnergy relativeEnergy_split relativeEnergy_nonneg siteEnergy
    siteEnergy_pos_of_ne_one_three)
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticePositiveEnergy
open D5.S3.VertexAlgebra.LatticeRelativeMassShell
open D5.S3.VertexAlgebra.LatticeLightConeCoordinates
open D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame
open D5.S3.VertexAlgebra.LatticeQuartetContraction
  (State Variables Exponents StateIndex sector actualBasis)
open D5.S3.VertexAlgebra.LatticeBRSTModeFiltration
  (variableWeight exponentDegree degree sector_coefficient)
open private charge_sum from D5.S3.Quantum.Fermionic.BcGhostCharge
open MvPolynomial

noncomputable section

private theorem abs_siteSign (j : ℕ) : |siteSign j| = (1 : ℤ) := by
  by_cases hj : j % 2 = 0 <;> simp [siteSign, hj]

private theorem abs_site_sum_le_card (T : Finset ℕ) :
    |∑ j ∈ T, siteSign j| ≤ (T.card : ℤ) := by
  calc
    |∑ j ∈ T, siteSign j| ≤ ∑ j ∈ T, |siteSign j| :=
      Finset.abs_sum_le_sum_abs siteSign T
    _ = (T.card : ℤ) := by simp [abs_siteSign]

private theorem card_le_siteEnergy_sum (S : Finset ℕ)
    (h1 : 1 ∉ S) (h3 : 3 ∉ S) :
    (S.card : ℤ) ≤ ∑ j ∈ S, siteEnergy j := by
  calc
    (S.card : ℤ) = ∑ _j ∈ S, (1 : ℤ) := by simp
    _ ≤ ∑ j ∈ S, siteEnergy j := by
      apply Finset.sum_le_sum
      intro j hj
      have hj1 : j ≠ 1 := by
        intro he
        subst j
        exact h1 hj
      have hj3 : j ≠ 3 := by
        intro he
        subst j
        exact h3 hj
      have hp := siteEnergy_pos_of_ne_one_three hj1 hj3
      omega

/-- Literal charge versus the original quartet count. Site 1 is a hole
when absent; site 3 really must be excluded from this inequality. -/
theorem ghost_abs_charge_sub_one_le_count (S : Finset ℕ) (h3 : 3 ∉ S) :
    |charge S - 1| ≤ (count S : ℤ) := by
  classical
  by_cases h1 : 1 ∈ S
  · have h3' : 3 ∉ S.erase 1 := by simp [h3]
    have hregular : (S.erase 1).erase 3 = S.erase 1 :=
      Finset.erase_eq_of_notMem h3'
    have hsum : charge S - 1 = ∑ j ∈ S.erase 1, siteSign j := by
      rw [charge_sum, ← Finset.sum_erase_add S siteSign h1]
      have hone : siteSign 1 = 1 := by norm_num [siteSign]
      rw [hone]
      omega
    rw [hsum]
    simpa [count, h1, hregular] using abs_site_sum_le_card (S.erase 1)
  · have hsum : charge S - 1 = (∑ j ∈ S, siteSign j) - 1 := by
      rw [charge_sum]
    have hcard : (count S : ℤ) = (S.card : ℤ) + 1 := by
      simp [count, h1, h3]
    rw [hsum, hcard]
    calc
      |(∑ j ∈ S, siteSign j) - 1| ≤
          |∑ j ∈ S, siteSign j| + (1 : ℤ) := by
        simpa only [sub_eq_add_neg, abs_neg, abs_one] using
          (abs_add_le (∑ j ∈ S, siteSign j) (-1 : ℤ))
      _ ≤ (S.card : ℤ) + 1 := by
        have h := abs_site_sum_le_card S
        omega

/-- Literal positive site energies dominate the count, including its site-1 hole. -/
theorem ghost_count_le_relativeEnergy (S : Finset ℕ) (h3 : 3 ∉ S) :
    (count S : ℤ) ≤ relativeEnergy S := by
  classical
  by_cases h1 : 1 ∈ S
  · have h3' : 3 ∉ S.erase 1 := by simp [h3]
    have hregular : (S.erase 1).erase 3 = S.erase 1 :=
      Finset.erase_eq_of_notMem h3'
    have hcount : (count S : ℤ) = ((S.erase 1).card : ℤ) := by
      simp [count, h1, hregular]
    rw [hcount]
    calc
      ((S.erase 1).card : ℤ) ≤ ∑ j ∈ S.erase 1, siteEnergy j :=
        card_le_siteEnergy_sum (S.erase 1) (Finset.notMem_erase 1 S) h3'
      _ = relativeEnergy S := by
        rw [relativeEnergy_split]
        simp [h1, hregular]
  · have hcount : (count S : ℤ) = (S.card : ℤ) + 1 := by
      simp [count, h1, h3]
    rw [hcount]
    calc
      (S.card : ℤ) + 1 ≤ (∑ j ∈ S, siteEnergy j) + 1 := by
        have h := card_le_siteEnergy_sum S h1 h3
        omega
      _ = relativeEnergy S := by
        rw [relativeEnergy_split]
        simp [h1, h3, add_comm]

private theorem ghost_abs_charge_sub_one_le_relativeEnergy (S : Finset ℕ)
    (h3 : 3 ∉ S) : |charge S - 1| ≤ relativeEnergy S :=
  (ghost_abs_charge_sub_one_le_count S h3).trans
    (ghost_count_le_relativeEnergy S h3)

/-- Frequency r is the original creation frequency r+1. -/
def frameEnergy {t : ℕ} (m : Exponents t) : ℕ :=
  Finsupp.weight frequencyWeight m

private theorem variableWeight_abs_le_one {t : ℕ} (x : Variables t) :
    |variableWeight x| ≤ (1 : ℤ) := by
  unfold variableWeight
  split_ifs <;> norm_num

/-- The original signed exponentDegree is bounded by the frequency-weighted
excitation sum, rather than by an assumed coordinate energy. -/
theorem abs_exponentDegree_le_frameEnergy {t : ℕ} (m : Exponents t) :
    |exponentDegree m| ≤ (frameEnergy m : ℤ) := by
  classical
  change |∑ x ∈ m.support, (m x : ℤ) * variableWeight x| ≤ _
  calc
    |∑ x ∈ m.support, (m x : ℤ) * variableWeight x| ≤
        ∑ x ∈ m.support, |(m x : ℤ) * variableWeight x| :=
      Finset.abs_sum_le_sum_abs (fun x => (m x : ℤ) * variableWeight x) m.support
    _ ≤ ∑ x ∈ m.support, (m x : ℤ) * ((x.2 + 1 : ℕ) : ℤ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hn : (0 : ℤ) ≤ (m x : ℤ) := by omega
      have hf : (1 : ℤ) ≤ ((x.2 + 1 : ℕ) : ℤ) := by omega
      rw [abs_mul, abs_of_nonneg hn]
      exact mul_le_mul_of_nonneg_left ((variableWeight_abs_le_one x).trans hf) hn
    _ = (frameEnergy m : ℤ) := by
      simp [frameEnergy, frequencyWeight, Finsupp.weight_apply, Finsupp.sum,
        smul_eq_mul, Nat.cast_sum, Nat.cast_mul]

/-- Pull back the ORIGINAL tensor coefficient Finsupp along d ↦ ((p,d),S).
The exponent-to-tensor-label map is injective. AddMonoidAlgebra.ofCoeff
packages the resulting finite coefficient function as the original polynomial. -/
def originalSlice (D : LatticeData) (p : Charge D) (S : Finset ℕ) :
    State D →ₗ[ℂ] Oscillator D where
  toFun x := AddMonoidAlgebra.ofCoeff
    (Finsupp.comapDomain (fun d : Exponent D => ((p,d),S))
      (tensorCoeffEquiv D x) (by
        intro d hd e he hde
        exact congrArg (fun i : TensorLabel D => i.1.2) hde))
  map_add' x y := by
    apply MvPolynomial.ext
    intro d
    change tensorCoeffEquiv D (x + y) ((p,d),S) =
      tensorCoeffEquiv D x ((p,d),S) + tensorCoeffEquiv D y ((p,d),S)
    simp only [map_add, Finsupp.add_apply]
  map_smul' z x := by
    apply MvPolynomial.ext
    intro d
    change tensorCoeffEquiv D (z • x) ((p,d),S) =
      z • tensorCoeffEquiv D x ((p,d),S)
    simp only [map_smul, Finsupp.smul_apply]

@[simp] theorem originalSlice_coeff (D : LatticeData) (x : State D)
    (p : Charge D) (S : Finset ℕ) (d : Exponent D) :
    (originalSlice D p S x).coeff d = coeff D x ((p,d),S) := rfl

private theorem originalSlice_tmul (D : LatticeData) (p : Charge D)
    (S : Finset ℕ) (v : Carrier D) (w : Fock) :
    originalSlice D p S (v ⊗ₜ[ℂ] w) = w S • v p := by
  apply MvPolynomial.ext
  intro d
  rw [originalSlice_coeff, coeff_tmul_original, MvPolynomial.coeff_smul]
  exact mul_comm _ _

/-- Actual polynomial substitution applied to the original tensor slice. -/
def coordinateSlice {D : LatticeData} (F : NullFrame D) {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K) (p : Charge D) (S : Finset ℕ) :
    State D →ₗ[ℂ] PolynomialCoordinates (NullFrame.Label t) :=
  (F.coordinateEquiv B).toLinearMap.comp (originalSlice D p S)

private theorem coordinateSlice_sector {D : LatticeData} (F : NullFrame D)
    {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (p q : Charge D) (S : Finset ℕ)
    (Q : PolynomialCoordinates (NullFrame.Label t)) (w : Fock) :
    coordinateSlice F B p S (sector F B q Q w) =
      if q = p then w S • Q else 0 := by
  classical
  change F.coordinateEquiv B
    (originalSlice D p S (Finsupp.single q ((F.coordinateEquiv B).symm Q) ⊗ₜ[ℂ] w)) = _
  rw [originalSlice_tmul, map_smul]
  by_cases hp : q = p <;> simp [hp]

/-- Arbitrary-state bridge, proved by equality of two linear maps on the
ORIGINAL tensor basis. The sector coefficient theorem is used only where
its hypotheses really apply, and basis expansion extends it to every x. -/
theorem actualBasis_repr_eq_coordinateSlice {D : LatticeData}
    (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (x : State D) (i : StateIndex D t) :
    (actualBasis F B).repr x i =
      (coordinateSlice F B i.1.1 i.2 x).coeff i.1.2 := by
  classical
  let L : State D →ₗ[ℂ] ℂ :=
    (Finsupp.lapply i).comp (actualBasis F B).repr.toLinearMap
  let R : State D →ₗ[ℂ] ℂ :=
    (MvPolynomial.lcoeff ℂ i.1.2).comp (coordinateSlice F B i.1.1 i.2)
  have he : L = R := by
    apply (tensorBasis D).ext
    rintro ⟨⟨q,d⟩,S⟩
    change (actualBasis F B).repr (tensorBasis D ((q,d),S)) i =
      (coordinateSlice F B i.1.1 i.2 (tensorBasis D ((q,d),S))).coeff i.1.2
    have ht : tensorBasis D ((q,d),S) =
        sector F B q (F.coordinateEquiv B (monomial d 1)) (ket S) := by
      rw [tensorBasis_apply]
      simp only [sector, AlgEquiv.symm_apply_apply]
    rw [ht, sector_coefficient, coordinateSlice_sector]
    by_cases hq : q = i.1.1 <;> simp [hq, smul_eq_mul, mul_comm]
  exact LinearMap.congr_fun he x

private theorem exists_original_coeff_of_coordinate_coeff
    {D : LatticeData} (F : NullFrame D) {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K) (x : State D)
    (q : Charge D) (S : Finset ℕ) (m : Exponents t)
    (hm : (coordinateSlice F B q S x).coeff m ≠ 0) :
    ∃ d : Exponent D, coeff D x ((q,d),S) ≠ 0 := by
  have hP : originalSlice D q S x ≠ 0 := by
    intro hz
    apply hm
    change (F.coordinateEquiv B (originalSlice D q S x)).coeff m = 0
    simp [hz]
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hP
  exact ⟨d, by simpa only [originalSlice_coeff] using hd⟩

/- The original L0 diagonal enters through mem_relativeMassShell_iff.
Every original monomial in this slice has the same natural frequency as d.
frequency_grading is the native theorem proved from the actual forward
and inverse frame-variable substitutions and lin_homogeneous, with no
coordinate-energy identity premise. -/
private theorem coordinate_slice_shell_support
    {D : LatticeData} (F : NullFrame D) {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p : Charge D) (x : State D) (hx : x ∈ relativeMassShell D H p)
    (q : Charge D) (S : Finset ℕ) (m : Exponents t)
    (hm : (coordinateSlice F B q S x).coeff m ≠ 0) :
    q = p ∧ 3 ∉ S ∧
      (frameEnergy m : ℤ) + relativeEnergy S = 1 - chargeEnergy D p := by
  have hs := (mem_relativeMassShell_iff D H hHG hGH p x).mp hx
  obtain ⟨d, hd⟩ := exists_original_coeff_of_coordinate_coeff F B x q S m hm
  have hi := hs ((q,d),S) hd
  have hhom : IsWeightedHomogeneous (oscillatorWeight D)
      (originalSlice D q S x) (oscillatorEnergy d) := by
    intro e he
    have hj := hs ((q,e),S) (by simpa only [originalSlice_coeff] using he)
    change oscillatorEnergy e = oscillatorEnergy d
    have hei : (oscillatorEnergy d : ℤ) + relativeEnergy S =
        1 - chargeEnergy D p := hi.2.2
    have hej : (oscillatorEnergy e : ℤ) + relativeEnergy S =
        1 - chargeEnergy D p := hj.2.2
    omega
  have hcoord : IsWeightedHomogeneous frequencyWeight
      (coordinateSlice F B q S x) (oscillatorEnergy d) :=
    (F.frequency_grading B (originalSlice D q S x) (oscillatorEnergy d)).mpr hhom
  have hf : frameEnergy m = oscillatorEnergy d := hcoord hm
  refine ⟨hi.1, hi.2.1, ?_⟩
  rw [hf]
  exact hi.2.2

/-- End-to-end coefficient bound for the literal original shell. The same
original momentum, b(0) exclusion and energy identity are conclusions.
The degree is LatticeBRSTModeFiltration.degree on actualBasis indices.
This supplies the missing interval for the original h-delta consumer;
it asserts no raising, invariance, nilpotence, HPL or cohomology theorem. -/
theorem actualBasis_coefficient_shell_degree_bound
    (D : LatticeData) (F : NullFrame D) {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p : Charge D) (x : State D) (hx : x ∈ relativeMassShell D H p)
    (i : StateIndex D t) (hi : (actualBasis F B).repr x i ≠ 0) :
    i.1.1 = p ∧ 3 ∉ i.2 ∧
      (frameEnergy i.1.2 : ℤ) + relativeEnergy i.2 = 1 - chargeEnergy D p ∧
      -(massShellCutoff D p : ℤ) ≤ degree i ∧
      degree i ≤ (massShellCutoff D p : ℤ) := by
  have hm : (coordinateSlice F B i.1.1 i.2 x).coeff i.1.2 ≠ 0 := by
    rwa [actualBasis_repr_eq_coordinateSlice F B x i] at hi
  obtain ⟨hp, h3, he⟩ :=
    coordinate_slice_shell_support F B H hHG hGH p x hx i.1.1 i.2 i.1.2 hm
  have hg := relativeEnergy_nonneg i.2
  have hf : (0 : ℤ) ≤ (frameEnergy i.1.2 : ℤ) := by omega
  have hcharge : chargeEnergy D p ≤ 1 := by omega
  have hN := massShellCutoff_cast D p hcharge
  have hmdeg := abs_exponentDegree_le_frameEnergy i.1.2
  have hgdeg := ghost_abs_charge_sub_one_le_relativeEnergy i.2 h3
  have habs : |degree i| ≤ (massShellCutoff D p : ℤ) := by
    calc
      |degree i| = |exponentDegree i.1.2 + (charge i.2 - 1)| := by
        congr 1
        unfold degree
        ring
      _ ≤ |exponentDegree i.1.2| + |charge i.2 - 1| := abs_add_le _ _
      _ ≤ (frameEnergy i.1.2 : ℤ) + relativeEnergy i.2 := add_le_add hmdeg hgdeg
      _ = (massShellCutoff D p : ℤ) := he.trans hN.symm
  exact ⟨hp, h3, he, (abs_le.mp habs).1, (abs_le.mp habs).2⟩

/- For chargeEnergy > 1, use the existing concrete theorem
LatticeRelativeMassShell.relativeMassShell_eq_bot_of_one_lt directly.
Its proof uses nonnegative original oscillator and relative ghost energies
in mem_relativeMassShell_iff and coefficient separation. -/

end
end D5.S3.VertexAlgebra.LatticeRelativeShellDegreeBounds
