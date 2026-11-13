/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration
   mirror-E: none(waiver:symbolic-original-q-fixed-energy-filtration)
   anchors: []
   utility: none
   digest: Uniform finite termination of the original Q perturbation on every integer fixed-energy sector. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTFullOriginalRaising
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare
import D5.S3.VertexAlgebra.LatticeSugawaraConformal
import D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
import Batteries.Tactic.OpenPrivate

/-!
Fixed integral charge and total energy for the literal original-Q carrier.

The signed filtration is the CURRENT `LatticeBRSTModeFiltration.degree`:
`exponentDegree + BcGhostCharge.charge - 1`.  The current full-original
raising theorem supplies the strict step for `(Q-d0)` and `h*(Q-d0)` on the
same `actualBasis`. This file proves the literal energy preservation and signed
window, then iterates the normalized perturbation through that window to zero.
The bound is `2 * level.toNat + 2` for every integer level and arbitrary rank;
no relative-kernel condition or zero-charge exclusion is imposed. The two
exceptional zero-mode occupations `{1}` and `{1,3}` remain in the window.
The final finite-HPL wrapper and unused projector restriction are saved future
source and are not part of this publication.

Source attribution: immutable supplier input
f8dc18b8c93143d2b804315536f93bb8b2d2eef5ea3ded35d6e4328687cc12a7.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraVirasoro LatticeSugawaraConformal
open LatticeLightConeCoordinates LatticeLightConeCoordinates.NullFrame
open LatticeQuartetContraction
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostCharge
open LatticeBRSTModeFiltration
open LatticeBRSTFullOriginalRaising
open private basis_expansion chargeProject_basis fixed_charge_coefficients from
  D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
open private charge_sum from D5.S3.Quantum.Fermionic.BcGhostCharge

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)

def groundEnergy (beta : Charge D) : ℂ := (bilinear D beta beta : ℂ) / 2

def totalL0 (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ (State D) :=
  LatticeMatterGhostCoupling.matterMode D H 0 + LatticeMatterGhostCoupling.ghostVirasoro D 0

def oscillatorLevel (m : Exponents t) : ℕ := Finsupp.weight frequencyWeight m

/-- Integer level measured above the actual c(1) vacuum, on every raw ket. -/
def indexLevel (i : StateIndex D t) : ℤ := oscillatorLevel i.1.2 + BcGhostRelativeEnergy.relativeEnergy i.2

theorem totalL0_basis (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : StateIndex D t) :
    totalL0 H (actualBasis F B i) =
      (groundEnergy i.1.1 + (indexLevel i : ℂ) - 1) • actualBasis F B i := by
  rcases i with ⟨⟨beta,m⟩,S⟩
  have hm : MvPolynomial.IsWeightedHomogeneous (oscillatorWeight D)
      ((F.coordinateEquiv B).symm (MvPolynomial.monomial m 1)) (oscillatorLevel m) := by
    apply (F.frequency_grading B _ _).mp
    rw [AlgEquiv.apply_symm_apply]
    apply MvPolynomial.isWeightedHomogeneous_monomial
    rfl
  have he := sugawaraMode_weighted_homogeneous D H hHG hGH beta _ _ hm
  rw [actualBasis_apply]
  simp only [totalL0, LinearMap.add_apply, LatticeMatterGhostCoupling.matterMode, LatticeMatterGhostCoupling.ghostVirasoro,
    sector, TensorProduct.map_tmul, LinearMap.id_apply, he, BcGhostRelativeEnergy.L_zero_ket,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  have hs : ((oscillatorLevel m : ℂ) + (bilinear D beta beta : ℂ) / 2) +
      (BcGhostRelativeEnergy.energy S : ℂ) =
      groundEnergy beta +
        (indexLevel (⟨⟨beta, m⟩, S⟩ : StateIndex D t) : ℂ) - 1 := by
    simp only [groundEnergy, indexLevel, BcGhostRelativeEnergy.relativeEnergy,
      Int.cast_add, Int.cast_natCast, Int.cast_sub, Int.cast_one]
    ring
  rw [← TensorProduct.add_tmul, ← add_smul, hs]

theorem totalL0_diagonal (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    totalL0 (D := D) H = diagonal (actualBasis F B)
      (fun i => groundEnergy i.1.1 + (indexLevel i : ℂ) - 1) := by
  apply (actualBasis F B).ext
  intro i
  rw [totalL0_basis F B H hHG hGH, diagonal_basis]

/-- The literal all-state charge/total-energy sector, at any integer level. -/
def fixedSector (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) : Submodule ℂ (State D) where
  carrier := {v | chargeProject beta v = v ∧
    totalL0 H v = (groundEnergy beta + (level : ℂ) - 1) • v}
  zero_mem' := by
    constructor <;> simp only [map_zero, smul_zero]
  add_mem' := by
    rintro v w ⟨hv,hvE⟩ ⟨hw,hwE⟩
    constructor
    · rw [map_add, hv, hw]
    · rw [map_add, hvE, hwE, smul_add]
  smul_mem' := by
    rintro a v ⟨hv,hvE⟩
    constructor
    · rw [map_smul, hv]
    · rw [map_smul, hvE, smul_comm]

theorem mem_fixedSector_iff (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) (level : ℤ) (v : State D) :
    v ∈ fixedSector H beta level ↔ ∀ i : StateIndex D t,
      (actualBasis F B).repr v i ≠ 0 → i.1.1 = beta ∧ indexLevel i = level := by
  constructor
  · rintro ⟨hc,he⟩ i hi
    have hp : i.1.1 = beta := by
      by_contra hn
      exact hi ((fixed_charge_coefficients F B beta v).mp hc i hn)
    refine ⟨hp, ?_⟩
    have eq := congrArg (fun w => (actualBasis F B).repr w i) he
    rw [totalL0_diagonal F B H hHG hGH, diagonal_coefficient] at eq
    simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, hp] at eq
    have e := mul_right_cancel₀ hi eq
    have e' : (indexLevel i : ℂ) = (level : ℂ) := by linear_combination e
    exact_mod_cast e'
  · intro hs
    constructor
    · apply (fixed_charge_coefficients F B beta v).mpr
      intro i hp
      by_contra hn
      exact hp (hs i hn).1
    · apply (actualBasis F B).repr.injective
      ext i
      rw [totalL0_diagonal F B H hHG hGH, diagonal_coefficient]
      simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
      by_cases hz : (actualBasis F B).repr v i = 0
      · simp [hz]
      · obtain ⟨hp,he⟩ := hs i hz
        rw [hp, he]

def signedFiltration (beta : Charge D) (level lower : ℤ) : Submodule ℂ (State D) :=
  Submodule.span ℂ (actualBasis F B '' {i : StateIndex D t |
    i.1.1 = beta ∧ indexLevel i = level ∧ lower ≤ degree i})

private theorem charge_shift_bounds (S : Finset ℕ) :
    -BcGhostRelativeEnergy.relativeEnergy S ≤
        BcGhostCharge.charge S - 1 ∧
      BcGhostCharge.charge S - 1 ≤ BcGhostRelativeEnergy.relativeEnergy S + 1 := by
  classical
  have hcharge : BcGhostCharge.charge S = ∑ j ∈ S, BcGhostCharge.siteSign j :=
    charge_sum S
  have split : BcGhostCharge.charge S - 1 =
      (if 1 ∈ S then 0 else -1) + (if 3 ∈ S then 1 else 0) +
        ∑ j ∈ (S.erase 1).erase 3, BcGhostCharge.siteSign j := by
    rw [hcharge]
    by_cases h1 : 1 ∈ S <;> by_cases h3 : 3 ∈ S
    · have he3 : 3 ∈ S.erase 1 := by simp [h3]
      rw [← Finset.sum_erase_add S BcGhostCharge.siteSign h1,
        ← Finset.sum_erase_add (S.erase 1) BcGhostCharge.siteSign he3]
      norm_num [h1, h3, BcGhostCharge.siteSign] <;> ring
    · have he3 : 3 ∉ S.erase 1 := by simp [h3]
      rw [← Finset.sum_erase_add S BcGhostCharge.siteSign h1]
      simp [h1, h3, he3, BcGhostCharge.siteSign]
    · have he1 : S.erase 1 = S := Finset.erase_eq_of_notMem h1
      rw [← Finset.sum_erase_add S BcGhostCharge.siteSign h3]
      simp [h1, h3, he1, BcGhostCharge.siteSign] <;> ring
    · simp [h1, h3, Finset.erase_eq_of_notMem, BcGhostCharge.siteSign] <;> ring
  have siteBounds (j : ℕ) (hj : j ∈ (S.erase 1).erase 3) :
      -BcGhostRelativeEnergy.siteEnergy j ≤ BcGhostCharge.siteSign j ∧
        BcGhostCharge.siteSign j ≤ BcGhostRelativeEnergy.siteEnergy j := by
    have h3 := (Finset.mem_erase.mp hj).1
    have h1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    have hp := BcGhostRelativeEnergy.siteEnergy_pos_of_ne_one_three h1 h3
    unfold BcGhostCharge.siteSign
    split_ifs <;> constructor <;> omega
  have lo := Finset.sum_le_sum (fun j hj => (siteBounds j hj).1)
  have hi := Finset.sum_le_sum (fun j hj => (siteBounds j hj).2)
  simp only [Finset.sum_neg_distrib] at lo
  rw [split, BcGhostRelativeEnergy.relativeEnergy_split]
  by_cases h1 : 1 ∈ S <;> by_cases h3 : 3 ∈ S <;>
    simp only [h1, h3, not_true_eq_false, not_false_eq_true, if_true, if_false] <;>
    constructor <;> omega

private theorem exponentDegree_bounds (m : Exponents t) :
    -(oscillatorLevel m : ℤ) ≤ exponentDegree m ∧
      exponentDegree m ≤ (oscillatorLevel m : ℤ) := by
  classical
  have term (x : Variables t) :
      -((m x * frequencyWeight x : ℕ) : ℤ) ≤
          (m x : ℤ) * variableWeight x ∧
        (m x : ℤ) * variableWeight x ≤ ((m x * frequencyWeight x : ℕ) : ℤ) := by
    have hw : -(frequencyWeight x : ℤ) ≤ variableWeight x ∧
        variableWeight x ≤ (frequencyWeight x : ℤ) := by
      rcases x with ⟨label,r⟩
      rcases label with u | u
      · simp only [variableWeight, frequencyWeight]
        constructor <;> omega
      · rcases u with u | k <;> simp only [variableWeight, frequencyWeight] <;>
          constructor <;> omega
    constructor
    · simpa only [Nat.cast_mul, mul_neg] using
        mul_le_mul_of_nonneg_left hw.1 (Int.natCast_nonneg (m x))
    · simpa only [Nat.cast_mul] using
        mul_le_mul_of_nonneg_left hw.2 (Int.natCast_nonneg (m x))
  have lo := Finset.sum_le_sum (s := m.support) (fun x _ => (term x).1)
  have hi := Finset.sum_le_sum (s := m.support) (fun x _ => (term x).2)
  constructor
  · simpa [oscillatorLevel, exponentDegree, Finsupp.weight_apply, Finsupp.sum,
      Nat.cast_sum, Nat.cast_mul, Finset.sum_neg_distrib] using lo
  · simpa [oscillatorLevel, exponentDegree, Finsupp.weight_apply, Finsupp.sum,
      Nat.cast_sum, Nat.cast_mul] using hi

/-- The absolute current degree window retains both zero-mode occupations {1} and {1,3}. -/
theorem degree_bounds (i : StateIndex D t) :
    -indexLevel i ≤ degree i ∧ degree i ≤ indexLevel i + 1 := by
  have hm := exponentDegree_bounds i.1.2
  have hg := charge_shift_bounds i.2
  unfold indexLevel degree
  constructor <;> omega

theorem basis_mem_fixedSector (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : StateIndex D t) : actualBasis F B i ∈ fixedSector H i.1.1 (indexLevel i) := by
  constructor
  · rw [chargeProject_basis F B]
    simp
  · exact totalL0_basis F B H hHG hGH i

theorem mem_signedFiltration_iff (beta : Charge D) (level lower : ℤ) (v : State D) :
    v ∈ signedFiltration F B beta level lower ↔ ∀ i : StateIndex D t,
      (actualBasis F B).repr v i ≠ 0 →
        i.1.1 = beta ∧ indexLevel i = level ∧ lower ≤ degree i := by
  classical
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rcases hv with ⟨j,hj,rfl⟩
      change j.1.1 = beta ∧ indexLevel j = level ∧ lower ≤ degree j at hj
      intro i hi
      have hij : j = i := by
        by_contra hn
        exact hi (by simp [Module.Basis.repr_self, hn])
      simpa only [hij] using hj
    | zero =>
      intro i hi
      have hz : (actualBasis F B).repr (0 : State D) = 0 :=
        (actualBasis F B).repr.map_zero
      exact (hi (congrArg (fun f : StateIndex D t →₀ ℂ => f i) hz)).elim
    | add v w hv hw ihv ihw =>
      intro i hi
      by_cases hvi : (actualBasis F B).repr v i = 0
      · apply ihw i
        intro hwi
        exact hi (by
          simp only [LinearEquiv.map_add, Finsupp.add_apply, hvi, hwi, add_zero])
      · exact ihv i hvi
    | smul a v hv ih =>
      intro i hi
      apply ih i
      intro hz
      exact hi (by simp only [LinearEquiv.map_smul, Finsupp.smul_apply, hz, smul_zero])
  · intro hs
    rw [← basis_expansion F B v]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, hs i (Finsupp.mem_support_iff.mp hi), rfl⟩

theorem sector_mem_filtration (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) (level : ℤ) (v : State D) (hv : v ∈ fixedSector H beta level) :
    v ∈ signedFiltration F B beta level (-level) := by
  rw [← basis_expansion F B v]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  obtain ⟨hp,he⟩ := (mem_fixedSector_iff F B H hHG hGH beta level v).mp hv i
    (Finsupp.mem_support_iff.mp hi)
  refine ⟨i, ⟨hp,he,?_⟩, rfl⟩
  simpa only [he] using (degree_bounds i).1

theorem filtration_exhausted (beta : Charge D) (level lower : ℤ)
    (h : level + 1 < lower) : signedFiltration F B beta level lower = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro v ⟨i, ⟨hp,he,hd⟩, rfl⟩
  have hu := (degree_bounds i).2
  rw [he] at hu
  omega

/-- The existing current covariance has zero anomaly at mode zero in EVERY rank. -/
theorem totalL0_Q (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    totalL0 (D := D) H * LatticeBRST.totalCharge D H =
      LatticeBRST.totalCharge D H * totalL0 H := by
  have eq := LatticeBRST.total_covariance D H hHG hGH 0
  simp at eq
  exact (sub_eq_zero.mp eq).symm

private theorem hasCharge_of_project
    (beta : Charge D) (v : State D)
    (hv : chargeProject beta v = v) : HasCharge F B beta v := by
  intro i hi
  by_contra hn
  exact hi ((fixed_charge_coefficients F B beta v).mp hv i hn)

private theorem project_of_hasCharge
    (beta : Charge D) (v : State D)
    (hv : HasCharge F B beta v) : chargeProject beta v = v := by
  apply (fixed_charge_coefficients F B beta v).mpr
  intro i hne
  by_contra hi
  exact hne (hv i hi)

include F B in
theorem Q_preserves (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) (level : ℤ) (v : State D) (hv : v ∈ fixedSector H beta level) :
    LatticeBRST.totalCharge D H v ∈ fixedSector H beta level := by
  constructor
  · exact project_of_hasCharge F B beta (LatticeBRST.totalCharge D H v)
      ((original_operators_preserve_charge F B H beta v
        (hasCharge_of_project F B beta v hv.1)).1)
  · have eq := LinearMap.congr_fun (totalL0_Q H hHG hGH) v
    simpa only [Module.End.mul_apply, hv.2, map_smul] using eq

set_option maxHeartbeats 800000 in
private theorem energy_tensor_current (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : E D) (n k : ℤ) (G : Module.End ℂ Fock)
    (hg : BcGhostVirasoro.L 0 * G -
      G * BcGhostVirasoro.L 0 = -(k : ℂ) • G) :
    totalL0 H * tp (a u n) G - tp (a u n) G * totalL0 H =
      (-(n : ℂ) - (k : ℂ)) • tp (a u n) G := by
  have hm : sugawaraMode D H 0 * a u n - a u n * sugawaraMode D H 0 =
      -(n : ℂ) • a u n := by
    unfold a
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
      ← Finset.sum_sub_distrib, ← smul_sub]
    simp_rw [sugawaraMode_current_commutator D H hHG hGH]
    simp only [zero_add, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_comm]
  apply TensorProduct.ext'
  intro v w
  have hm' := LinearMap.congr_fun hm v
  have hg' := LinearMap.congr_fun hg w
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hm' hg'
  simp only [totalL0, LatticeMatterGhostCoupling.matterMode, LatticeMatterGhostCoupling.ghostVirasoro, tp, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.smul_apply, map_add]
  have hm'' := congrArg (fun z => z ⊗ₜ[ℂ] G w) hm'
  have hg'' := congrArg (fun z => a u n v ⊗ₜ[ℂ] z) hg'
  simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub] at hm'' hg''
  rw [← TensorProduct.smul_tmul'] at hm''
  rw [TensorProduct.tmul_smul] at hg''
  calc
    _ = ((sugawaraMode D H 0) ((a u n) v) ⊗ₜ[ℂ] G w -
          (a u n) ((sugawaraMode D H 0) v) ⊗ₜ[ℂ] G w) +
        ((a u n) v ⊗ₜ[ℂ] (BcGhostVirasoro.L 0) (G w) -
          (a u n) v ⊗ₜ[ℂ] G ((BcGhostVirasoro.L 0) w)) := by abel
    _ = -(n : ℂ) • ((a u n) v ⊗ₜ[ℂ] G w) +
        -(k : ℂ) • ((a u n) v ⊗ₜ[ℂ] G w) := congrArg₂ (· + ·) hm'' hg''
    _ = _ := by rw [← add_smul, sub_eq_add_neg]

theorem totalL0_d0 (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) : totalL0 H * d0 F beta = d0 F beta * totalL0 H := by
  have atom (n : ℤ) : totalL0 H * dm F n = dm F n * totalL0 H := by
    have hg : BcGhostVirasoro.L 0 * c (-n) -
        c (-n) * BcGhostVirasoro.L 0 =
        -((-n : ℤ) : ℂ) • c (-n) := by
      simpa using BcGhostVirasoro.ward_c 0 (-n)
    have eq := energy_tensor_current H hHG hGH F.eMinus n (-n) (c (-n)) hg
    apply sub_eq_zero.mp
    simpa [dm] using eq
  have ht : totalL0 H * unscaledD F = unscaledD F * totalL0 H := by
    apply Family.total_commutes_fixed (dFamily F)
    intro r
    simp only [dFamily, dTerm, mul_add, add_mul, atom]
  simpa only [d0, mul_smul_comm, smul_mul_assoc] using congrArg (fun A => F.pPlus beta • A) ht

private theorem totalL0_R (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) : totalL0 H * R F beta = R F beta * totalL0 H := by
  have atom (n : ℤ) : totalL0 H * rr F n = rr F n * totalL0 H := by
    have hg : BcGhostVirasoro.L 0 * b n -
        b n * BcGhostVirasoro.L 0 = -(n : ℂ) • b n := by
      simpa using BcGhostVirasoro.ward_b 0 n
    have eq := energy_tensor_current H hHG hGH F.ePlus (-n) n (b n) hg
    apply sub_eq_zero.mp
    simpa [rr] using eq
  have ht : totalL0 H * unscaledR F = unscaledR F * totalL0 H := by
    apply Family.total_commutes_fixed (rFamily F)
    intro r
    simp only [rFamily, rTerm, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, atom]
  simpa only [R, mul_smul_comm, smul_mul_assoc] using
    congrArg (fun A => (F.pPlus beta)⁻¹ • A) ht

private theorem totalL0_invM (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    totalL0 H * invM F B = invM F B * totalL0 H := by
  apply (actualBasis F B).ext
  intro i
  simp only [Module.End.mul_apply, invM, inverseNumber, diagonal_basis,
    map_smul, totalL0_basis F B H hHG hGH]
  exact smul_comm _ _ _

theorem totalL0_h (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) : totalL0 H * h F B beta = h F B beta * totalL0 H := by
  rw [h, ← mul_assoc, totalL0_R F H hHG hGH, mul_assoc,
    totalL0_invM F B H hHG hGH, ← mul_assoc]

include B in
theorem d0_preserves (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) (level : ℤ) (v : State D) (hv : v ∈ fixedSector H beta level) :
    d0 F beta v ∈ fixedSector H beta level := by
  constructor
  · exact project_of_hasCharge F B beta (d0 F beta v)
      ((original_operators_preserve_charge F B H beta v
        (hasCharge_of_project F B beta v hv.1)).2.1)
  · simpa only [Module.End.mul_apply, hv.2, map_smul] using
      LinearMap.congr_fun (totalL0_d0 F H hHG hGH beta) v

theorem h_preserves (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) (level : ℤ) (v : State D) (hv : v ∈ fixedSector H beta level) :
    h F B beta v ∈ fixedSector H beta level := by
  constructor
  · exact project_of_hasCharge F B beta (h F B beta v)
      ((original_operators_preserve_charge F B H beta v
        (hasCharge_of_project F B beta v hv.1)).2.2)
  · simpa only [Module.End.mul_apply, hv.2, map_smul] using
      LinearMap.congr_fun (totalL0_h F B H hHG hGH beta) v

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration

/-! Uniform termination of the original Q perturbation on every literal fixed-energy sector. -/

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTFiniteTransfer

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open LatticeLightConeCoordinates LatticeLightConeCoordinates.NullFrame
open LatticeQuartetContraction D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration
open LatticeBRSTModeFiltration LatticeBRSTFullOriginalRaising
open D5.S3.HomologicalAlgebra
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (beta : Charge D)

def normalizedPerturbation : Module.End ℂ (State D) :=
  h F B beta * (LatticeBRST.totalCharge D H - d0 F beta)

set_option backward.isDefEq.respectTransparency true

set_option maxRecDepth 2048 in
include hHG hGH in
/-- The current full-original raising supplier gives one genuine step on each
raw occupation basis vector.  Its charge and energy conclusions are handled
by the literal fixed-sector lemmas above; its degree conclusion is the current
`LatticeBRSTModeFiltration.degree`, including all zero modes and transverse
charge. -/
private theorem normalizedPerturbation_basis_step
    (m : Exponents t) (S : Finset ℕ) :
    normalizedPerturbation F B H beta (actualBasis F B (⟨beta,m⟩,S)) ∈
      signedFiltration F B beta (indexLevel (⟨beta,m⟩,S))
        (degree (⟨beta,m⟩,S) + 1) := by
  classical
  let i : StateIndex D t := (⟨beta,m⟩, S)
  have hcharge : HasCharge F B beta (actualBasis F B i) := by
    intro j hj
    have hji : j = i := by
      by_contra hne
      exact hj (by simp [Module.Basis.repr_self, hne])
    rw [hji]
  have hdegree : ∀ j : StateIndex D t,
      (actualBasis F B).repr (actualBasis F B i) j ≠ 0 →
        degree i ≤ degree j := by
    intro j hj
    have hji : j = i := by
      by_contra hne
      exact hj (by simp [Module.Basis.repr_self, hne])
    simpa [hji]
  have hraise := full_remainder_fixed_charge_vectors F B H hHG hGH beta
    (actualBasis F B i) hcharge (degree i) hdegree
  have hsector : actualBasis F B i ∈ fixedSector H beta (indexLevel i) := by
    exact basis_mem_fixedSector F B H hHG hGH i
  have hminus :
      (LatticeBRST.totalCharge D H - d0 F beta) (actualBasis F B i) ∈
        fixedSector H beta (indexLevel i) := by
    exact Submodule.sub_mem _
      (Q_preserves F B H hHG hGH beta (indexLevel i) (actualBasis F B i) hsector)
      (d0_preserves F B H hHG hGH beta (indexLevel i) (actualBasis F B i) hsector)
  have hnorm : normalizedPerturbation F B H beta (actualBasis F B i) ∈
      fixedSector H beta (indexLevel i) := by
    unfold normalizedPerturbation
    exact h_preserves F B H hHG hGH beta (indexLevel i)
      ((LatticeBRST.totalCharge D H - d0 F beta) (actualBasis F B i)) hminus
  rw [mem_signedFiltration_iff]
  intro j hj
  have hje := (mem_fixedSector_iff F B H hHG hGH beta (indexLevel i)
      (normalizedPerturbation F B H beta (actualBasis F B i))).mp hnorm j hj
  refine ⟨hje.1, hje.2, ?_⟩
  exact hraise.2.2 j hj

include hHG hGH in
private theorem normalizedPerturbation_raises
    (level lower : ℤ) (v : State D)
    (hv : v ∈ signedFiltration F B beta level lower) :
    normalizedPerturbation F B H beta v ∈
      signedFiltration F B beta level (lower + 1) := by
  have inclusion : signedFiltration F B beta level lower ≤
      (signedFiltration F B beta level (lower + 1)).comap
        (normalizedPerturbation F B H beta) := by
    apply Submodule.span_le.mpr
    rintro v ⟨⟨⟨gamma,m⟩,S⟩, ⟨hc,he,hd⟩, rfl⟩
    dsimp only at hc
    subst gamma
    have step := normalizedPerturbation_basis_step F B H hHG hGH beta m S
    change normalizedPerturbation F B H beta (actualBasis F B (⟨beta,m⟩,S)) ∈
      signedFiltration F B beta level (lower + 1)
    rw [mem_signedFiltration_iff] at step ⊢
    intro j hj
    obtain ⟨hcj,hej,hdj⟩ := step j hj
    exact ⟨hcj, hej.trans he, by omega⟩
  exact inclusion hv

include hHG hGH in
/-- Every vector in the literal fixed charge/energy sector is killed by the
uniform finite power.  The `toNat` expression also covers empty negative-level
sectors: for `level < 0`, the same filtration exhaustion inequality is proved
arithmetically rather than assumed. -/
theorem actual_normalized_perturbation_termination
    (level : ℤ) (v : State D)
    (charge : chargeProject beta v = v)
    (energy : totalL0 H v = (groundEnergy beta + (level : ℂ) - 1) • v) :
    ((h F B beta * (LatticeBRST.totalCharge D H - d0 F beta)) ^
      (2 * level.toNat + 2)) v = 0 := by
  have iterated (k : ℕ) :
      (normalizedPerturbation F B H beta ^ k) v ∈
        signedFiltration F B beta level (-level + (k : ℤ)) := by
    induction k with
    | zero =>
      simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero] using
        sector_mem_filtration F B H hHG hGH beta level v ⟨charge,energy⟩
    | succ k ih =>
      have next := normalizedPerturbation_raises F B H hHG hGH beta
        level (-level + (k : ℤ)) _ ih
      simpa only [pow_succ', Module.End.mul_apply, Nat.cast_add, Nat.cast_one,
        add_assoc] using next
  have out := iterated (2 * level.toNat + 2)
  rw [filtration_exhausted F B beta level
    (-level + ((2 * level.toNat + 2 : ℕ) : ℤ)) (by omega)] at out
  simpa [normalizedPerturbation] using out

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTFiniteTransfer
