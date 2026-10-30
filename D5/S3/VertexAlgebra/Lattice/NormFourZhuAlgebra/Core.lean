/- GID: D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra/Core
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Internal proof core for the actual norm-four Zhu algebra and polynomial presentation. -/

import D5.S3.VertexAlgebra.Lattice.NormFourZhuFinite
import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceClosure
import D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance
import D5.S3.VertexAlgebra.HalfFock.NormFourFirstGradeSpectrum
import D5.S3.VertexAlgebra.Lattice.NormFourCosetVirasoro
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.NormFourZhuAlgebra.Core

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeSugawaraCurrents NormFourVirasoroVector NormFourVacuumIrreducible
open NormFourVacuumVertexAlgebra NormFourZhuFinite
open HalfFockSpectralFiberSource
open scoped BigOperators VertexOperator

open private word wordGrade word_mem
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible
open private finite_decomposition decomposition_direct full_field_closed
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra


def assemble (D : LatticeData) (a : Charge D) (s : ℂ) :
    (ℕ →₀ vacuumDescendants D a s) →ₗ[ℂ] vacuumDescendants D a s :=
  Finsupp.lsum ℂ (fun _ : ℕ =>
    (LinearMap.id : Module.End ℂ (vacuumDescendants D a s)))

theorem expansion_unique (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (f g : ℕ →₀ vacuumDescendants D a s)
    (hf : ∀ n, f n ∈ grade D a s n) (hg : ∀ n, g n ∈ grade D a s n)
    (he : assemble D a s f=assemble D a s g) : f=g := by
  have hfg := decomposition_direct D a ha s hs (f-g)
    (fun n => (grade D a s n).sub_mem (hf n) (hg n)) (by
      change assemble D a s (f-g)=0
      rw [map_sub,he,sub_self])
  exact sub_eq_zero.mp hfg

def chosenExpansion (D : LatticeData) (a : Charge D) (s : ℂ)
    (u : vacuumDescendants D a s) : ℕ →₀ vacuumDescendants D a s :=
  Classical.choose (finite_decomposition D a s u)

theorem chosenExpansion_sum (D : LatticeData) (a : Charge D) (s : ℂ)
    (u : vacuumDescendants D a s) : assemble D a s (chosenExpansion D a s u)=u :=
  (Classical.choose_spec (finite_decomposition D a s u)).1

theorem chosenExpansion_grade (D : LatticeData) (a : Charge D) (s : ℂ)
    (u : vacuumDescendants D a s) (n : ℕ) :
    chosenExpansion D a s u n ∈ grade D a s n :=
  (Classical.choose_spec (finite_decomposition D a s u)).2 n

-- Uniqueness, rather than an arbitrary choice of coefficients, proves
-- that this actual finite decomposition is a LINEAR map.
def expansion (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    vacuumDescendants D a s →ₗ[ℂ] (ℕ →₀ vacuumDescendants D a s) where
  toFun := chosenExpansion D a s
  map_add' u v := expansion_unique D a ha s hs _ _
    (chosenExpansion_grade D a s (u+v))
    (fun n => (grade D a s n).add_mem
      (chosenExpansion_grade D a s u n) (chosenExpansion_grade D a s v n)) (by
        rw [map_add,chosenExpansion_sum,chosenExpansion_sum,chosenExpansion_sum])
  map_smul' c u := expansion_unique D a ha s hs _ _
    (chosenExpansion_grade D a s (c • u))
    (fun n => (grade D a s n).smul_mem c (chosenExpansion_grade D a s u n)) (by
      rw [map_smul,chosenExpansion_sum,chosenExpansion_sum]
      rfl)

theorem expansion_single (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (n : ℕ) (u : vacuumDescendants D a s) (hu : u ∈ grade D a s n) :
    expansion D a ha s hs u=Finsupp.single n u := by
  apply expansion_unique D a ha s hs _ _ (chosenExpansion_grade D a s u)
  · intro j
    by_cases hj : j=n
    · subst j
      simpa only [Finsupp.single_eq_same] using hu
    · simp only [Finsupp.single_eq_of_ne hj]
      exact (grade D a s j).zero_mem
  · rw [chosenExpansion_sum]
    simp [assemble,Finsupp.lsum_single]

def rawProduct (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (q : ℤ) :
    vacuumDescendants D a s →ₗ[ℂ]
      vacuumDescendants D a s →ₗ[ℂ] vacuumDescendants D a s where
  toFun u :=
    { toFun := fun v => ⟨mu D u.val q v.val,
        full_field_closed D a ha s hs u.val u.property q v.val v.property⟩
      map_add' := fun v w => Subtype.ext (by simp [mu])
      map_smul' := fun c v => Subtype.ext (by simp [mu]) }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [mu,map_add,LinearMap.add_apply,Pi.add_apply]
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp [mu,map_smul,LinearMap.smul_apply,Pi.smul_apply]

-- Defined even on inhomogeneous arguments; canonical expansion selects
-- the genuine left weight before this finite binomial operator is used.
def binomialProduct (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (n : ℕ) :
    vacuumDescendants D a s →ₗ[ℂ]
      vacuumDescendants D a s →ₗ[ℂ] vacuumDescendants D a s :=
  ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) •
    rawProduct D a ha s hs ((j:ℤ)-1)

-- A single actual bilinear product on the ENTIRE vacuum algebra.
-- Finsupp.lsum performs the finite left grade sum without postulating
-- globally finite support for the sequence of bilinear operators.
def star (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    vacuumDescendants D a s →ₗ[ℂ]
      vacuumDescendants D a s →ₗ[ℂ] vacuumDescendants D a s :=
  (Finsupp.lsum ℂ (fun n : ℕ => binomialProduct D a ha s hs n)).comp
    (expansion D a ha s hs)

theorem star_homogeneous (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (n : ℕ) (u v : vacuumDescendants D a s) (hu : u ∈ grade D a s n) :
    star D a ha s hs u v=binomialProduct D a ha s hs n u v := by
  change (Finsupp.lsum ℂ (fun n : ℕ => binomialProduct D a ha s hs n))
    (expansion D a ha s hs u) v = _
  rw [expansion_single D a ha s hs n u hu,Finsupp.lsum_single]

def vacuumState (D : LatticeData) (a : Charge D) (s : ℂ) :
    vacuumDescendants D a s := ⟨vacuum D,word_mem D a s []⟩

theorem binomialProduct_vacuum (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (n : ℕ) (u : vacuumDescendants D a s) :
    binomialProduct D a ha s hs n u (vacuumState D a s)=u := by
  classical
  apply Subtype.ext
  simp only [binomialProduct, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul]
  change (∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) •
    mu D u.val ((j:ℤ)-1) (vacuum D)) = u.val
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right,Nat.cast_one,one_smul,Nat.cast_zero,
      zero_sub,mu,stateField_creation]
  · intro j _ hj
    have hz : mu D u.val ((j:ℤ)-1) (vacuum D)=0 :=
      stateField_creativity D u.val ((j:ℤ)-1) (by omega)
    rw [hz,smul_zero]
  · intro h
    exact (h (by simp)).elim

theorem star_vacuum_right (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u : vacuumDescendants D a s) : star D a ha s hs u (vacuumState D a s)=u := by
  simp only [star, LinearMap.comp_apply, Finsupp.lsum_apply, Finsupp.sum,
    LinearMap.sum_apply]
  change (∑ n ∈ (expansion D a ha s hs u).support,
    binomialProduct D a ha s hs n (expansion D a ha s hs u n)
      (vacuumState D a s)) = u
  simp_rw [binomialProduct_vacuum]
  exact chosenExpansion_sum D a s u

theorem star_vacuum_left (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u : vacuumDescendants D a s) : star D a ha s hs (vacuumState D a s) u=u := by
  rw [star_homogeneous D a ha s hs 0 _ u
    (Submodule.subset_span ⟨[],rfl,rfl⟩)]
  apply Subtype.ext
  simp [binomialProduct,rawProduct,vacuumState,mu,stateField_vacuum,identity_modes]



open D5.S3.VertexAlgebra
open LatticeHalfFockGroundRightCurrentTransport
open LatticeHalfFockGroundRightCurrentTransport.Calculus
open scoped BigOperators VertexOperator


theorem natural_left_residue {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (U : ℤ → VertexOperator ℂ M)
    (law : fullLaw A B U 0) (α : ℕ) (q r : ℤ) (x : M) :
    (∑ j ∈ Finset.range (α+1), (α.choose j:ℂ) •
      ((U (r+j))[[((α:ℤ)+q-j)]]) x) =
      (∑ᶠ j : ℕ, firstTerm A B α q r x j) -
      (∑ᶠ j : ℕ, secondTerm A B α q r x j) := by
  classical
  have h := (law α q r x).2.2.2
  have left : (∑ᶠ j : ℕ, leftTerm U 0 α q r x j) =
      ∑ j ∈ Finset.range (α+1), (α.choose j:ℂ) •
        ((U (r+j))[[((α:ℤ)+q-j)]]) x := by
    simp only [leftTerm,Int.cast_zero,zero_div,add_zero,Int.cast_natCast,
      Ring.choose_natCast]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have bound : α<j := by
      have hnot := Finset.mem_range.not.mp outside
      omega
    exact hj (by
      change (α.choose j : ℂ) • _ = 0
      rw [Nat.choose_eq_zero_of_lt bound]
      simp)
  rw [left] at h
  exact h

-- In the circle residue BOTH entire ordered families vanish on top.
-- No iterate tail is discarded and no O-annihilation premise is supplied.
theorem circle_residue_top {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (U : ℤ → VertexOperator ℂ M)
    (law : fullLaw A B U 0) (α β : ℕ) (x : M)
    (ha : ∀ j : ℕ, (A[[((α:ℤ)+j)]]) x=0)
    (hb : ∀ j : ℕ, (B[[((β:ℤ)+j)]]) x=0) :
    (∑ j ∈ Finset.range (α+1), (α.choose j:ℂ) •
      ((U (-2+j))[[((α:ℤ)+β-j)]]) x) = 0 := by
  have h := natural_left_residue A B U law α β (-2) x
  have first : (∑ᶠ j : ℕ, firstTerm A B α β (-2) x j)=0 := by
    simp only [firstTerm,hb,map_zero,smul_zero,finsum_zero]
  have second : (∑ᶠ j : ℕ, secondTerm A B α β (-2) x j)=0 := by
    simp only [secondTerm,ha,map_zero,smul_zero,finsum_zero]
  simpa only [first,second,sub_self] using h

-- For star only first j=0 survives; the entire second family vanishes.
theorem star_residue_top {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (U : ℤ → VertexOperator ℂ M)
    (law : fullLaw A B U 0) (α β : ℕ) (x : M)
    (ha : ∀ j : ℕ, (A[[((α:ℤ)+j)]]) x=0)
    (hb : ∀ j : ℕ, (B[[((β:ℤ)+j)]]) x=0) :
    (∑ j ∈ Finset.range (α+1), (α.choose j:ℂ) •
      ((U (-1+j))[[((α:ℤ)+((β:ℤ)-1)-j)]]) x) =
      (A[[((α:ℤ)-1)]]) ((B[[((β:ℤ)-1)]]) x) := by
  classical
  have h := natural_left_residue A B U law α ((β:ℤ)-1) (-1) x
  have first : (∑ᶠ j : ℕ, firstTerm A B α ((β:ℤ)-1) (-1) x j) =
      (A[[((α:ℤ)-1)]]) ((B[[((β:ℤ)-1)]]) x) := by
    rw [finsum_eq_single _ 0]
    · simp [firstTerm, residueWeight]
      congr 2 <;> omega
    · intro j hj
      have idx : ((β:ℤ)-1)+(j:ℤ)=(β:ℤ)+((j-1:ℕ):ℤ) := by omega
      simp only [firstTerm]
      rw [idx,hb,map_zero,smul_zero]
  have second : (∑ᶠ j : ℕ, secondTerm A B α ((β:ℤ)-1) (-1) x j)=0 := by
    simp only [secondTerm,ha,map_zero,smul_zero,finsum_zero]
  simpa only [first,second,sub_zero] using h


open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeHalfFockGradedTrace
open HalfFock.ActualEnergyCovariance
open HalfFock.NormFourLowestGrades HalfFock.NormFourFirstGradeSpectrum


theorem negative_actual_grade_zero (D : LatticeData)
    (hu : IsUnit D.G.det) (M : ℤ) (hM : M<0) (x : ActualTensor D hu)
    (hx : actualTensorL0 D hu x=
      ((D.rank:ℂ)/16+(M:ℂ)/2) • x) : x=0 := by
  let b := actualAmbientBasis D hu
  apply b.repr.injective
  rw [map_zero]
  apply Finsupp.ext
  intro ib
  change b.repr x ib=0
  have coefficient_ne :
      ((D.rank:ℂ)/16+(oddWeight D ib.1:ℂ)/2)-
        ((D.rank:ℂ)/16+(M:ℂ)/2) ≠ 0 := by
    intro he
    have same : (oddWeight D ib.1:ℂ)=(M:ℂ) := by
      linear_combination 2*he
    have same_int : (oddWeight D ib.1:ℤ)=M := by exact_mod_cast same
    omega
  have coord := congrArg (fun y : ActualTensor D hu => b.repr y ib) hx
  simp only [b,actualTensorL0_repr,map_smul,Finsupp.smul_apply,smul_eq_mul] at coord
  have product :
      (((D.rank:ℂ)/16+(oddWeight D ib.1:ℂ)/2)-
        ((D.rank:ℂ)/16+(M:ℂ)/2)) * b.repr x ib=0 := by
    rw [sub_mul,coord,sub_self]
  exact (mul_eq_zero.mp product).resolve_left coefficient_ne

theorem top_eigen (D : LatticeData) (hu : IsUnit D.G.det)
    (x : ActualTensor D hu) (hx : x ∈ actualGrade D hu 1) :
    actualTensorL0 D hu x=((D.rank:ℂ)/16+((1 : ℕ):ℂ)/2) • x := by
  rw [actualGrade, LinearMap.mem_ker] at hx
  exact sub_eq_zero.mp hx

-- q>=weight(u) lowers the first grade to a genuinely negative SIGNED
-- oscillator grade. It is never truncated with Int.toNat.
theorem high_coefficient_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (u : Carrier D) (huGrade : u ∈ LatticePositiveEnergy.grade D (n:ℤ))
    (x : ActualTensor D hu) (hx : x ∈ actualGrade D hu 1)
    (q : ℤ) (hq : (n:ℤ)≤q) :
    (correctedField D hu u).coeff (-2*q-2) x=0 := by
  have shifted := correctedField_signed_output D hu (n:ℤ) 1 (-2*q-2)
    u huGrade x (top_eigen D hu x hx)
  exact negative_actual_grade_zero D hu (1+(-2*q-2)+2*(n:ℤ))
    (by omega) _ shifted

theorem zero_coefficient_preserves_top (D : LatticeData)
    (hu : IsUnit D.G.det) (n : ℕ) (u : Carrier D)
    (huGrade : u ∈ LatticePositiveEnergy.grade D (n:ℤ))
    (x : ActualTensor D hu) (hx : x ∈ actualGrade D hu 1) :
    (correctedField D hu u).coeff (-2*(n:ℤ)) x ∈ actualGrade D hu 1 := by
  have shifted := correctedField_signed_output D hu (n:ℤ) 1 (-2*(n:ℤ))
    u huGrade x (top_eigen D hu x hx)
  rw [show (1:ℤ)+(-2*(n:ℤ))+2*(n:ℤ)=1 by omega] at shifted
  rw [actualGrade, LinearMap.mem_ker]
  exact sub_eq_zero.mpr shifted

-- The general actual multiplicity equations exclude ranks zero and one,
-- and make all three spectral fibers positive in this telescope.
theorem actual_top_three_eigenspaces_positive (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) :
    2≤D.rank ∧
    0<Module.finrank ℂ ((actualGradeOneZeroMode D hu a ha s).eigenspace 0) ∧
    0<Module.finrank ℂ ((actualGradeOneZeroMode D hu a ha s).eigenspace (1/16)) ∧
    0<Module.finrank ℂ ((actualGradeOneZeroMode D hu a ha s).eigenspace (1/2)) := by
  obtain ⟨h0,h16,hh⟩ := actual_first_grade_eigenspace_multiplicities D hu a ha s hs
  have rank_two : 2≤D.rank := by
    by_contra small_rank
    have quotient_zero : D.rank/2=0 := by omega
    have impossible := hh
    rw [quotient_zero] at impossible
    norm_num only [pow_zero] at impossible
    omega
  have power_pos : 0<(2:ℕ)^(D.rank/2) := by positivity
  have zero_pos : 0<(D.rank-1)*2^(D.rank/2) :=
    Nat.mul_pos (by omega) power_pos
  have sixteen_pos : 0<D.rank*2^(D.rank/2) :=
    Nat.mul_pos (by omega) power_pos
  refine ⟨rank_two,?_,?_,?_⟩ <;> omega


open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeSugawaraVirasoro LatticeActualConformalState
open LatticeInvolution NormFourVirasoroVector NormFourVacuumIrreducible
open NormFourVacuumVertexAlgebra NormFourCosetVirasoro
open HalfFock.NormFourFirstGradeSpectrum
open scoped BigOperators VertexOperator

open private word wordGrade gradeSpace eigen_in_grade
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible


theorem word_fixed (D : LatticeData) (a : Charge D) (s : ℂ)
    (w : List ℕ) : word D a s w ∈ fixedSpace D := by
  induction w with
  | nil => exact (mem_fixedSpace D _).mpr (theta_vacuum D)
  | cons k w ih =>
      change ((Y D (vector D a s))[[-((k:ℤ)+1)+1]])
        (word D a s w) ∈ fixedSpace D
      exact fixed_mode_closed D _ _ (normFourFixedSource D a s).property ih _

theorem descendants_fixed (D : LatticeData) (a : Charge D) (s : ℂ) :
    vacuumDescendants D a s ≤ fixedSpace D := by
  apply Submodule.span_le.mpr
  rintro v ⟨w,rfl⟩
  exact word_fixed D a s w

theorem ambient_word_eigen (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (w : List ℕ) :
    sugawaraMode D H 0 (word D a s w) =
      (wordGrade w:ℂ) • word D a s w := by
  induction w with
  | nil =>
      have h := stateField_creativity D (omega D H) 1 (by omega)
      change mu D (omega D H) 1 (vacuum D)=0 at h
      simpa only [LatticeActualConformalWard.omega_product,show (1:ℤ)-1=0 by omega,
        word,wordGrade,Nat.cast_zero,zero_smul] using h
  | cons k w ih =>
      let m : ℤ := -((k:ℤ)+1)
      have h := LinearMap.congr_fun
        ((mixed_products D H hHG hGH a ha s).2 0 m) (word D a s w)
      have hm : m ≠ 0 := by dsimp [m]; omega
      simp only [zero_add, hm, ↓reduceIte, add_zero, LinearMap.sub_apply,
        Module.End.mul_apply, LinearMap.smul_apply, Int.cast_zero, zero_sub] at h
      rw [ih, map_smul] at h
      have solved := sub_eq_iff_eq_add.mp h
      change sugawaraMode D H 0 (mode D a s m (word D a s w)) = _
      rw [solved]
      simp only [word,wordGrade,m,Int.cast_neg,Int.cast_add,Int.cast_natCast,
        Int.cast_one,Nat.cast_add,Nat.cast_one,zero_sub]
      module

theorem axis_grade_ambient (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ)
    (n : ℕ) (u : vacuumDescendants D a s) (hu : u ∈ grade D a s n) :
    u.val ∈ LatticePositiveEnergy.grade D (n:ℤ) := by
  have includes : gradeSpace D a s n ≤ LatticePositiveEnergy.grade D (n:ℤ) := by
    apply Submodule.span_le.mpr
    rintro v ⟨w,hw,rfl⟩
    apply (LatticePositiveEnergy.actualL0_eigen_iff_grade D H hHG hGH (n:ℤ) _).mp
    simpa only [hw,Int.cast_natCast] using ambient_word_eigen D H hHG hGH a ha s w
  exact includes hu

-- Literal O permits any source with the stated actual axis eigenvalue.
-- Recover grade membership from the already accepted eigen_in_grade;
-- do not replace the literal O definition by a smaller graded O-space.
theorem axis_eigen_mem_grade (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1)
    (n : ℕ) (u : vacuumDescendants D a s)
    (he : mode D a s 0 u.val=(n:ℂ) • u.val) :
    u ∈ grade D a s n := by
  by_cases hz : u.val=0
  · have hu0 : u=0 := Subtype.ext hz
    rw [hu0]
    exact (grade D a s n).zero_mem
  · obtain ⟨j,hj,hnj⟩ := eigen_in_grade D a ha s hs
      (n:ℂ) u.val u.property hz he
    have same : n=j := by exact_mod_cast hnj
    subst j
    exact hj


open LatticeGeneratingFieldLocality LatticeHalfFockGradedTrace
open HalfFock.NormFourLowestGrades HalfFock.NormFourFirstGradeSpectrum


-- Consume with the actual nonzero spectral vectors; there is no assumed
-- three-dimensional representation, basis, or independent-class premise.
theorem quadratic_eigen_readout
    {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : Module.End ℂ M) (lam c0 c1 c2 : ℂ) (v : M)
    (hv : v ≠ 0) (he : L v = lam • v)
    (h : c0 • (1 : Module.End ℂ M) + c1 • L +
      c2 • (L * L + (2 : ℂ) • L) = 0) :
    c0 + c1 * lam + c2 * (lam * lam + 2 * lam) = 0 := by
  have row := LinearMap.congr_fun h v
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, Module.End.mul_apply, LinearMap.zero_apply,
    he, map_smul, smul_add, smul_smul, ← add_smul] at row
  have scalar := (smul_eq_zero.mp row).resolve_right hv
  linear_combination scalar

theorem actual_three_images_independent
    (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ)
    (h0 : 0 < Module.finrank ℂ
      ((actualGradeOneZeroMode D hu a ha s).eigenspace 0))
    (h16 : 0 < Module.finrank ℂ
      ((actualGradeOneZeroMode D hu a ha s).eigenspace (1 / 16)))
    (hh : 0 < Module.finrank ℂ
      ((actualGradeOneZeroMode D hu a ha s).eigenspace (1 / 2)))
    (c0 c1 c2 : ℂ)
    (h : c0 • (1 : Module.End ℂ (actualGrade D hu 1)) +
      c1 • actualGradeOneZeroMode D hu a ha s +
      c2 • (actualGradeOneZeroMode D hu a ha s *
        actualGradeOneZeroMode D hu a ha s +
        (2 : ℂ) • actualGradeOneZeroMode D hu a ha s) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  let L := actualGradeOneZeroMode D hu a ha s
  have readout (lam : ℂ)
      (hp : 0 < Module.finrank ℂ (L.eigenspace lam)) :
      c0 + c1 * lam + c2 * (lam * lam + 2 * lam) = 0 := by
    letI : Nontrivial (L.eigenspace lam) :=
      Module.nontrivial_of_finrank_pos hp
    obtain ⟨v, hv⟩ := exists_ne (0 : L.eigenspace lam)
    have hvval : (v : actualGrade D hu 1) ≠ 0 := by
      intro hz
      exact hv (Subtype.ext hz)
    exact quadratic_eigen_readout L lam c0 c1 c2 v.val hvval
      (Module.End.mem_eigenspace_iff.mp v.property) h
  have r0 := readout 0 h0
  have r16 := readout (1 / 16) h16
  have rh := readout (1 / 2) hh
  norm_num at r0 r16 rh
  refine ⟨r0, ?_, ?_⟩
  · linear_combination (640 / 7 : ℂ) * r16 - (66 / 7 : ℂ) * rh -
      (82 : ℂ) * r0
  · linear_combination -(256 / 7 : ℂ) * r16 + (32 / 7 : ℂ) * rh +
      (32 : ℂ) * r0

-- The actual first-grade cubic has the same monic factor order as
-- the polynomial used for the quotient presentation.


open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeHalfFockGradedTrace
open LatticeHalfFockPhysicalRescaling NormFourVacuumIrreducible
open NormFourVacuumVertexAlgebra HalfFock.ActualEnergyCovariance
open HalfFock.NormFourLowestGrades LatticeAllStateField
open scoped BigOperators VertexOperator

open private coefficient
  from D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance
open private actualInverse_left_local actualInverse_right_local
  from D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
open private axisState
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra
open private word wordGrade gradeSpace
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible
open private vacuum_coeff
  from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds


def nativeZero (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) (n : ℕ) :
    vacuumDescendants D a s →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) :=
  ((coefficient D hu (-2*(n:ℤ))).comp (correctedField D hu)).comp
    (vacuumDescendants D a s).subtype

def oAmbient (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    vacuumDescendants D a s →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) :=
  (Finsupp.lsum ℂ (fun n : ℕ => nativeZero D hu a s n)).comp
    (expansion D a ha s hs)

theorem oAmbient_homogeneous (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) (n : ℕ) (u : vacuumDescendants D a s)
    (hgrade : u ∈ grade D a s n) :
    oAmbient D hu a ha s hs u =
      (correctedField D hu u.val).coeff (-2*(n:ℤ)) := by
  change (Finsupp.lsum ℂ (fun n : ℕ => nativeZero D hu a s n))
    (expansion D a ha s hs u) = _
  rw [expansion_single D a ha s hs n u hgrade,Finsupp.lsum_single]
  rfl

theorem nativeZero_preserves_top (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (n : ℕ) (u : vacuumDescendants D a s)
    (hgrade : u ∈ grade D a s n) (x : ActualTensor D hu)
    (hx : x ∈ actualGrade D hu 1) :
    nativeZero D hu a s n u x ∈ actualGrade D hu 1 := by
  exact zero_coefficient_preserves_top D hu n u.val
    (axis_grade_ambient D (actualInverse D)
      (actualInverse_left_local D hu) (actualInverse_right_local D hu)
      a ha s n u hgrade) x hx

-- Preserve the full first grade by the actual finite homogeneous sum;
-- never project an arbitrary ambient vector back into a chosen subspace.
theorem oAmbient_preserves_top (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) (u : vacuumDescendants D a s)
    (x : ActualTensor D hu) (hx : x ∈ actualGrade D hu 1) :
    oAmbient D hu a ha s hs u x ∈ actualGrade D hu 1 := by
  change (∑ n ∈ (expansion D a ha s hs u).support,
    nativeZero D hu a s n (expansion D a ha s hs u n)) x ∈ _
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro n _
  exact nativeZero_preserves_top D hu a ha s n _
    (chosenExpansion_grade D a s u n) x hx

def topAction (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    vacuumDescendants D a s →ₗ[ℂ] Module.End ℂ (actualGrade D hu 1) where
  toFun u := (oAmbient D hu a ha s hs u).restrict
    (oAmbient_preserves_top D hu a ha s hs u)
  map_add' u v := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun ((oAmbient D hu a ha s hs).map_add u v) x.val
  map_smul' c u := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun ((oAmbient D hu a ha s hs).map_smul c u) x.val

theorem topAction_vacuum (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) :
    topAction D hu a ha s hs (vacuumState D a s)=1 := by
  have hg : vacuumState D a s ∈ grade D a s 0 :=
    Submodule.subset_span ⟨[],rfl,rfl⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change oAmbient D hu a ha s hs (vacuumState D a s) x.val=x.val
  rw [oAmbient_homogeneous D hu a ha s hs 0 _ hg]
  simpa [vacuumState] using vacuum_coeff D hu 0 x.val

theorem axisState_grade_two (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    axisState D a ha s hs ∈ grade D a s 2 := by
  change NormFourVirasoroVector.vector D a s ∈ gradeSpace D a s 2
  have word_axis : word D a s [1]=NormFourVirasoroVector.vector D a s := by
    change LatticeAllStateReconstruction.mu D
      (NormFourVirasoroVector.vector D a s) (-1) (vacuum D)=_
    exact stateField_creation D _
  rw [← word_axis]
  exact Submodule.subset_span ⟨[1],rfl,rfl⟩

theorem topAction_axis (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) :
    topAction D hu a ha s hs (axisState D a ha s hs)=
      actualGradeOneZeroMode D hu a ha s := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change oAmbient D hu a ha s hs (axisState D a ha s hs) x.val=
    zeroMode D hu a s x.val
  rw [oAmbient_homogeneous D hu a ha s hs 2 _
    (axisState_grade_two D a ha s hs)]
  rfl


open LatticeGeneratingFieldLocality LatticeAllStateReconstruction
open LatticeAllStateField LatticeSugawaraConformal
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeHalfFockPhysicalRescaling
open LatticeHalfFockGroundRightCurrentTransport
open LatticeHalfFockGroundRightCurrentTransport.Calculus LatticeInvolution
open NormFourVacuumIrreducible NormFourVacuumVertexAlgebra
open NormFourZhuFinite
open scoped BigOperators VertexOperator

open private coefficient_weight_eigen
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra
open private zhu_three_spanning zhuO_le
  from D5.S3.VertexAlgebra.Lattice.NormFourZhuFinite
open private representatives representatives_mem small small_le
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2
open private axisState
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra
open private actualInverse_left_local actualInverse_right_local
  from D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace


def weightedProduct (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1)
    (α : ℕ) (k : ℤ) (u v : vacuumDescendants D a s) :
    vacuumDescendants D a s :=
  ∑ j ∈ Finset.range (α+1), (α.choose j:ℂ) •
    rawProduct D a ha s hs (k+(j:ℤ)) u v

-- k=-2 is circle, k=-1 is star. Every result grade is nonnegative;
-- Int.toNat below is used only AFTER that inequality is proved.
theorem weightedProduct_zero_mode (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) (α β : ℕ) (k : ℤ) (hk : k≤-1)
    (u v : vacuumDescendants D a s) (hu : u ∈ grade D a s α)
    (hv : v ∈ grade D a s β) (x : ActualTensor D hd) :
    oAmbient D hd a ha s hs (weightedProduct D a ha s hs α k u v) x =
      ∑ j ∈ Finset.range (α+1), (α.choose j:ℂ) •
        ((physicalSlice D hd
          (correctedField D hd (mu D u.val (k+j) v.val)) 0)
          [[(α:ℤ)+β-k-2-j]]) x := by
  classical
  unfold weightedProduct
  rw [map_sum]
  simp only [map_smul,LinearMap.sum_apply,LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have jle : j≤α := by have := Finset.mem_range.mp hj; omega
  let n : ℕ := ((α:ℤ)+β-(k+j)-1).toNat
  have nonneg : 0≤(α:ℤ)+β-(k+j)-1 := by omega
  have nn : (n:ℤ)=(α:ℤ)+β-(k+j)-1 := Int.toNat_of_nonneg nonneg
  have he := coefficient_weight_eigen D a ha s hs α β (k+j) u v hu hv
  have hgrade : rawProduct D a ha s hs (k+j) u v ∈ grade D a s n := by
    apply axis_eigen_mem_grade D a ha s hs n
    change mode D a s 0 (mu D u.val (k+j) v.val)=(n:ℂ) • _
    rw [← nn,Int.cast_natCast] at he
    exact he
  congr 1
  rw [oAmbient_homogeneous D hd a ha s hs n _ hgrade,physicalSlice_mode]
  change (correctedField D hd (mu D u.val (k+j) v.val)).coeff (-2*(n:ℤ)) x = _
  congr 2
  rw [nn]
  push_cast
  ring

theorem descendants_full_law (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (s : ℂ)
    (u v : vacuumDescendants D a s) :
    fullLaw (physicalSlice D hd (correctedField D hd u.val) 0)
      (physicalSlice D hd (correctedField D hd v.val) 0)
      (fun r => physicalSlice D hd
        (correctedField D hd (mu D u.val r v.val)) 0) 0 := by
  have he : theta D u.val=(-1:ℂ)^(0:ℤ) • u.val := by
    simpa using (mem_fixedSpace D u.val).mp
      (descendants_fixed D a s u.property)
  simpa only [OriginalCompatible,zero_add] using
    first_eigen_arbitrary_second D hd u.val 0 he v.val 0

theorem high_physical_mode_zero (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (α : ℕ) (u : vacuumDescendants D a s)
    (hu : u ∈ grade D a s α) (x : ActualTensor D hd)
    (hx : x ∈ actualGrade D hd 1) (j : ℕ) :
    ((physicalSlice D hd (correctedField D hd u.val) 0)[[(α:ℤ)+j]]) x=0 := by
  rw [physicalSlice_mode]
  simp only [sub_zero]
  exact high_coefficient_zero D hd α u.val
    (axis_grade_ambient D (actualInverse D)
      (actualInverse_left_local D hd) (actualInverse_right_local D hd)
      a ha s α u hu) x hx ((α:ℤ)+j) (by omega)

theorem actual_circle_annihilates_top (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) (α β : ℕ)
    (u v : vacuumDescendants D a s) (hu : u ∈ grade D a s α)
    (hv : v ∈ grade D a s β) (x : ActualTensor D hd)
    (hx : x ∈ actualGrade D hd 1) :
    oAmbient D hd a ha s hs (weightedProduct D a ha s hs α (-2) u v) x=0 := by
  rw [weightedProduct_zero_mode D hd a ha s hs α β (-2) (by norm_num) u v hu hv x]
  have indices (j : ℕ) : (α:ℤ)+β-(-2)-2-j=(α:ℤ)+β-j := by omega
  simp_rw [indices]
  exact circle_residue_top _ _ _ (descendants_full_law D hd a s u v) α β x
    (high_physical_mode_zero D hd a ha s α u hu x hx)
    (high_physical_mode_zero D hd a ha s β v hv x hx)

theorem actual_star_multiplies_top (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) (α β : ℕ)
    (u v : vacuumDescendants D a s) (hu : u ∈ grade D a s α)
    (hv : v ∈ grade D a s β) (x : ActualTensor D hd)
    (hx : x ∈ actualGrade D hd 1) :
    oAmbient D hd a ha s hs (weightedProduct D a ha s hs α (-1) u v) x=
      oAmbient D hd a ha s hs u (oAmbient D hd a ha s hs v x) := by
  rw [weightedProduct_zero_mode D hd a ha s hs α β (-1) (by norm_num) u v hu hv x]
  have indices (j : ℕ) : (α:ℤ)+β-(-1)-2-j=(α:ℤ)+((β:ℤ)-1)-j := by omega
  simp_rw [indices]
  have u_mode : oAmbient D hd a ha s hs u=
      (physicalSlice D hd (correctedField D hd u.val) 0)[[(α:ℤ)-1]] := by
    rw [oAmbient_homogeneous D hd a ha s hs α u hu,physicalSlice_mode]
    congr 1
    push_cast
    ring
  have v_mode : oAmbient D hd a ha s hs v=
      (physicalSlice D hd (correctedField D hd v.val) 0)[[(β:ℤ)-1]] := by
    rw [oAmbient_homogeneous D hd a ha s hs β v hv,physicalSlice_mode]
    congr 1
    push_cast
    ring
  rw [u_mode,v_mode]
  exact star_residue_top _ _ _ (descendants_full_law D hd a s u v) α β x
    (high_physical_mode_zero D hd a ha s α u hu x hx)
    (high_physical_mode_zero D hd a ha s β v hv x hx)

theorem actual_star_homogeneous_action (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) (α β : ℕ)
    (u v : vacuumDescendants D a s) (hu : u ∈ grade D a s α)
    (hv : v ∈ grade D a s β) :
    topAction D hd a ha s hs (star D a ha s hs u v)=
      topAction D hd a ha s hs u * topAction D hd a ha s hs v := by
  rw [star_homogeneous D a ha s hs α u v hu]
  have same : binomialProduct D a ha s hs α u v=
      weightedProduct D a ha s hs α (-1) u v := by
    simp only [binomialProduct,weightedProduct,LinearMap.sum_apply,
      LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (j:ℤ)-1=(-1:ℤ)+j by omega]
  rw [same]
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact actual_star_multiplies_top D hd a ha s hs α β u v hu hv
    x.val x.property
