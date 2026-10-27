/- GID: D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual star algebra and polynomial presentation of the literal norm-four Zhu quotient. -/

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

namespace D5.S3.VertexAlgebra.Lattice.NormFourZhuAlgebra

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeSugawaraCurrents NormFourVirasoroVector NormFourVacuumIrreducible
open NormFourVacuumVertexAlgebra NormFourZhuFinite
open HalfFockSpectralFiberSource
open scoped BigOperators VertexOperator

open private word wordGrade word_mem
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible
open private finite_decomposition decomposition_direct full_field_closed
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra


private def assemble (D : LatticeData) (a : Charge D) (s : ℂ) :
    (ℕ →₀ vacuumDescendants D a s) →ₗ[ℂ] vacuumDescendants D a s :=
  Finsupp.lsum ℂ (fun _ : ℕ =>
    (LinearMap.id : Module.End ℂ (vacuumDescendants D a s)))

private theorem expansion_unique (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (f g : ℕ →₀ vacuumDescendants D a s)
    (hf : ∀ n, f n ∈ grade D a s n) (hg : ∀ n, g n ∈ grade D a s n)
    (he : assemble D a s f=assemble D a s g) : f=g := by
  have hfg := decomposition_direct D a ha s hs (f-g)
    (fun n => (grade D a s n).sub_mem (hf n) (hg n)) (by
      change assemble D a s (f-g)=0
      rw [map_sub,he,sub_self])
  exact sub_eq_zero.mp hfg

private def chosenExpansion (D : LatticeData) (a : Charge D) (s : ℂ)
    (u : vacuumDescendants D a s) : ℕ →₀ vacuumDescendants D a s :=
  Classical.choose (finite_decomposition D a s u)

private theorem chosenExpansion_sum (D : LatticeData) (a : Charge D) (s : ℂ)
    (u : vacuumDescendants D a s) : assemble D a s (chosenExpansion D a s u)=u :=
  (Classical.choose_spec (finite_decomposition D a s u)).1

private theorem chosenExpansion_grade (D : LatticeData) (a : Charge D) (s : ℂ)
    (u : vacuumDescendants D a s) (n : ℕ) :
    chosenExpansion D a s u n ∈ grade D a s n :=
  (Classical.choose_spec (finite_decomposition D a s u)).2 n

-- Uniqueness, rather than an arbitrary choice of coefficients, proves
-- that this actual finite decomposition is a LINEAR map.
private def expansion (D : LatticeData) (a : Charge D)
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

private theorem expansion_single (D : LatticeData) (a : Charge D)
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

private def rawProduct (D : LatticeData) (a : Charge D)
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
private def binomialProduct (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (n : ℕ) :
    vacuumDescendants D a s →ₗ[ℂ]
      vacuumDescendants D a s →ₗ[ℂ] vacuumDescendants D a s :=
  ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) •
    rawProduct D a ha s hs ((j:ℤ)-1)

-- A single actual bilinear product on the ENTIRE vacuum algebra.
-- Finsupp.lsum performs the finite left grade sum without postulating
-- globally finite support for the sequence of bilinear operators.
private def star (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    vacuumDescendants D a s →ₗ[ℂ]
      vacuumDescendants D a s →ₗ[ℂ] vacuumDescendants D a s :=
  (Finsupp.lsum ℂ (fun n : ℕ => binomialProduct D a ha s hs n)).comp
    (expansion D a ha s hs)

private theorem star_homogeneous (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (n : ℕ) (u v : vacuumDescendants D a s) (hu : u ∈ grade D a s n) :
    star D a ha s hs u v=binomialProduct D a ha s hs n u v := by
  change (Finsupp.lsum ℂ (fun n : ℕ => binomialProduct D a ha s hs n))
    (expansion D a ha s hs u) v = _
  rw [expansion_single D a ha s hs n u hu,Finsupp.lsum_single]

private def vacuumState (D : LatticeData) (a : Charge D) (s : ℂ) :
    vacuumDescendants D a s := ⟨vacuum D,word_mem D a s []⟩

private theorem binomialProduct_vacuum (D : LatticeData) (a : Charge D)
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

private theorem star_vacuum_right (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u : vacuumDescendants D a s) : star D a ha s hs u (vacuumState D a s)=u := by
  simp only [star, LinearMap.comp_apply, Finsupp.lsum_apply, Finsupp.sum,
    LinearMap.sum_apply]
  change (∑ n ∈ (expansion D a ha s hs u).support,
    binomialProduct D a ha s hs n (expansion D a ha s hs u n)
      (vacuumState D a s)) = u
  simp_rw [binomialProduct_vacuum]
  exact chosenExpansion_sum D a s u

private theorem star_vacuum_left (D : LatticeData) (a : Charge D)
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


private theorem natural_left_residue {M : Type*} [AddCommGroup M] [Module ℂ M]
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
private theorem circle_residue_top {M : Type*} [AddCommGroup M] [Module ℂ M]
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
private theorem star_residue_top {M : Type*} [AddCommGroup M] [Module ℂ M]
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


private theorem negative_actual_grade_zero (D : LatticeData)
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

private theorem top_eigen (D : LatticeData) (hu : IsUnit D.G.det)
    (x : ActualTensor D hu) (hx : x ∈ actualGrade D hu 1) :
    actualTensorL0 D hu x=((D.rank:ℂ)/16+((1 : ℕ):ℂ)/2) • x := by
  rw [actualGrade, LinearMap.mem_ker] at hx
  exact sub_eq_zero.mp hx

-- q>=weight(u) lowers the first grade to a genuinely negative SIGNED
-- oscillator grade. It is never truncated with Int.toNat.
private theorem high_coefficient_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (u : Carrier D) (huGrade : u ∈ LatticePositiveEnergy.grade D (n:ℤ))
    (x : ActualTensor D hu) (hx : x ∈ actualGrade D hu 1)
    (q : ℤ) (hq : (n:ℤ)≤q) :
    (correctedField D hu u).coeff (-2*q-2) x=0 := by
  have shifted := correctedField_signed_output D hu (n:ℤ) 1 (-2*q-2)
    u huGrade x (top_eigen D hu x hx)
  exact negative_actual_grade_zero D hu (1+(-2*q-2)+2*(n:ℤ))
    (by omega) _ shifted

private theorem zero_coefficient_preserves_top (D : LatticeData)
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
private theorem actual_top_three_eigenspaces_positive (D : LatticeData)
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


private theorem word_fixed (D : LatticeData) (a : Charge D) (s : ℂ)
    (w : List ℕ) : word D a s w ∈ fixedSpace D := by
  induction w with
  | nil => exact (mem_fixedSpace D _).mpr (theta_vacuum D)
  | cons k w ih =>
      change ((Y D (vector D a s))[[-((k:ℤ)+1)+1]])
        (word D a s w) ∈ fixedSpace D
      exact fixed_mode_closed D _ _ (normFourFixedSource D a s).property ih _

private theorem descendants_fixed (D : LatticeData) (a : Charge D) (s : ℂ) :
    vacuumDescendants D a s ≤ fixedSpace D := by
  apply Submodule.span_le.mpr
  rintro v ⟨w,rfl⟩
  exact word_fixed D a s w

private theorem ambient_word_eigen (D : LatticeData)
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

private theorem axis_grade_ambient (D : LatticeData)
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
private theorem axis_eigen_mem_grade (D : LatticeData) (a : Charge D)
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
private theorem quadratic_eigen_readout
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

private theorem actual_three_images_independent
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


private def nativeZero (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) (n : ℕ) :
    vacuumDescendants D a s →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) :=
  ((coefficient D hu (-2*(n:ℤ))).comp (correctedField D hu)).comp
    (vacuumDescendants D a s).subtype

private def oAmbient (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    vacuumDescendants D a s →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) :=
  (Finsupp.lsum ℂ (fun n : ℕ => nativeZero D hu a s n)).comp
    (expansion D a ha s hs)

private theorem oAmbient_homogeneous (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) (n : ℕ) (u : vacuumDescendants D a s)
    (hgrade : u ∈ grade D a s n) :
    oAmbient D hu a ha s hs u =
      (correctedField D hu u.val).coeff (-2*(n:ℤ)) := by
  change (Finsupp.lsum ℂ (fun n : ℕ => nativeZero D hu a s n))
    (expansion D a ha s hs u) = _
  rw [expansion_single D a ha s hs n u hgrade,Finsupp.lsum_single]
  rfl

private theorem nativeZero_preserves_top (D : LatticeData)
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
private theorem oAmbient_preserves_top (D : LatticeData)
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

private def topAction (D : LatticeData) (hu : IsUnit D.G.det)
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

private theorem topAction_vacuum (D : LatticeData)
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

private theorem axisState_grade_two (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    axisState D a ha s hs ∈ grade D a s 2 := by
  change NormFourVirasoroVector.vector D a s ∈ gradeSpace D a s 2
  have word_axis : word D a s [1]=NormFourVirasoroVector.vector D a s := by
    change LatticeAllStateReconstruction.mu D
      (NormFourVirasoroVector.vector D a s) (-1) (vacuum D)=_
    exact stateField_creation D _
  rw [← word_axis]
  exact Submodule.subset_span ⟨[1],rfl,rfl⟩

private theorem topAction_axis (D : LatticeData)
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


private def weightedProduct (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1)
    (α : ℕ) (k : ℤ) (u v : vacuumDescendants D a s) :
    vacuumDescendants D a s :=
  ∑ j ∈ Finset.range (α+1), (α.choose j:ℂ) •
    rawProduct D a ha s hs (k+(j:ℤ)) u v

-- k=-2 is circle, k=-1 is star. Every result grade is nonnegative;
-- Int.toNat below is used only AFTER that inequality is proved.
private theorem weightedProduct_zero_mode (D : LatticeData)
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

private theorem descendants_full_law (D : LatticeData)
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

private theorem high_physical_mode_zero (D : LatticeData)
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

private theorem actual_circle_annihilates_top (D : LatticeData)
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

private theorem actual_star_multiplies_top (D : LatticeData)
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

private theorem actual_star_homogeneous_action (D : LatticeData)
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

-- Both arguments range over the WHOLE actual vacuum algebra. Finite
-- expansions are supplied by its proved direct word grading, rather
-- than by a new representation or homogeneous-state assumption.
private theorem actual_star_action_finsupp (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1)
    (f g : ℕ →₀ vacuumDescendants D a s)
    (hf : ∀ n, f n ∈ grade D a s n)
    (hg : ∀ n, g n ∈ grade D a s n) :
    topAction D hd a ha s hs
        (star D a ha s hs (assemble D a s f) (assemble D a s g)) =
      topAction D hd a ha s hs (assemble D a s f) *
        topAction D hd a ha s hs (assemble D a s g) := by
  classical
  change topAction D hd a ha s hs
      (star D a ha s hs (∑ α ∈ f.support, f α) (∑ β ∈ g.support, g β)) =
    topAction D hd a ha s hs (∑ α ∈ f.support, f α) *
      topAction D hd a ha s hs (∑ β ∈ g.support, g β)
  rw [LinearMap.map_sum₂]
  simp only [map_sum]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  exact actual_star_homogeneous_action D hd a ha s hs α β (f α) (g β)
    (hf α) (hg β)

private theorem actual_star_action (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) (u v : vacuumDescendants D a s) :
    topAction D hd a ha s hs (star D a ha s hs u v)=
      topAction D hd a ha s hs u * topAction D hd a ha s hs v := by
  classical
  let f := chosenExpansion D a s u
  let g := chosenExpansion D a s v
  have fu : assemble D a s f=u := chosenExpansion_sum D a s u
  have gv : assemble D a s g=v := chosenExpansion_sum D a s v
  rw [← fu,← gv]
  exact actual_star_action_finsupp D hd a ha s hs f g
    (chosenExpansion_grade D a s u) (chosenExpansion_grade D a s v)

private theorem actual_circle_all_right_states (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) (α : ℕ)
    (u v : vacuumDescendants D a s) (hu : u ∈ grade D a s α)
    (x : ActualTensor D hd) (hx : x ∈ actualGrade D hd 1) :
    oAmbient D hd a ha s hs (weightedProduct D a ha s hs α (-2) u v) x=0 := by
  classical
  let R : vacuumDescendants D a s →ₗ[ℂ] vacuumDescendants D a s :=
    ∑ j ∈ Finset.range (α+1), (α.choose j:ℂ) •
      rawProduct D a ha s hs (-2+(j:ℤ)) u
  have hR (w : vacuumDescendants D a s) :
      R w=weightedProduct D a ha s hs α (-2) u w := by
    simp only [R,weightedProduct,LinearMap.sum_apply,LinearMap.smul_apply]
  rw [← hR v]
  let f := chosenExpansion D a s v
  have hv : assemble D a s f=v := chosenExpansion_sum D a s v
  rw [← hv]
  change oAmbient D hd a ha s hs (R (∑ β ∈ f.support, f β)) x=0
  rw [map_sum,map_sum]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro β _
  rw [hR]
  exact actual_circle_annihilates_top D hd a ha s hs α β u (f β) hu
    (chosenExpansion_grade D a s v β) x hx

-- This is the original literal O, including all right states and every
-- source satisfying the actual axis eigenvalue equation. No smaller
-- graded O or ideal is substituted for it.
private theorem literal_O_le_topAction_kernel (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) :
    (zhuO D a s).comap (vacuumDescendants D a s).subtype ≤
      (topAction D hd a ha s hs).ker := by
  classical
  let S := vacuumDescendants D a s
  let K := (topAction D hd a ha s hs).ker
  have includes : zhuO D a s ≤ K.map S.subtype := by
    apply Submodule.span_le.mpr
    rintro z ⟨α,u,v,hu,hv,he,rfl⟩
    let uS : S := ⟨u,hu⟩
    let vS : S := ⟨v,hv⟩
    let w : S := weightedProduct D a ha s hs α (-2) uS vS
    have hwval : w.val=circle D α u v := by
      simp only [w,weightedProduct,Submodule.coe_sum,Submodule.coe_smul]
      change (∑ j ∈ Finset.range (α+1), (α.choose j:ℂ) •
        mu D u (-2+(j:ℤ)) v) =
        ∑ j ∈ Finset.range (α+1), (α.choose j:ℂ) • mu D u ((j:ℤ)-2) v
      apply Finset.sum_congr rfl
      intro j _
      rw [show (-2:ℤ)+j=(j:ℤ)-2 by omega]
    have hwker : w ∈ K := by
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change oAmbient D hd a ha s hs w x.val=0
      exact actual_circle_all_right_states D hd a ha s hs α uS vS
        (axis_eigen_mem_grade D a ha s hs α uS he) x.val x.property
    exact Submodule.mem_map.mpr ⟨w,hwker,hwval⟩
  intro z hz
  obtain ⟨w,hw,he⟩ := Submodule.mem_map.mp (includes hz)
  have same : w=z := Subtype.ext he
  exact same ▸ hw

private def axisSquare (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    vacuumDescendants D a s :=
  rawProduct D a ha s hs (-1) (axisState D a ha s hs) (axisState D a ha s hs)

private def axisDerivative (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    vacuumDescendants D a s :=
  rawProduct D a ha s hs 0 (axisState D a ha s hs) (axisState D a ha s hs)

-- The two identities below use the actual self-OPE and actual -2 vacuum
-- creation law; b is the SAME second representative from C2 spanning.
private theorem axis_circle_vacuum (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    weightedProduct D a ha s hs 2 (-2) (axisState D a ha s hs)
      (vacuumState D a s)=
        axisDerivative D a ha s hs+(2:ℂ) • axisState D a ha s hs := by
  apply Subtype.ext
  have hT := LatticeActualVertexAlgebra.translation_as_mode D
    (NormFourVirasoroVector.vector D a s)
  have hself := (NormFourVirasoroVector.self_products D a ha s hs).1
  have hzero := stateField_creativity D
    (NormFourVirasoroVector.vector D a s) 0 (by omega)
  have hself' : ((Y D (NormFourVirasoroVector.vector D a s))[[0]])
      (NormFourVirasoroVector.vector D a s) = translation D
        (NormFourVirasoroVector.vector D a s) := by
    simpa only [mu] using hself
  simp [weightedProduct,axisDerivative,rawProduct,axisState,vacuumState,
    Finset.sum_range_succ,mu,← hT,hzero,hself',stateField_creation]

private theorem axis_star_square (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    star D a ha s hs (axisState D a ha s hs) (axisState D a ha s hs)=
      axisSquare D a ha s hs+(2:ℂ) • axisDerivative D a ha s hs+
        (2:ℂ) • axisState D a ha s hs := by
  rw [star_homogeneous D a ha s hs 2 _ _ (axisState_grade_two D a ha s hs)]
  apply Subtype.ext
  have h1 := (NormFourVirasoroVector.self_products D a ha s hs).2.1
  simp [binomialProduct,axisSquare,axisDerivative,rawProduct,axisState,
    Finset.sum_range_succ,h1]

private theorem topAction_axisSquare (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) :
    topAction D hd a ha s hs (axisSquare D a ha s hs)=
      HalfFock.NormFourLowestGrades.actualGradeOneZeroMode D hd a ha s *
        HalfFock.NormFourLowestGrades.actualGradeOneZeroMode D hd a ha s+
      (2:ℂ) • HalfFock.NormFourLowestGrades.actualGradeOneZeroMode D hd a ha s := by
  let A := topAction D hd a ha s hs
  let e := axisState D a ha s hs
  have circle_zero : A (weightedProduct D a ha s hs 2 (-2) e
      (vacuumState D a s))=0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact actual_circle_all_right_states D hd a ha s hs 2 e
      (vacuumState D a s) (axisState_grade_two D a ha s hs) x.val x.property
  rw [axis_circle_vacuum,map_add,map_smul] at circle_zero
  have product_eq := actual_star_action D hd a ha s hs e e
  rw [axis_star_square,map_add,map_add,map_smul,map_smul] at product_eq
  have solve : A (axisSquare D a ha s hs)=A e*A e+(2:ℂ) • A e := by
    calc
      A (axisSquare D a ha s hs) = A e*A e-
          (2:ℂ) • A (axisDerivative D a ha s hs)-(2:ℂ) • A e := by
        rw [← product_eq]
        simp only [A,e]
        module
      _ = A e*A e+(2:ℂ) • A e := by
        have derivative : A (axisDerivative D a ha s hs)=-(2:ℂ) • A e := by
          calc
            A (axisDerivative D a ha s hs) = -((2 : ℂ) • A e) :=
              eq_neg_of_add_eq_zero_left circle_zero
            _ = -(2:ℂ) • A e := by
              exact (neg_smul (2 : ℂ) (A e)).symm
        rw [derivative]
        rw [smul_smul, show (2 : ℂ) * -(2 : ℂ) = -(2 + 2) by norm_num,
          neg_smul, sub_neg_eq_add, add_smul]
        abel
  simpa only [A,e,topAction_axis] using solve

private theorem small_three_scalars (D : LatticeData) (a : Charge D)
    (s : ℂ) (t : Carrier D) (ht : t ∈ small D a s) :
    ∃ c0 c1 c2 : ℂ, t=c0 • representatives D a s 0+
      c1 • representatives D a s 1+c2 • representatives D a s 2 := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨i,rfl⟩ := ht
      fin_cases i
      · exact ⟨1,0,0,by simp⟩
      · exact ⟨0,1,0,by simp⟩
      · exact ⟨0,0,1,by simp⟩
  | zero => exact ⟨0,0,0,by simp⟩
  | add u v _ _ hu hv =>
      obtain ⟨u0,u1,u2,hu⟩ := hu
      obtain ⟨v0,v1,v2,hv⟩ := hv
      refine ⟨u0+v0,u1+v1,u2+v2,?_⟩
      rw [hu,hv]
      module
  | smul c u _ hu =>
      obtain ⟨u0,u1,u2,hu⟩ := hu
      refine ⟨c*u0,c*u1,c*u2,?_⟩
      rw [hu]
      module

-- Direct exact-kernel proof: use actual filtered three-vector spanning
-- and actual spectral separation. No dimension assumption on End(top),
-- abstract representation, chosen quotient basis, or replacement O.
private theorem topAction_kernel_eq_literal_O (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) :
    (topAction D hd a ha s hs).ker=
      (zhuO D a s).comap (vacuumDescendants D a s).subtype := by
  let S := vacuumDescendants D a s
  let A := topAction D hd a ha s hs
  let r : Fin 3 → S := fun i =>
    ⟨representatives D a s i,representatives_mem D a ha s hs i⟩
  have r0 : r 0=vacuumState D a s := by
    apply Subtype.ext
    simp [r,representatives,vacuumState]
  have r1 : r 1=axisState D a ha s hs := by
    apply Subtype.ext
    simp [r,representatives,NormFourVirasoroVector.mode,axisState,
      stateField_creation]
  have r2 : r 2=axisSquare D a ha s hs := by
    apply Subtype.ext
    simp [r,representatives,pow_succ',Module.End.mul_apply,
      NormFourVirasoroVector.mode,axisSquare,rawProduct,axisState,mu,
      stateField_creation]
  apply le_antisymm
  · intro u hu
    have huA : A u=0 := LinearMap.mem_ker.mp hu
    obtain ⟨z,hz,t,ht,equal⟩ := Submodule.mem_sup.mp
      (zhu_three_spanning D a ha s hs u.property)
    let zS : S := ⟨z,zhuO_le D a ha s hs hz⟩
    let tS : S := ⟨t,small_le D a ha s hs ht⟩
    have equalS : zS+tS=u := Subtype.ext equal
    have hzA : A zS=0 := LinearMap.mem_ker.mp
      (literal_O_le_topAction_kernel D hd a ha s hs hz)
    have htA : A tS=0 := by
      have eqA := congrArg A equalS
      simpa only [map_add,hzA,zero_add,huA] using eqA
    obtain ⟨c0,c1,c2,coefficients⟩ := small_three_scalars D a s t ht
    have coefficientsS : tS=c0 • r 0+c1 • r 1+c2 • r 2 :=
      Subtype.ext coefficients
    rw [coefficientsS,map_add,map_add,map_smul,map_smul,map_smul,
      r0,r1,r2,topAction_vacuum,topAction_axis,topAction_axisSquare] at htA
    obtain ⟨_,h0,h16,hh⟩ := actual_top_three_eigenspaces_positive D hd a ha s hs
    obtain ⟨hc0,hc1,hc2⟩ := actual_three_images_independent
      D hd a ha s h0 h16 hh c0 c1 c2 htA
    have tzero : t=0 := by simp [coefficients,hc0,hc1,hc2]
    change u.val ∈ zhuO D a s
    rw [← equal,tzero,add_zero]
    exact hz
  · exact literal_O_le_topAction_kernel D hd a ha s hs

-- Both kernels required for descending the ACTUAL bilinear star. Each
-- follows from the proved exact literal kernel and actual multiplication.
private theorem literal_O_star_closed (D : LatticeData)
    (hd : IsUnit D.G.det) (a : Charge D) (ha : bilinear D a a=4)
    (s : ℂ) (hs : s ^ 2 = 1) (u v : vacuumDescendants D a s) :
    (u ∈ (zhuO D a s).comap (vacuumDescendants D a s).subtype →
      star D a ha s hs u v ∈
        (zhuO D a s).comap (vacuumDescendants D a s).subtype) ∧
    (v ∈ (zhuO D a s).comap (vacuumDescendants D a s).subtype →
      star D a ha s hs u v ∈
        (zhuO D a s).comap (vacuumDescendants D a s).subtype) := by
  rw [← topAction_kernel_eq_literal_O D hd a ha s hs]
  constructor
  · intro hu
    apply LinearMap.mem_ker.mpr
    rw [actual_star_action,LinearMap.mem_ker.mp hu,zero_mul]
  · intro hv
    apply LinearMap.mem_ker.mpr
    rw [actual_star_action,LinearMap.mem_ker.mp hv,mul_zero]


open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open NormFourVirasoroVector NormFourVacuumIrreducible NormFourVacuumVertexAlgebra
open NormFourZhuFinite LatticeHalfFockGradedTrace HalfFock.NormFourLowestGrades
open scoped BigOperators VertexOperator


private abbrev O (D : LatticeData) (a : Charge D) (s : ℂ) :=
  (zhuO D a s).comap (vacuumDescendants D a s).subtype

private abbrev Q (D : LatticeData) (a : Charge D) (s : ℂ) :=
  vacuumDescendants D a s ⧸ O D a s

private def quotientAction (D : LatticeData) (hd : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    Q D a s →ₗ[ℂ] Module.End ℂ (actualGrade D hd 1) :=
  (O D a s).liftQ (topAction D hd a ha s hs)
    (literal_O_le_topAction_kernel D hd a ha s hs)

private theorem quotientAction_injective (D : LatticeData) (hd : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    Function.Injective (quotientAction D hd a ha s hs) := by
  intro x y he
  obtain ⟨u,rfl⟩ := (O D a s).mkQ_surjective x
  obtain ⟨v,rfl⟩ := (O D a s).mkQ_surjective y
  change topAction D hd a ha s hs u=topAction D hd a ha s hs v at he
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero (O D a s)).mpr
  change u - v ∈ (zhuO D a s).comap (vacuumDescendants D a s).subtype
  rw [← topAction_kernel_eq_literal_O D hd a ha s hs]
  exact LinearMap.mem_ker.mpr (by rw [map_sub,he,sub_self])

private def seed (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :=
  (star D a ha s hs).compr₂ (O D a s).mkQ

private theorem seed_left_kernel (D : LatticeData) (hd : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    O D a s ≤ (seed D a ha s hs).ker := by
  intro u hu
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro v
  exact (Submodule.Quotient.mk_eq_zero (O D a s)).mpr
    ((literal_O_star_closed D hd a ha s hs u v).1 hu)

private theorem seed_right_kernel (D : LatticeData) (hd : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    O D a s ≤ (seed D a ha s hs).flip.ker := by
  intro v hv
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro u
  exact (Submodule.Quotient.mk_eq_zero (O D a s)).mpr
    ((literal_O_star_closed D hd a ha s hs u v).2 hv)

/-- The bilinear product on the literal additive quotient induced by the
actual finite homogeneous Zhu star product. -/
def quotientProduct (D : LatticeData) (hd : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    Q D a s →ₗ[ℂ] Q D a s →ₗ[ℂ] Q D a s :=
  (seed D a ha s hs).liftQ₂ (O D a s) (O D a s)
    (seed_left_kernel D hd a ha s hs) (seed_right_kernel D hd a ha s hs)

private theorem quotient_action_product (D : LatticeData) (hd : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1)
    (x y : Q D a s) :
    quotientAction D hd a ha s hs (quotientProduct D hd a ha s hs x y)=
      quotientAction D hd a ha s hs x * quotientAction D hd a ha s hs y := by
  obtain ⟨u,rfl⟩ := (O D a s).mkQ_surjective x
  obtain ⟨v,rfl⟩ := (O D a s).mkQ_surjective y
  exact actual_star_action D hd a ha s hs u v

private def rep (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) (i : Fin 3) :
    vacuumDescendants D a s :=
  ⟨representatives D a s i,representatives_mem D a ha s hs i⟩

private theorem rep_eq (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    rep D a ha s hs 0=vacuumState D a s ∧
    rep D a ha s hs 1=axisState D a ha s hs ∧
    rep D a ha s hs 2=axisSquare D a ha s hs := by
  refine ⟨Subtype.ext ?_,Subtype.ext ?_,Subtype.ext ?_⟩
  · simp [rep,representatives,vacuumState]
  · simp [rep,representatives,NormFourVirasoroVector.mode,axisState,stateField_creation]
  · simp [rep,representatives,pow_succ',Module.End.mul_apply,
      NormFourVirasoroVector.mode,axisSquare,rawProduct,axisState,mu,stateField_creation]

private theorem quotient_three_scalars (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) (x : Q D a s) :
    ∃ c0 c1 c2 : ℂ, x=
      c0 • (O D a s).mkQ (rep D a ha s hs 0)+
      c1 • (O D a s).mkQ (rep D a ha s hs 1)+
      c2 • (O D a s).mkQ (rep D a ha s hs 2) := by
  obtain ⟨u,rfl⟩ := (O D a s).mkQ_surjective x
  obtain ⟨z,hz,t,ht,he⟩ := Submodule.mem_sup.mp
    (zhu_three_spanning D a ha s hs u.property)
  let zS : vacuumDescendants D a s := ⟨z,zhuO_le D a ha s hs hz⟩
  let tS : vacuumDescendants D a s := ⟨t,small_le D a ha s hs ht⟩
  have equal : zS+tS=u := Subtype.ext he
  obtain ⟨c0,c1,c2,hc⟩ := small_three_scalars D a s t ht
  have tEq : tS=c0 • rep D a ha s hs 0+c1 • rep D a ha s hs 1+
      c2 • rep D a ha s hs 2 := Subtype.ext hc
  refine ⟨c0,c1,c2,?_⟩
  rw [← equal,map_add,show (O D a s).mkQ zS=0 from
    (Submodule.Quotient.mk_eq_zero (O D a s)).mpr hz,zero_add,tEq]
  simp only [map_add,map_smul]

private theorem quotient_action_comm (D : LatticeData) (hd : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1)
    (x y : Q D a s) :
    quotientAction D hd a ha s hs x * quotientAction D hd a ha s hs y=
      quotientAction D hd a ha s hs y * quotientAction D hd a ha s hs x := by
  obtain ⟨c0,c1,c2,hx⟩ := quotient_three_scalars D a ha s hs x
  obtain ⟨d0,d1,d2,hy⟩ := quotient_three_scalars D a ha s hs y
  obtain ⟨r0,r1,r2⟩ := rep_eq D a ha s hs
  rw [hx,hy]
  simp only [map_add,map_smul]
  change (c0 • topAction D hd a ha s hs (rep D a ha s hs 0)+
      c1 • topAction D hd a ha s hs (rep D a ha s hs 1)+
      c2 • topAction D hd a ha s hs (rep D a ha s hs 2)) *
    (d0 • topAction D hd a ha s hs (rep D a ha s hs 0)+
      d1 • topAction D hd a ha s hs (rep D a ha s hs 1)+
      d2 • topAction D hd a ha s hs (rep D a ha s hs 2)) =
    (d0 • topAction D hd a ha s hs (rep D a ha s hs 0)+
      d1 • topAction D hd a ha s hs (rep D a ha s hs 1)+
      d2 • topAction D hd a ha s hs (rep D a ha s hs 2)) *
    (c0 • topAction D hd a ha s hs (rep D a ha s hs 0)+
      c1 • topAction D hd a ha s hs (rep D a ha s hs 1)+
      c2 • topAction D hd a ha s hs (rep D a ha s hs 2))
  simp only [r0,r1,r2,topAction_vacuum,topAction_axis,topAction_axisSquare]
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,one_mul,mul_one,
    mul_assoc]
  module

/-- A commutative ring on the original additive quotient, with the
actual descended star product and the actual vacuum class as unit. -/
@[instance_reducible]
def quotientRing (D : LatticeData) (hd : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    CommRing (Q D a s) where
  __ := (inferInstance : AddCommGroup (Q D a s))
  mul := fun x y => quotientProduct D hd a ha s hs x y
  one := (O D a s).mkQ (vacuumState D a s)
  mul_assoc x y z := quotientAction_injective D hd a ha s hs (by
    change quotientAction D hd a ha s hs
        (quotientProduct D hd a ha s hs
          (quotientProduct D hd a ha s hs x y) z) =
      quotientAction D hd a ha s hs
        (quotientProduct D hd a ha s hs x
          (quotientProduct D hd a ha s hs y z))
    simp only [quotient_action_product]
    exact mul_assoc _ _ _)
  one_mul x := by
    obtain ⟨u,rfl⟩ := (O D a s).mkQ_surjective x
    change (O D a s).mkQ (star D a ha s hs (vacuumState D a s) u)=_
    rw [star_vacuum_left]
  mul_one x := by
    obtain ⟨u,rfl⟩ := (O D a s).mkQ_surjective x
    change (O D a s).mkQ (star D a ha s hs u (vacuumState D a s))=_
    rw [star_vacuum_right]
  mul_comm x y := quotientAction_injective D hd a ha s hs (by
    change quotientAction D hd a ha s hs
        (quotientProduct D hd a ha s hs x y) =
      quotientAction D hd a ha s hs
        (quotientProduct D hd a ha s hs y x)
    rw [quotient_action_product, quotient_action_product]
    exact quotient_action_comm D hd a ha s hs x y)
  left_distrib x y z := (quotientProduct D hd a ha s hs x).map_add y z
  right_distrib x y z := congrArg (fun f : Q D a s →ₗ[ℂ] Q D a s => f z)
    ((quotientProduct D hd a ha s hs).map_add x y)
  zero_mul x := congrArg (fun f : Q D a s →ₗ[ℂ] Q D a s => f x)
    (map_zero (quotientProduct D hd a ha s hs))
  mul_zero x := map_zero (quotientProduct D hd a ha s hs x)

/-- The original complex scalar action is compatible with the actual
quotient ring; complex constants act by multiples of the vacuum class. -/
@[instance_reducible]
def quotientAlgebra (D : LatticeData) (hd : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    letI := quotientRing D hd a ha s hs
    Algebra ℂ (Q D a s) := by
  letI := quotientRing D hd a ha s hs
  apply Algebra.ofModule
  · intro c x y
    exact congrArg (fun f : Q D a s →ₗ[ℂ] Q D a s => f y)
      ((quotientProduct D hd a ha s hs).map_smul c x)
  · intro c x y
    exact (quotientProduct D hd a ha s hs x).map_smul c y

private def quotientRepresentation (D : LatticeData) (hd : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    letI := quotientRing D hd a ha s hs
    letI := quotientAlgebra D hd a ha s hs
    Q D a s →ₐ[ℂ] Module.End ℂ (actualGrade D hd 1) := by
  letI := quotientRing D hd a ha s hs
  letI := quotientAlgebra D hd a ha s hs
  exact AlgHom.ofLinearMap (quotientAction D hd a ha s hs)
    (topAction_vacuum D hd a ha s hs) (quotient_action_product D hd a ha s hs)

/-- The actual star algebra has dimension three and satisfies the monic
axis relation. Representative multiplication uses the actual star. -/
theorem actual_zhu_algebra (D : LatticeData) (hd : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    letI := quotientRing D hd a ha s hs
    letI := quotientAlgebra D hd a ha s hs
    let q := (O D a s).mkQ
    let x := q (axisState D a ha s hs)
    (∀ u v, q (star D a ha s hs u v)=q u*q v) ∧
    FiniteDimensional ℂ (Q D a s) ∧ Module.finrank ℂ (Q D a s)=3 ∧
    x*(x-algebraMap ℂ (Q D a s) (1/16))*(x-algebraMap ℂ (Q D a s) (1/2))=0 := by
  classical
  letI := quotientRing D hd a ha s hs
  letI := quotientAlgebra D hd a ha s hs
  obtain ⟨_,finite,bound⟩ := actual_zhu_quotient_finite D a ha s hs
  letI : FiniteDimensional ℂ (Q D a s) := finite
  have independent : LinearIndependent ℂ
      (fun i : Fin 3 => (O D a s).mkQ (rep D a ha s hs i)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have image := congrArg (quotientAction D hd a ha s hs) hc
    simp only [map_sum,map_add,map_smul,map_zero,Fin.sum_univ_three] at image
    have image' : c 0 • topAction D hd a ha s hs (rep D a ha s hs 0)+
        c 1 • topAction D hd a ha s hs (rep D a ha s hs 1)+
        c 2 • topAction D hd a ha s hs (rep D a ha s hs 2)=0 := by
      change c 0 • topAction D hd a ha s hs (rep D a ha s hs 0)+
          c 1 • topAction D hd a ha s hs (rep D a ha s hs 1)+
          c 2 • topAction D hd a ha s hs (rep D a ha s hs 2)=0 at image
      exact image
    obtain ⟨r0,r1,r2⟩ := rep_eq D a ha s hs
    rw [r0,r1,r2,topAction_vacuum,topAction_axis,topAction_axisSquare] at image'
    obtain ⟨_,h0,h16,hh⟩ := actual_top_three_eigenspaces_positive D hd a ha s hs
    obtain ⟨hc0,hc1,hc2⟩ := actual_three_images_independent D hd a ha s
      h0 h16 hh (c 0) (c 1) (c 2) image'
    fin_cases i <;> assumption
  have lower : 3≤Module.finrank ℂ (Q D a s) := by
    simpa using independent.fintype_card_le_finrank
  refine ⟨fun _ _ => rfl,finite,Nat.le_antisymm bound lower,?_⟩
  apply quotientAction_injective D hd a ha s hs
  change quotientAction D hd a ha s hs
      (quotientProduct D hd a ha s hs
        (quotientProduct D hd a ha s hs
          ((O D a s).mkQ (axisState D a ha s hs))
          ((O D a s).mkQ (axisState D a ha s hs) -
            algebraMap ℂ (Q D a s) (1/16)))
        ((O D a s).mkQ (axisState D a ha s hs) -
          algebraMap ℂ (Q D a s) (1/2))) =
    quotientAction D hd a ha s hs 0
  rw [quotient_action_product, quotient_action_product, map_zero]
  have scalar (c : ℂ) :
      quotientAction D hd a ha s hs (algebraMap ℂ (Q D a s) c) =
        c • (1 : Module.End ℂ (actualGrade D hd 1)) := by
    rw [Algebra.algebraMap_eq_smul_one]
    rw [map_smul]
    congr 1
    change topAction D hd a ha s hs (vacuumState D a s)=1
    exact topAction_vacuum D hd a ha s hs
  rw [map_sub, map_sub, scalar, scalar]
  change topAction D hd a ha s hs (axisState D a ha s hs) *
      (topAction D hd a ha s hs (axisState D a ha s hs) - (1/16:ℂ) • 1) *
      (topAction D hd a ha s hs (axisState D a ha s hs) - (1/2:ℂ) • 1)=0
  rw [topAction_axis]
  exact actualGradeOneZeroMode_polynomial D hd a ha s hs

/-- The monic polynomial with roots zero, one sixteenth and one half. -/
def zhuPolynomial : Polynomial ℂ :=
  Polynomial.X*(Polynomial.X-Polynomial.C (1/16))*(Polynomial.X-Polynomial.C (1/2))

/-- An actual complex algebra equivalence from the monic cubic algebra to
the literal Zhu quotient, carrying its root to the actual axis class.
The explicit integral cubic is the same relation with denominators cleared. -/
theorem actual_zhu_presentation (D : LatticeData) (hd : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a=4) (s : ℂ) (hs : s ^ 2 = 1) :
    letI := quotientRing D hd a ha s hs
    letI := quotientAlgebra D hd a ha s hs
    let x := (O D a s).mkQ (axisState D a ha s hs)
    zhuPolynomial.Monic ∧
    (∃ E : AdjoinRoot zhuPolynomial ≃ₐ[ℂ] Q D a s,
      E (AdjoinRoot.root zhuPolynomial)=x) ∧
    (64:ℂ) • x^3-(36:ℂ) • x^2+(2:ℂ) • x=0 := by
  classical
  letI := quotientRing D hd a ha s hs
  letI := quotientAlgebra D hd a ha s hs
  let q := (O D a s).mkQ
  let x : Q D a s := q (axisState D a ha s hs)
  obtain ⟨compatibility,finite,dimension,cubic⟩ := actual_zhu_algebra D hd a ha s hs
  letI : FiniteDimensional ℂ (Q D a s) := finite
  have monic : zhuPolynomial.Monic :=
    (Polynomial.monic_X.mul (Polynomial.monic_X_sub_C _)).mul
      (Polynomial.monic_X_sub_C _)
  let F : AdjoinRoot zhuPolynomial →ₐ[ℂ] Q D a s :=
    AdjoinRoot.liftAlgHom zhuPolynomial (Algebra.ofId ℂ (Q D a s)) x
      (by simpa [zhuPolynomial, x, q] using cubic)
  have root_image : F (AdjoinRoot.root zhuPolynomial)=x := by simp [F]
  let R := F.toLinearMap.range
  have axis_square : q (axisSquare D a ha s hs)=x^2+(2:ℂ) • x := by
    have circle_zero : q (weightedProduct D a ha s hs 2 (-2)
        (axisState D a ha s hs) (vacuumState D a s))=0 := by
      apply quotientAction_injective D hd a ha s hs
      rw [map_zero]
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact actual_circle_all_right_states D hd a ha s hs 2
        (axisState D a ha s hs) (vacuumState D a s)
        (axisState_grade_two D a ha s hs) v.val v.property
    rw [axis_circle_vacuum,map_add,map_smul] at circle_zero
    have derivative : q (axisDerivative D a ha s hs)=-(2:ℂ) • x := by
      simpa [x] using eq_neg_of_add_eq_zero_left circle_zero
    have product := compatibility (axisState D a ha s hs) (axisState D a ha s hs)
    rw [axis_star_square,map_add,map_add,map_smul,map_smul,derivative] at product
    change q (axisSquare D a ha s hs)+(2:ℂ) • (-(2:ℂ) • x)+
      (2:ℂ) • x=x*x at product
    rw [pow_two]
    linear_combination (norm := module) product
  have one_range : (1 : Q D a s) ∈ R := LinearMap.mem_range.mpr ⟨1,map_one F⟩
  have axis_range : x ∈ R := by
    apply LinearMap.mem_range.mpr
    refine ⟨AdjoinRoot.root zhuPolynomial, ?_⟩
    change F (AdjoinRoot.root zhuPolynomial) = x
    exact root_image
  have square_range : x^2+(2:ℂ) • x ∈ R := by
    exact R.add_mem (LinearMap.mem_range.mpr ⟨(AdjoinRoot.root zhuPolynomial)^2,by
      change F ((AdjoinRoot.root zhuPolynomial)^2) = x^2
      rw [map_pow,root_image]⟩) (R.smul_mem _ axis_range)
  have surjective : Function.Surjective F := by
    intro y
    obtain ⟨c0,c1,c2,hy⟩ := quotient_three_scalars D a ha s hs y
    change y ∈ R
    rw [hy]
    obtain ⟨r0,r1,r2⟩ := rep_eq D a ha s hs
    rw [r0,r1,r2,axis_square]
    exact R.add_mem (R.add_mem (R.smul_mem _ one_range) (R.smul_mem _ axis_range))
      (R.smul_mem _ square_range)
  letI : FiniteDimensional ℂ (AdjoinRoot zhuPolynomial) := monic.finite_adjoinRoot
  have domain_dimension : Module.finrank ℂ (AdjoinRoot zhuPolynomial)=3 := by
    change Module.finrank ℂ (Polynomial ℂ ⧸ Ideal.span {zhuPolynomial})=3
    rw [finrank_quotient_span_eq_natDegree]
    simp only [zhuPolynomial]
    rw [Polynomial.natDegree_mul
      (mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero _))
      (Polynomial.X_sub_C_ne_zero _),
      Polynomial.natDegree_mul Polynomial.X_ne_zero
        (Polynomial.X_sub_C_ne_zero _)]
    simp only [Polynomial.natDegree_X, Polynomial.natDegree_sub_C]
  have injective : Function.Injective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := F.toLinearMap) (domain_dimension.trans dimension.symm)).mpr surjective
  refine ⟨monic,⟨AlgEquiv.ofBijective F ⟨injective,surjective⟩,root_image⟩,?_⟩
  have expanded : x*(x-algebraMap ℂ (Q D a s) (1/16))*
      (x-algebraMap ℂ (Q D a s) (1/2))=
      x^3-(9/16:ℂ) • x^2+(1/32:ℂ) • x := by
    simp only [Algebra.algebraMap_eq_smul_one]
    simp only [mul_sub,sub_mul,smul_mul_assoc,mul_smul_comm,smul_smul,
      mul_one,one_mul,pow_succ,pow_zero,mul_assoc]
    module
  rw [expanded] at cubic
  have cleared := congrArg (fun z : Q D a s => (64:ℂ) • z) cubic
  simpa only [smul_add,smul_sub,smul_smul,smul_zero,
    show (64:ℂ)*(9/16)=36 by norm_num,
    show (64:ℂ)*(1/32)=2 by norm_num,one_smul] using cleared

end D5.S3.VertexAlgebra.Lattice.NormFourZhuAlgebra
