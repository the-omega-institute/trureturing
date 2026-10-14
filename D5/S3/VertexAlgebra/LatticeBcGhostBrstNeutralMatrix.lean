/- GID: D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original neutral BRST matrix is evaluated on the vacuum and one-oscillator probes.
-/

import D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction
import D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass
import D5.S3.VertexAlgebra.LatticeSugawaraConformal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge LatticeBcGhostBrstCAction
  LatticeBcGhostBrstVacuumClass BcGhostFockSupport BcGhostStressCurrent
  LatticeFiniteNegativeGeneration
open LatticeSugawaraVirasoro
open scoped BigOperators TensorProduct

noncomputable section

def neutralMatter (D : LatticeData) (t : Fin D.rank) : Carrier D :=
  Finsupp.single (0 : Charge D) (MvPolynomial.X (t, 0) : Oscillator D)

inductive Probe (D : LatticeData) where
  | vacuum
  | c0Vacuum
  | oneOscillator (t : Fin D.rank)
  | c0OneOscillator (t : Fin D.rank)
  | z
  | w

def vacuumState (D : LatticeData) : State D :=
  vacuumVector D

def uState (D : LatticeData) : State D :=
  C D 0 (vacuumState D)

def jState (D : LatticeData) (t : Fin D.rank) : State D :=
  neutralMatter D t ⊗ₜ[ℂ] c (K := ℂ) 1 (vacuum : Fock ℂ)

def kState (D : LatticeData) (t : Fin D.rank) : State D :=
  C D 0 (jState D t)

def zState (D : LatticeData) : State D :=
  C D (-1) (C D 1 (vacuumState D))

def wState (D : LatticeData) : State D :=
  C D (-1) (C D 0 (C D 1 (vacuumState D)))

def probeState (D : LatticeData) : Probe D → State D
  | .vacuum => vacuumState D
  | .c0Vacuum => uState D
  | .oneOscillator t => jState D t
  | .c0OneOscillator t => kState D t
  | .z => zState D
  | .w => wState D

def neutralCoefficient (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (s t : Fin D.rank) : ℂ :=
  (2 : ℂ)⁻¹ * ∑ r : Fin D.rank,
    (H s r + H r s) * gramComplex D r t

def kronecker (D : LatticeData) (s t : Fin D.rank) : ℂ :=
  if s = t then 1 else 0

def formulaState (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Probe D → State D
  | .vacuum => 0
  | .c0Vacuum => (-2 : ℂ) • zState D
  | .oneOscillator t =>
      ∑ s : Fin D.rank,
        (neutralCoefficient D H s t - kronecker D s t) • kState D s
  | .c0OneOscillator _ => 0
  | .z => 0
  | .w => 0

def inverseFormulaState (D : LatticeData) : Probe D → State D
  | .vacuum => 0
  | .c0Vacuum => (-2 : ℂ) • zState D
  | .oneOscillator _ => 0
  | .c0OneOscillator _ => 0
  | .z => 0
  | .w => 0

private theorem neutralMatter_frequency (D : LatticeData) (t : Fin D.rank) :
    vectorFrequencyBound D (neutralMatter D t) = 1 := by
  simp [neutralMatter, vectorFrequencyBound, polynomialFrequencyBound, MvPolynomial.X]

private theorem neutralMode_one_neutralMatter (D : LatticeData) (i t : Fin D.rank) :
    neutralMode D i 1 (neutralMatter D t) =
      (D.G i t : ℂ) • Finsupp.single (0 : Charge D) (1 : Oscillator D) := by
  rw [neutralMatter, neutralMode_single]
  have hpos : neutralPolynomialMode D i 0 1 =
      (1 : ℂ) • weightedPartial D i 0 := by
    simpa using (neutralPolynomialMode_positive D i 0 0)
  rw [hpos]
  simp only [weightedPartial, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply, Prod.mk.injEq]
  simp

private theorem neutralMode_zero_neutralMatter (D : LatticeData) (i t : Fin D.rank) :
    neutralMode D i 0 (neutralMatter D t) = 0 := by
  rw [neutralMatter, neutralMode_single]
  simp [neutralPolynomialMode, bilinear, unitCharge]

private theorem neutralMode_nonnegative_ground (D : LatticeData) (i : Fin D.rank)
    (m : ℤ) (hm : 0 ≤ m) :
    neutralMode D i m (Finsupp.single (0 : Charge D) (1 : Oscillator D)) = 0 := by
  by_cases hm0 : m = 0
  · subst m
    simp [neutralMode, neutralPolynomialMode, bilinear, unitCharge]
  · apply neutralMode_vanish
    rw [LatticeSugawaraVirasoro.ground_frequency_bound]
    omega

private theorem sugawaraMode_zero_neutralMatter (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (t : Fin D.rank) :
    sugawaraMode D H 0 (neutralMatter D t) =
      ∑ s : Fin D.rank, neutralCoefficient D H s t • neutralMatter D s := by
  classical
  rw [sugawaraMode_interval_sum, neutralMatter_frequency]
  have hinterval : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by decide
  rw [show min 0 ((0 : ℤ) - (↑(1 : ℕ) : ℤ)) = -1 by norm_num,
    show (↑(1 : ℕ) : ℤ) = 1 by norm_num, hinterval]
  have hminus (i : Fin D.rank) (p : Oscillator D) :
      neutralPolynomialMode D i 0 (-1) p = MvPolynomial.X (i, 0) * p := by
    simp [neutralPolynomialMode]
  have hnegSingle (i j : Fin D.rank) :
      neutralMode D i (-1)
          (Finsupp.single (0 : Charge D) ((D.G j t : ℂ) • (1 : Oscillator D))) =
        Finsupp.single (0 : Charge D) ((D.G j t : ℂ) • MvPolynomial.X (i, 0)) := by
    rw [neutralMode_single, hminus i]
    congr 1
    simp [mul_smul_comm]
  have hsum (f : ℤ → Carrier D) :
      (∑ k ∈ ({-1, 0, 1} : Finset ℤ), f k) = f (-1) + f 0 + f 1 := by
    simp [Finset.sum_insert, add_assoc]
  simp_rw [hsum]
  · simp only [normalSummand, show (-1 : ℤ) < 0 by omega, if_true,
      show ¬(0 : ℤ) < 0 by omega, if_false, Module.End.mul_apply,
      show ¬(1 : ℤ) < 0 by omega, if_false,
      show (0 - (-1 : ℤ) : ℤ) = 1 by norm_num,
      show (0 - (1 : ℤ) : ℤ) = -1 by norm_num,
      neutralMode_zero_neutralMatter,
      neutralMode_one_neutralMatter, map_zero, map_smul, smul_zero, zero_add,
      add_zero, Finsupp.single_zero, Finsupp.smul_single]
    have hquad :
        (∑ i : Fin D.rank, ∑ j : Fin D.rank,
          H i j •
            ((neutralMode D i (-1))
                (Finsupp.single (0 : Charge D) ((D.G j t : ℂ) • (1 : Oscillator D))) +
              (neutralMode D j (-1))
                (Finsupp.single (0 : Charge D) ((D.G i t : ℂ) • (1 : Oscillator D))))) =
        (∑ i : Fin D.rank, ∑ j : Fin D.rank,
          H i j •
            (Finsupp.single (0 : Charge D) ((D.G j t : ℂ) • MvPolynomial.X (i, 0)) +
              Finsupp.single (0 : Charge D) ((D.G i t : ℂ) • MvPolynomial.X (j, 0)))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hnegSingle i j, hnegSingle j i]
    rw [hquad]
    apply Finsupp.ext
    intro β
    by_cases hβ : β = 0
    · subst β
      simp [Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
        Finsupp.add_apply, neutralMatter]
      have hmatrix :
          (∑ i : Fin D.rank, ∑ j : Fin D.rank,
              H i j • ((D.G j t : ℂ) • (MvPolynomial.X (i, 0) : Oscillator D))) +
            ∑ i : Fin D.rank, ∑ j : Fin D.rank,
              H i j • ((D.G i t : ℂ) • (MvPolynomial.X (j, 0) : Oscillator D)) =
          ∑ i : Fin D.rank, ∑ j : Fin D.rank,
            (H i j + H j i) • ((D.G j t : ℂ) • (MvPolynomial.X (i, 0) : Oscillator D)) := by
        have hswap :
            (∑ i : Fin D.rank, ∑ j : Fin D.rank,
                H i j • ((D.G i t : ℂ) • (MvPolynomial.X (j, 0) : Oscillator D))) =
              ∑ i : Fin D.rank, ∑ j : Fin D.rank,
                H j i • ((D.G j t : ℂ) • (MvPolynomial.X (i, 0) : Oscillator D)) :=
          Finset.sum_comm
        rw [hswap, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← add_smul]
      have hsplit :
          (∑ i : Fin D.rank, ∑ j : Fin D.rank,
              (H i j • ((D.G j t : ℂ) • (MvPolynomial.X (i, 0) : Oscillator D)) +
                H i j • ((D.G i t : ℂ) • (MvPolynomial.X (j, 0) : Oscillator D)))) =
            (∑ i : Fin D.rank, ∑ j : Fin D.rank,
                H i j • ((D.G j t : ℂ) • (MvPolynomial.X (i, 0) : Oscillator D))) +
              ∑ i : Fin D.rank, ∑ j : Fin D.rank,
                H i j • ((D.G i t : ℂ) • (MvPolynomial.X (j, 0) : Oscillator D)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_add_distrib]
      rw [hsplit, hmatrix, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.smul_sum]
      simp only [smul_smul]
      rw [← Finset.sum_smul]
      rw [neutralCoefficient]
      simp only [gramComplex, Matrix.map_apply]
      congr 1
      rw [Finset.mul_sum]
    · simp [neutralMatter, Finsupp.single_apply, hβ, Ne.symm hβ]

private theorem sugawaraMode_positive_neutralMatter (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (t : Fin D.rank)
    (m : ℤ) (hm : 1 ≤ m) :
    sugawaraMode D H m (neutralMatter D t) = 0 := by
  classical
  rw [sugawaraMode_interval_sum, neutralMatter_frequency]
  rw [show min 0 (m - (↑(1 : ℕ) : ℤ)) = 0 by omega]
  have hinterval : Finset.Icc (0 : ℤ) (↑(1 : ℕ) : ℤ) = {0, 1} := by decide
  rw [hinterval]
  have hsum (f : ℤ → Carrier D) :
      (∑ k ∈ ({0, 1} : Finset ℤ), f k) = f 0 + f 1 := by
    simp [Finset.sum_insert]
  simp_rw [hsum]
  have hterm (i j : Fin D.rank) :
      normalSummand D i j 0 (m - 0) (neutralMatter D t) +
          normalSummand D i j 1 (m - 1) (neutralMatter D t) = 0 := by
    have hfirst :
        normalSummand D i j 0 (m - 0) (neutralMatter D t) = 0 := by
      rw [normalSummand, if_neg (by omega), Module.End.mul_apply,
        neutralMode_zero_neutralMatter]
      simp
    rw [hfirst, zero_add]
    rw [normalSummand, if_neg (by omega), Module.End.mul_apply,
      neutralMode_one_neutralMatter, map_smul,
      neutralMode_nonnegative_ground D j (m - 1) (by omega)]
    simp
  simp_rw [hterm, smul_zero, Finset.sum_const_zero]
  simp

private theorem c_one_vacuum :
    c (K := ℂ) 1 (vacuum : Fock ℂ) = Finsupp.single ({1} : Finset ℕ) 1 := by
  simp [c, create, vacuum, Finsupp.linearCombination_single, createBasis, sign]

private theorem c_zero_vacuum :
    c (K := ℂ) 0 (vacuum : Fock ℂ) = Finsupp.single ({3} : Finset ℕ) 1 := by
  simp [c, create, vacuum, Finsupp.linearCombination_single, createBasis, sign]

private theorem c_minus_one_vacuum :
    c (K := ℂ) (-1) (vacuum : Fock ℂ) = Finsupp.single ({5} : Finset ℕ) 1 := by
  simp [c, create, vacuum, Finsupp.linearCombination_single, createBasis, sign]

private theorem c_zero_c_one_vacuum :
    c (K := ℂ) 0 (c 1 (vacuum : Fock ℂ)) =
      -Finsupp.single ({1, 3} : Finset ℕ) 1 := by
  rw [c_one_vacuum]
  have hset : insert 3 ({1} : Finset ℕ) = {1, 3} := by decide
  have hcard : ({s ∈ ({1} : Finset ℕ) | s < 3}.card) = 1 := by decide
  simp [c, create, Finsupp.linearCombination_single, createBasis, sign, hset, hcard]

private theorem c_minus_one_c_one_vacuum :
    c (K := ℂ) (-1) (c 1 (vacuum : Fock ℂ)) =
      -Finsupp.single ({1, 5} : Finset ℕ) 1 := by
  rw [c_one_vacuum]
  have hset : insert 5 ({1} : Finset ℕ) = {1, 5} := by decide
  have hcard : ({s ∈ ({1} : Finset ℕ) | s < 5}.card) = 1 := by decide
  simp [c, create, Finsupp.linearCombination_single, createBasis, sign, hset, hcard]

private theorem c_minus_one_c_zero_c_one_vacuum :
    c (K := ℂ) (-1) (c 0 (c 1 (vacuum : Fock ℂ))) =
      -Finsupp.single ({1, 3, 5} : Finset ℕ) 1 := by
  rw [c_zero_c_one_vacuum]
  have hset : insert 5 ({1, 3} : Finset ℕ) = {1, 3, 5} := by decide
  have hcard : ({s ∈ ({1, 3} : Finset ℕ) | s < 5}.card) = 2 := by decide
  simp [c, create, Finsupp.linearCombination_single, createBasis, sign, hset, hcard]

private theorem c_one_c_minus_one_vacuum :
    c (K := ℂ) 1 (c (-1) (vacuum : Fock ℂ)) =
      Finsupp.single ({1, 5} : Finset ℕ) 1 := by
  rw [c_minus_one_vacuum]
  have hset : insert 1 ({5} : Finset ℕ) = {1, 5} := by decide
  have hcard : ({s ∈ ({5} : Finset ℕ) | s = 0}.card) = 0 := by decide
  simp [c, create, Finsupp.linearCombination_single, createBasis, sign, hset, hcard]

private theorem c_minus_one_c_one_vacuum_eq_z :
    c (K := ℂ) (-1) (c 1 (vacuum : Fock ℂ)) =
      -Finsupp.single ({1, 5} : Finset ℕ) 1 := c_minus_one_c_one_vacuum

private theorem c_one_c_zero_vacuum :
    c (K := ℂ) 1 (c 0 (vacuum : Fock ℂ)) =
      Finsupp.single ({1, 3} : Finset ℕ) 1 := by
  rw [c_zero_vacuum]
  have hset : insert 1 ({3} : Finset ℕ) = {1, 3} := by decide
  have hcard : ({s ∈ ({3} : Finset ℕ) | s = 0}.card) = 0 := by decide
  simp [c, create, Finsupp.linearCombination_single, createBasis, sign, hset, hcard]

private theorem c_zero_vacuum_c_zero :
    c (K := ℂ) 0 (c 0 (c 1 (vacuum : Fock ℂ))) = 0 := by
  rw [c_zero_c_one_vacuum]
  simp [c, create, Finsupp.linearCombination_single, createBasis, sign]

private theorem c_positive_vacuum_zero (n : ℤ) (hn : 2 ≤ n) :
    c (K := ℂ) n (vacuum : Fock ℂ) = 0 := by
  rw [c, if_neg (by omega)]
  apply annihilate_eq_zero
  simp [occupied, vacuum]

private theorem c_c_vacuum_negative_zero (n : ℤ) (hn : n ≤ -2) :
    c (K := ℂ) (-n) (c n (vacuum : Fock ℂ)) = 0 := by
  have hzero : c (K := ℂ) (-n) (vacuum : Fock ℂ) = 0 :=
    c_positive_vacuum_zero (-n) (by omega)
  have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (vacuum : Fock ℂ))
    (c_c (K := ℂ) (-n) n)
  simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
    hzero, map_zero, add_zero]
    using h

private theorem V_zero_vacuum_support (D : LatticeData) :
    Function.support (fun n : ℤ =>
      (2 * n : ℂ) • ((C D (-n) * C D n) (vacuumState D))) ⊆
        Set.Icc (-1 : ℤ) 1 := by
  intro n hn
  constructor
  · by_contra hlow
    have hzero : (C D (-n) * C D n) (vacuumState D) = 0 := by
      simp only [LatticeBcGhostBrstCharge.C, Module.End.mul_apply, vacuumState,
        vacuumVector, TensorProduct.map_tmul, LinearMap.id_apply]
      rw [c_c_vacuum_negative_zero n (by omega)]
      simp
    exact hn (by simp [hzero])
  · by_contra hhigh
    have hzero : (C D (-n) * C D n) (vacuumState D) = 0 := by
      have hc := c_positive_vacuum_zero n (by omega)
      simp only [LatticeBcGhostBrstCharge.C, Module.End.mul_apply, vacuumState,
        vacuumVector, TensorProduct.map_tmul, LinearMap.id_apply]
      rw [hc]
      simp
    exact hn (by simp [hzero])

private theorem V_zero_vacuum (D : LatticeData) :
    V D 0 (vacuumState D) = (4 : ℂ) • zState D := by
  simp only [V, LinearMap.coe_mk, AddHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-1 : ℤ) 1)
    (by simpa [Finset.coe_Icc, add_zero] using V_zero_vacuum_support D)]
  have hsum (f : ℤ → State D) :
      (∑ n ∈ Finset.Icc (-1 : ℤ) 1, f n) = f (-1) + f 0 + f 1 := by
    have hinterval : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by decide
    rw [hinterval]
    simp [Finset.sum_insert, add_assoc]
  rw [zState]
  rw [hsum]
  simp only [LatticeBcGhostBrstCharge.C, Module.End.mul_apply, vacuumState, vacuumVector,
    TensorProduct.map_tmul, LinearMap.id_apply]
  norm_num
  simp only [c_one_c_minus_one_vacuum, c_minus_one_c_one_vacuum_eq_z]
  simp only [TensorProduct.tmul_neg, smul_neg]
  module

private theorem c_one_c_one_vacuum_early :
    c (K := ℂ) 1 (c 1 (vacuum : Fock ℂ)) = 0 := by
  rw [c_one_vacuum]
  simp [c, create, Finsupp.linearCombination_single, createBasis, sign]

private theorem c_positive_c_one_vacuum_early (n : ℤ) (hn : 2 ≤ n) :
    c (K := ℂ) n (c 1 (vacuum : Fock ℂ)) = 0 := by
  rw [c_one_vacuum, c, if_neg (by omega)]
  apply annihilate_eq_zero
  simp [occupied]

private theorem c_negative_c_one_vacuum_early (n : ℤ) (hn : n ≤ -2) :
    c (K := ℂ) (-n) (c n (c 1 (vacuum : Fock ℂ))) = 0 := by
  have hzero : c (K := ℂ) (-n) (c 1 (vacuum : Fock ℂ)) = 0 :=
    c_positive_c_one_vacuum_early (-n) (by omega)
  have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (c 1 (vacuum : Fock ℂ)))
    (c_c (K := ℂ) (-n) n)
  simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
    hzero, map_zero, add_zero] using h

private theorem c_one_c_minus_one_c_one_vacuum_early :
    c (K := ℂ) 1 (c (-1) (c 1 (vacuum : Fock ℂ))) = 0 := by
  have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (c 1 (vacuum : Fock ℂ)))
    (c_c (K := ℂ) 1 (-1))
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  rw [c_one_c_one_vacuum_early] at h
  simpa only [map_zero, LinearMap.zero_apply, add_zero] using h

private theorem c_positive_c_one_vacuum_at_least_one (n : ℤ) (hn : 1 ≤ n) :
    c (K := ℂ) n (c 1 (vacuum : Fock ℂ)) = 0 := by
  by_cases h : n = 1
  · subst n
    exact c_one_c_one_vacuum_early
  · exact c_positive_c_one_vacuum_early n (by omega)

private theorem c_positive_c_zero_c_one_vacuum (n : ℤ) (hn : 1 ≤ n) :
    c (K := ℂ) n (c 0 (c 1 (vacuum : Fock ℂ))) = 0 := by
  have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (c 1 (vacuum : Fock ℂ)))
    (c_c (K := ℂ) n 0)
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  rw [c_positive_c_one_vacuum_at_least_one n hn] at h
  simpa only [map_zero, LinearMap.zero_apply, add_zero] using h

private theorem c_negative_c_zero_c_one_vacuum (n : ℤ) (hn : n ≤ -1) :
    c (K := ℂ) (-n) (c (n - 1) (c 0 (c 1 (vacuum : Fock ℂ)))) = 0 := by
  have houter := c_positive_c_zero_c_one_vacuum (-n) (by omega)
  have h := congrArg
    (fun T : Module.End ℂ (Fock ℂ) => T (c 0 (c 1 (vacuum : Fock ℂ))))
    (c_c (K := ℂ) (-n) (n - 1))
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  rw [houter] at h
  simpa only [map_zero, LinearMap.zero_apply, add_zero] using h

private theorem c_positive_c_shift_vacuum (n : ℤ) (hn : n ≤ -2) :
    c (K := ℂ) (-n) (c (n + 1) (vacuum : Fock ℂ)) = 0 := by
  have houter := c_positive_vacuum_zero (-n) (by omega)
  have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (vacuum : Fock ℂ))
    (c_c (K := ℂ) (-n) (n + 1))
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  rw [houter] at h
  simpa only [map_zero, LinearMap.zero_apply, add_zero] using h

private theorem V_one_vacuum (D : LatticeData) :
    V D 1 (vacuumState D) = (-2 : ℂ) • C D 1 (C D 0 (vacuumState D)) := by
  simp only [V, LinearMap.coe_mk, AddHom.coe_mk]
  have hsupport : Function.support (fun n : ℤ =>
      (2 * n + 1 : ℂ) • ((C D (-n) * C D (n + 1)) (vacuumState D))) ⊆
        Set.Icc (-1 : ℤ) 0 := by
    intro n hn
    constructor
    · by_contra hlow
      have hzero : (C D (-n) * C D (n + 1)) (vacuumState D) = 0 := by
        simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
          TensorProduct.map_tmul, LinearMap.id_apply]
        by_cases hinner : 0 < n
        · rw [c_positive_vacuum_zero (n + 1) (by omega)]
          simp
        · rw [c_positive_c_shift_vacuum n (by omega)]
          simp
      exact hn (by simp [hzero])
    · by_contra hhigh
      have hzero : (C D (-n) * C D (n + 1)) (vacuumState D) = 0 := by
        simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
          TensorProduct.map_tmul, LinearMap.id_apply]
        rw [c_positive_vacuum_zero (n + 1) (by omega)]
        simp
      exact hn (by simp [hzero])
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-1 : ℤ) 0)
    (by simpa [Finset.coe_Icc] using hsupport)]
  have hsum (f : ℤ → State D) :
      (∑ n ∈ Finset.Icc (-1 : ℤ) 0, f n) = f (-1) + f 0 := by
    have hinterval : Finset.Icc (-1 : ℤ) 0 = {-1, 0} := by decide
    rw [hinterval]
    simp [Finset.sum_insert]
  rw [hsum]
  simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
    TensorProduct.map_tmul, LinearMap.id_apply]
  norm_num
  rw [c_one_c_zero_vacuum, c_zero_c_one_vacuum]
  simp only [TensorProduct.tmul_neg, smul_neg]
  module

private theorem V_zero_c_one_vacuum (D : LatticeData) :
    V D 0 (C D 1 (vacuumState D)) = 0 := by
  simp only [V, LinearMap.coe_mk, AddHom.coe_mk]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hlow : n ≤ -2
  · simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
      TensorProduct.map_tmul, LinearMap.id_apply]
    simp only [add_zero]
    rw [c_negative_c_one_vacuum_early n hlow]
    simp
  · by_cases hhigh : 2 ≤ n
    · simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
        TensorProduct.map_tmul, LinearMap.id_apply]
      simp only [add_zero]
      rw [c_positive_c_one_vacuum_early n hhigh]
      simp
    · have hcases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
      rcases hcases with rfl | rfl | rfl
      · simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
          TensorProduct.map_tmul, LinearMap.id_apply]
        norm_num
        rw [c_one_c_minus_one_c_one_vacuum_early]
        simp
      · norm_num
      · simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
          TensorProduct.map_tmul, LinearMap.id_apply]
        simp only [add_zero]
        rw [c_one_c_one_vacuum_early]
        simp

private theorem c_zero_c_minus_one_c_one_vacuum :
    c (K := ℂ) 0 (c (-1) (c 1 (vacuum : Fock ℂ))) =
      Finsupp.single ({1, 3, 5} : Finset ℕ) 1 := by
  have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (c 1 (vacuum : Fock ℂ)))
    (c_c (K := ℂ) 0 (-1))
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  rw [c_minus_one_c_zero_c_one_vacuum] at h
  have hsub :
      c (K := ℂ) 0 (c (-1) (c 1 (vacuum : Fock ℂ))) -
        Finsupp.single ({1, 3, 5} : Finset ℕ) 1 = 0 := by
    simpa only [sub_eq_add_neg, map_zero, LinearMap.zero_apply] using h
  calc
    c (K := ℂ) 0 (c (-1) (c 1 (vacuum : Fock ℂ))) =
        (c (K := ℂ) 0 (c (-1) (c 1 (vacuum : Fock ℂ))) -
          Finsupp.single ({1, 3, 5} : Finset ℕ) 1) +
          Finsupp.single ({1, 3, 5} : Finset ℕ) 1 := by module
    _ = 0 + Finsupp.single ({1, 3, 5} : Finset ℕ) 1 := by rw [hsub]
    _ = Finsupp.single ({1, 3, 5} : Finset ℕ) 1 := by simp

private theorem c_zero_c_minus_one_c_zero_c_one_vacuum :
    c (K := ℂ) 0 (c (-1) (c 0 (c 1 (vacuum : Fock ℂ)))) = 0 := by
  have h := congrArg
    (fun T : Module.End ℂ (Fock ℂ) => T (c 0 (c 1 (vacuum : Fock ℂ))))
    (c_c (K := ℂ) 0 (-1))
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  rw [c_zero_vacuum_c_zero] at h
  simpa only [map_zero, LinearMap.zero_apply, add_zero] using h

private theorem V_minus_one_c_one_vacuum (D : LatticeData) :
    V D (-1) (C D 1 (vacuumState D)) = (2 : ℂ) • wState D := by
  simp only [V, LinearMap.coe_mk, AddHom.coe_mk]
  have hsupport : Function.support (fun n : ℤ =>
      (2 * n - 1 : ℂ) • ((C D (-n) * C D (n - 1)) (C D 1 (vacuumState D)))) ⊆
        Set.Icc (0 : ℤ) 1 := by
    intro n hn
    constructor
    · by_contra hlow
      have hzero : (C D (-n) * C D (n - 1)) (C D 1 (vacuumState D)) = 0 := by
        simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
          TensorProduct.map_tmul, LinearMap.id_apply]
        rw [show c (K := ℂ) (-n) (c (n - 1) (c 1 (vacuum : Fock ℂ))) = 0 by
          have houter := c_positive_c_one_vacuum_at_least_one (-n) (by omega)
          have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (c 1 (vacuum : Fock ℂ)))
            (c_c (K := ℂ) (-n) (n - 1))
          simp only [LinearMap.add_apply, Module.End.mul_apply] at h
          rw [houter] at h
          simpa only [map_zero, LinearMap.zero_apply, add_zero] using h]
        simp
      exact hn (by simp [hzero])
    · by_contra hhigh
      have hzero : (C D (-n) * C D (n - 1)) (C D 1 (vacuumState D)) = 0 := by
        simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
          TensorProduct.map_tmul, LinearMap.id_apply]
        have hc := c_positive_c_one_vacuum_at_least_one (n - 1) (by omega)
        rw [hc]
        simp
      exact hn (by simp [hzero])
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (0 : ℤ) 1)
    (by simpa [Finset.coe_Icc, sub_eq_add_neg] using hsupport)]
  have hsum (f : ℤ → State D) :
      (∑ n ∈ Finset.Icc (0 : ℤ) 1, f n) = f 0 + f 1 := by
    have hinterval : Finset.Icc (0 : ℤ) 1 = {0, 1} := by decide
    rw [hinterval]
    simp [Finset.sum_insert]
  rw [hsum]
  rw [wState]
  simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
    TensorProduct.map_tmul, LinearMap.id_apply]
  norm_num
  rw [c_zero_c_minus_one_c_one_vacuum, c_minus_one_c_zero_c_one_vacuum]
  simp only [TensorProduct.tmul_neg, smul_neg]
  module

private theorem V_minus_one_c_zero_c_one_vacuum (D : LatticeData) :
    V D (-1) (C D 0 (C D 1 (vacuumState D))) = 0 := by
  simp only [V, LinearMap.coe_mk, AddHom.coe_mk]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hlow : n ≤ -1
  · simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
      TensorProduct.map_tmul, LinearMap.id_apply]
    have hc : c (K := ℂ) (-n) (c (n + -1) (c 0 (c 1 (vacuum : Fock ℂ)))) = 0 := by
      simpa only [sub_eq_add_neg] using c_negative_c_zero_c_one_vacuum n hlow
    rw [hc]
    simp
  · by_cases hhigh : 2 ≤ n
    · simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
        TensorProduct.map_tmul, LinearMap.id_apply]
      have hc := c_positive_c_zero_c_one_vacuum (n - 1) (by omega)
      rw [show c (K := ℂ) (n + -1) (c 0 (c 1 (vacuum : Fock ℂ))) = 0 by
        simpa only [sub_eq_add_neg] using hc]
      simp
    · have hcases : n = 0 ∨ n = 1 := by omega
      rcases hcases with rfl | rfl
      · simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
          TensorProduct.map_tmul, LinearMap.id_apply]
        norm_num
        rw [c_zero_c_minus_one_c_zero_c_one_vacuum]
        simp
      · simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
          TensorProduct.map_tmul, LinearMap.id_apply]
        norm_num
        rw [c_zero_vacuum_c_zero]
        simp

private theorem c_one_c_one_vacuum :
    c (K := ℂ) 1 (c 1 (vacuum : Fock ℂ)) = 0 := by
  rw [c_one_vacuum]
  simp [c, create, Finsupp.linearCombination_single, createBasis, sign]

private theorem c_one_c_zero_vacuum_single :
    c (K := ℂ) 1 (c 0 (vacuum : Fock ℂ)) =
      Finsupp.single ({1, 3} : Finset ℕ) 1 := by
  rw [c_zero_vacuum]
  have hset : insert 1 ({3} : Finset ℕ) = {1, 3} := by decide
  have hcard : ({s ∈ ({3} : Finset ℕ) | s = 0}.card) = 0 := by decide
  simp [c, create, Finsupp.linearCombination_single, createBasis, sign, hset, hcard]

private theorem L_neg_one_c_one_vacuum :
    L (K := ℂ) (-1) (c 1 (vacuum : Fock ℂ)) =
      c (K := ℂ) 0 (vacuum : Fock ℂ) := by
  have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (vacuum : Fock ℂ))
    (L_c_commutator (K := ℂ) (-1) 1)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    BcGhostVacuum.L_vacuum_annihilation (-1) (by omega), map_zero, sub_zero,
    Int.cast_neg, Int.cast_one] at h
  norm_num at h
  simpa only [c_zero_vacuum] using h

private theorem L_zero_c_one_vacuum :
    L (K := ℂ) 0 (c 1 (vacuum : Fock ℂ)) =
      -(c (K := ℂ) 1 (vacuum : Fock ℂ)) := by
  have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (vacuum : Fock ℂ))
    (L_c_commutator (K := ℂ) 0 1)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    BcGhostVacuum.L_vacuum_annihilation 0 (by omega), map_zero, sub_zero, zero_mul,
    Int.cast_zero] at h
  norm_num at h
  exact h

private theorem L_one_c_one_vacuum :
    L (K := ℂ) 1 (c 1 (vacuum : Fock ℂ)) = 0 := by
  have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (vacuum : Fock ℂ))
    (L_c_commutator (K := ℂ) 1 1)
  have hc : c (K := ℂ) 2 (vacuum : Fock ℂ) = 0 := by
    exact c_positive_vacuum_zero 2 (by omega)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    BcGhostVacuum.L_vacuum_annihilation 1 (by omega), map_zero, sub_zero, smul_zero,
    Int.cast_one, neg_mul, one_mul, neg_neg] at h
  rw [show (1 + 1 : ℤ) = 2 by norm_num, hc] at h
  norm_num at h
  exact h

private theorem outer_minus_one_c_one_vacuum :
    BcGhostStressTails.outerNormalPair (-1) (c 1 (vacuum : Fock ℂ)) =
      Finsupp.single ({1, 3} : Finset ℕ) 1 := by
  simp only [BcGhostStressTails.outerNormalPair, if_pos (show (-1 : ℤ) ≤ -1 by omega),
    LinearMap.comp_apply, L_neg_one_c_one_vacuum]
  norm_num
  rw [c_one_c_zero_vacuum_single]

private theorem outer_zero_c_one_vacuum :
    BcGhostStressTails.outerNormalPair 0 (c 1 (vacuum : Fock ℂ)) =
      Finsupp.single ({1, 3} : Finset ℕ) 1 := by
  simp only [BcGhostStressTails.outerNormalPair, if_pos (show (-1 : ℤ) ≤ 0 by omega),
    LinearMap.comp_apply, L_zero_c_one_vacuum, map_neg]
  simp [c_zero_c_one_vacuum]

private theorem outer_one_c_one_vacuum :
    BcGhostStressTails.outerNormalPair 1 (c 1 (vacuum : Fock ℂ)) = 0 := by
  simp only [BcGhostStressTails.outerNormalPair, if_pos (show (-1 : ℤ) ≤ 1 by omega),
    LinearMap.comp_apply, L_one_c_one_vacuum, map_zero]

private theorem c_positive_c_one_vacuum (n : ℤ) (hn : 2 ≤ n) :
    c (K := ℂ) n (c 1 (vacuum : Fock ℂ)) = 0 := by
  rw [c_one_vacuum, c, if_neg (by omega)]
  apply annihilate_eq_zero
  simp [occupied]

private theorem c_one_c_minus_one_c_one_vacuum :
    c (K := ℂ) 1 (c (-1) (c 1 (vacuum : Fock ℂ))) = 0 := by
  have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (c 1 (vacuum : Fock ℂ)))
    (c_c (K := ℂ) 1 (-1))
  simp only [LinearMap.add_apply, Module.End.mul_apply, c_one_c_one_vacuum,
    map_zero, add_zero] at h
  exact h

private theorem c_negative_c_one_vacuum (n : ℤ) (hn : n ≤ -2) :
    c (K := ℂ) (-n) (c n (c 1 (vacuum : Fock ℂ))) = 0 := by
  have hzero : c (K := ℂ) (-n) (c 1 (vacuum : Fock ℂ)) = 0 :=
    c_positive_c_one_vacuum (-n) (by omega)
  have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (c 1 (vacuum : Fock ℂ)))
    (c_c (K := ℂ) (-n) n)
  simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
    hzero, map_zero, add_zero]
    using h

private theorem V_zero_one_oscillator (D : LatticeData)
    (t : Fin D.rank) : V D 0 (jState D t) = 0 := by
  simp only [V, LinearMap.coe_mk, AddHom.coe_mk]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hlow : n ≤ -2
  · simp only [LatticeBcGhostBrstCharge.C, Module.End.mul_apply, jState,
      TensorProduct.map_tmul, LinearMap.id_apply]
    simp only [add_zero]
    rw [c_negative_c_one_vacuum n hlow]
    simp
  · by_cases hhigh : 2 ≤ n
    · simp only [LatticeBcGhostBrstCharge.C, Module.End.mul_apply, jState,
        TensorProduct.map_tmul, LinearMap.id_apply]
      simp only [add_zero]
      rw [c_positive_c_one_vacuum n hhigh]
      simp
    · have hcases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
      rcases hcases with rfl | rfl | rfl
      · simp only [LatticeBcGhostBrstCharge.C, Module.End.mul_apply, jState,
          TensorProduct.map_tmul, LinearMap.id_apply]
        norm_num
        rw [c_one_c_minus_one_c_one_vacuum]
        simp
      · norm_num
      · simp only [LatticeBcGhostBrstCharge.C, Module.End.mul_apply, jState,
          TensorProduct.map_tmul, LinearMap.id_apply]
        simp only [add_zero]
        rw [c_one_c_one_vacuum]
        simp

private theorem L_positive_c_one_vacuum (n : ℤ) (hn : 1 ≤ n) :
    L (K := ℂ) n (c 1 (vacuum : Fock ℂ)) = 0 := by
  have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (vacuum : Fock ℂ))
    (L_c_commutator (K := ℂ) n 1)
  have hc : c (K := ℂ) (n + 1) (vacuum : Fock ℂ) = 0 := by
    exact c_positive_vacuum_zero (n + 1) (by omega)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    BcGhostVacuum.L_vacuum_annihilation n (by omega), map_zero, sub_zero, hc, smul_zero] at h
  exact h

end

end D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix

namespace D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge LatticeBcGhostBrstCAction
  LatticeBcGhostBrstVacuumClass BcGhostFockSupport BcGhostStressCurrent
  LatticeFiniteNegativeGeneration
open LatticeSugawaraVirasoro
open scoped BigOperators TensorProduct

noncomputable section

theorem Q_vacuum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Q D H (vacuumState D) = 0 := by
  simpa [vacuumState] using vacuum_closed D H

theorem Q_c0_vacuum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Q D H (uState D) = (-2 : ℂ) • zState D := by
  have h := congrArg (fun T : Module.End ℂ (State D) => T (vacuumState D))
    (c_action D H 0)
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    uState, zState, Q_vacuum D H, map_zero, V_zero_vacuum D, smul_smul] at h
  norm_num at h
  change Q D H (C D 0 (vacuumState D)) =
    (-2 : ℂ) • C D (-1) (C D 1 (vacuumState D))
  simpa only [neg_smul] using h

theorem Q_one_oscillator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (t : Fin D.rank) :
    Q D H (jState D t) =
      ∑ s : Fin D.rank,
        (neutralCoefficient D H s t - kronecker D s t) • kState D s := by
  classical
  have hbound : BcGhostBrstSupport.bound (c (K := ℂ) 1 (vacuum : Fock ℂ)) = 1 := by
    rw [c_one_vacuum]
    simp [BcGhostBrstSupport.bound, occupied]
  have hsub :
      Finset.Icc (-1 : ℤ) 1 ⊆
        Finset.Icc (-BcGhostBrstSupport.bound (c (K := ℂ) 1 (vacuum : Fock ℂ)) - 2)
          (chargeUpper D H (neutralMatter D t) (c (K := ℂ) 1 (vacuum : Fock ℂ))) := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hu : 1 ≤ chargeUpper D H (neutralMatter D t)
        (c (K := ℂ) 1 (vacuum : Fock ℂ)) := by
      simp [chargeUpper, hbound]
    rw [Finset.mem_Icc]
    constructor
    · rw [hbound]
      omega
    · exact hn'.2.trans hu
  rw [jState, Q_tmul]
  rw [← Finset.sum_subset hsub]
  · have hsum (f : ℤ → State D) :
        (∑ n ∈ Finset.Icc (-1 : ℤ) 1, f n) = f (-1) + f 0 + f 1 := by
      have hinterval : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by decide
      rw [hinterval]
      simp [Finset.sum_insert, add_assoc]
    rw [hsum]
    have hminus :
        sugawaraMode D H (-1) (neutralMatter D t) ⊗ₜ[ℂ]
            c (K := ℂ) 1 (c 1 (vacuum : Fock ℂ)) = 0 := by
      rw [c_one_c_one_vacuum]
      simp
    have hzero :
        sugawaraMode D H 0 (neutralMatter D t) ⊗ₜ[ℂ]
            c (K := ℂ) 0 (c 1 (vacuum : Fock ℂ)) =
          ∑ s : Fin D.rank,
            neutralCoefficient D H s t • kState D s := by
      rw [sugawaraMode_zero_neutralMatter D H t, c_zero_c_one_vacuum]
      rw [TensorProduct.sum_tmul]
      simp only [TensorProduct.smul_tmul', kState, jState,
        LatticeBcGhostBrstCharge.C, TensorProduct.map_tmul,
        LinearMap.id_apply, c_zero_c_one_vacuum]
    have htail :
        (2 : ℂ)⁻¹ •
            (neutralMatter D t ⊗ₜ[ℂ]
              BcGhostStressTails.outerNormalPair (-1) (c 1 (vacuum : Fock ℂ))) +
          (2 : ℂ)⁻¹ •
            (neutralMatter D t ⊗ₜ[ℂ]
              BcGhostStressTails.outerNormalPair 0 (c 1 (vacuum : Fock ℂ))) =
          -(kronecker D t t) • kState D t := by
      rw [outer_minus_one_c_one_vacuum, outer_zero_c_one_vacuum]
      rw [show kronecker D t t = 1 by simp [kronecker]]
      simp only [kState, jState, LatticeBcGhostBrstCharge.C,
        TensorProduct.map_tmul, LinearMap.id_apply, c_zero_c_one_vacuum,
        TensorProduct.tmul_neg, smul_neg]
      module
    norm_num
    rw [hminus, hzero, outer_one_c_one_vacuum]
    rw [sugawaraMode_positive_neutralMatter D H t 1 (by omega)]
    simp only [TensorProduct.tmul_zero, TensorProduct.zero_tmul, smul_zero,
      zero_add, add_zero]
    calc
      _ =
          ((2 : ℂ)⁻¹ •
              (neutralMatter D t ⊗ₜ[ℂ]
                BcGhostStressTails.outerNormalPair (-1) (c 1 (vacuum : Fock ℂ)))) +
            ((2 : ℂ)⁻¹ •
              (neutralMatter D t ⊗ₜ[ℂ]
                BcGhostStressTails.outerNormalPair 0 (c 1 (vacuum : Fock ℂ)))) +
          ∑ s : Fin D.rank, neutralCoefficient D H s t • kState D s := by
            module
      _ = ∑ s : Fin D.rank,
          (neutralCoefficient D H s t - kronecker D s t) • kState D s := by
        rw [htail]
        simp_rw [sub_smul]
        rw [Finset.sum_sub_distrib]
        simp only [kronecker, ite_smul, one_smul, zero_smul]
        rw [Finset.sum_ite_eq']
        simp <;> module
  · intro n hn hnot
    by_cases hlow : n < -1
    · have hc : c (K := ℂ) (-n) (c 1 (vacuum : Fock ℂ)) = 0 :=
          c_positive_c_one_vacuum (-n) (by omega)
      simp [BcGhostStressTails.outerNormalPair, show ¬(-1 : ℤ) ≤ n by omega, hc]
    · have hhigh : 1 < n := by
        by_contra hnot_high
        exact hnot (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hm := sugawaraMode_positive_neutralMatter D H t n (by omega)
      have hL := L_positive_c_one_vacuum n (by omega)
      simp [hm, BcGhostStressTails.outerNormalPair,
        show (-1 : ℤ) ≤ n by omega, hL]

theorem Q_c0_one_oscillator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (t : Fin D.rank) :
    Q D H (kState D t) = 0 := by
  have hQj : Q D H (jState D t) =
      ∑ s : Fin D.rank,
        (neutralCoefficient D H s t - kronecker D s t) • kState D s :=
    Q_one_oscillator D H t
  have hC : C D 0 (Q D H (jState D t)) = 0 := by
    rw [hQj]
    simp only [map_sum, map_smul]
    apply Finset.sum_eq_zero
    intro s hs
    simp only [kState, LatticeBcGhostBrstCharge.C, Module.End.mul_apply,
      jState, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [c_zero_vacuum_c_zero]
    simp
  have h := congrArg (fun T : Module.End ℂ (State D) => T (jState D t))
    (c_action D H 0)
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    V_zero_one_oscillator D t, map_zero, hC] at h
  simpa only [kState, add_zero, smul_zero] using h

theorem Q_z (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Q D H (zState D) = 0 := by
  have h1 : Q D H (C D 1 (vacuumState D)) =
      C D 1 (C D 0 (vacuumState D)) := by
    have h := congrArg
      (fun T : Module.End ℂ (State D) => T (vacuumState D))
      (c_action D H 1)
    simp only [LinearMap.add_apply, Module.End.mul_apply] at h
    change Q D H (C D 1 (vacuumState D)) + C D 1 (Q D H (vacuumState D)) =
      -(2 : ℂ)⁻¹ • V D 1 (vacuumState D) at h
    rw [Q_vacuum D H, V_one_vacuum D] at h
    simp only [map_zero, LinearMap.zero_apply, smul_smul] at h
    norm_num at h
    exact h
  have hcross : C D (-1) (C D 1 (C D 0 (vacuumState D))) =
      -wState D := by
    have hanti : c (K := ℂ) 1 (c 0 (vacuum : Fock ℂ)) =
        -(c 0 (c 1 (vacuum : Fock ℂ))) := by
      have h := congrArg
        (fun T : Module.End ℂ (Fock ℂ) => T (vacuum : Fock ℂ))
        (c_c (K := ℂ) 1 0)
      simp only [LinearMap.add_apply, Module.End.mul_apply, map_zero,
        LinearMap.zero_apply] at h
      calc
        c (K := ℂ) 1 (c 0 (vacuum : Fock ℂ)) =
            c (K := ℂ) 1 (c 0 (vacuum : Fock ℂ)) +
              c 0 (c 1 (vacuum : Fock ℂ)) -
              c 0 (c 1 (vacuum : Fock ℂ)) := by abel
        _ = 0 - c 0 (c 1 (vacuum : Fock ℂ)) := by rw [h]
        _ = -(c 0 (c 1 (vacuum : Fock ℂ))) := by simp
    simp only [wState, C, Module.End.mul_apply, vacuumState, vacuumVector,
      TensorProduct.map_tmul, LinearMap.id_apply]
    rw [hanti]
    simp only [map_neg, TensorProduct.tmul_neg, smul_neg]
  have hminus := congrArg
    (fun T : Module.End ℂ (State D) => T (C D 1 (vacuumState D)))
    (c_action D H (-1))
  simp only [LinearMap.add_apply, Module.End.mul_apply] at hminus
  rw [h1] at hminus
  change Q D H (C D (-1) (C D 1 (vacuumState D))) +
      C D (-1) (C D 1 (C D 0 (vacuumState D))) =
        -(2 : ℂ)⁻¹ • V D (-1) (C D 1 (vacuumState D)) at hminus
  rw [hcross, V_minus_one_c_one_vacuum D] at hminus
  change Q D H (C D (-1) (C D 1 (vacuumState D))) = 0
  norm_num [smul_smul] at hminus
  exact hminus

theorem Q_w (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Q D H (wState D) = 0 := by
  have h1 : Q D H (C D 1 (vacuumState D)) =
      C D 1 (C D 0 (vacuumState D)) := by
    have h := congrArg
      (fun T : Module.End ℂ (State D) => T (vacuumState D))
      (c_action D H 1)
    simp only [LinearMap.add_apply, Module.End.mul_apply] at h
    change Q D H (C D 1 (vacuumState D)) + C D 1 (Q D H (vacuumState D)) =
      -(2 : ℂ)⁻¹ • V D 1 (vacuumState D) at h
    rw [Q_vacuum D H, V_one_vacuum D] at h
    simp only [map_zero, LinearMap.zero_apply, smul_smul] at h
    norm_num at h
    exact h
  have hc00 : c (K := ℂ) 0 (c 0 (vacuum : Fock ℂ)) = 0 := by
    rw [c_zero_vacuum]
    simp [c, create, Finsupp.linearCombination_single, createBasis, sign]
  have hc010 : c (K := ℂ) 0 (c 1 (c 0 (vacuum : Fock ℂ))) = 0 := by
    have h := congrArg (fun T : Module.End ℂ (Fock ℂ) => T (c 0 (vacuum : Fock ℂ)))
      (c_c (K := ℂ) 0 1)
    simp only [LinearMap.add_apply, Module.End.mul_apply, hc00, map_zero,
      LinearMap.zero_apply, add_zero] at h
    exact h
  have h0 : Q D H (C D 0 (C D 1 (vacuumState D))) = 0 := by
    have hC010 : C D 0 (C D 1 (C D 0 (vacuumState D))) = 0 := by
      simp only [C, Module.End.mul_apply, vacuumState, vacuumVector,
        TensorProduct.map_tmul, LinearMap.id_apply]
      rw [hc010]
      simp
    have h := congrArg
      (fun T : Module.End ℂ (State D) => T (C D 1 (vacuumState D)))
      (c_action D H 0)
    simp only [LinearMap.add_apply, Module.End.mul_apply] at h
    rw [h1] at h
    change Q D H (C D 0 (C D 1 (vacuumState D))) +
        C D 0 (C D 1 (C D 0 (vacuumState D))) =
          -(2 : ℂ)⁻¹ • V D 0 (C D 1 (vacuumState D)) at h
    rw [V_zero_c_one_vacuum D] at h
    rw [hC010] at h
    simp only [map_zero, LinearMap.zero_apply, add_zero, smul_zero] at h
    exact h
  have hminus := congrArg
    (fun T : Module.End ℂ (State D) => T (C D 0 (C D 1 (vacuumState D))))
    (c_action D H (-1))
  simp only [LinearMap.add_apply, Module.End.mul_apply] at hminus
  rw [h0] at hminus
  change Q D H (C D (-1) (C D 0 (C D 1 (vacuumState D)))) +
      C D (-1) 0 = -(2 : ℂ)⁻¹ •
        V D (-1) (C D 0 (C D 1 (vacuumState D))) at hminus
  rw [V_minus_one_c_zero_c_one_vacuum D] at hminus
  change Q D H (C D (-1) (C D 0 (C D 1 (vacuumState D)))) = 0
  simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    map_zero, LinearMap.zero_apply, add_zero, smul_zero] using hminus

end

end D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix
