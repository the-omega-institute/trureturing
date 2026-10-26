/- GID: D5/S3/VertexAlgebra/Lattice/LeechPeirceMultiplicities
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LeechPeirceMultiplicities
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual ordinary Leech fixed-energy-two trace and Peirce multiplicities. -/

import D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension
import D5.S3.VertexAlgebra.Lattice.NormFourTwoEigenline
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Algebra.BigOperators.Sym
import Batteries.Tactic.OpenPrivate

/-! Ordinary untwisted theta-fixed energy two for the actual Golay Leech lattice.
The lattice vertex construction follows Bakalov--Kac and FLM. The norm-four
Ising formula is due to Dong--Mason--Zhu, as recalled by Shimakura (1.3).
No orbifold, Monster module or string completion is asserted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.VertexAlgebra.Lattice.LeechPeirceMultiplicities
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeActualProductKernel LatticePositiveEnergy
open LatticeSugawaraConformal LatticeInvolution NormFourVirasoroVector RootlessLowGrades
open InvolutionRootlessLowGrades
open D5.S3.Arith.Lattices.Golay GolayEncoder IntegerLeech
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

open private Q R Gi E ground quadratic_sum charge_contract zero_mode_Q zero_mode_E
  zero_mode_orbit_middle zero_mode_orbit_add zero_mode_orbit_sub
  norm_four_inner_bounds actual_basis_neutral_coe
  from D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
open private norm_sub from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open private Q_mem from D5.S3.VertexAlgebra.Lattice.NormFourTwoEigenline
open private pairOccupation_pair pairOccupation_injective
  from D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
open private normFourNeg normFourOrbitSetoid normFourOrbitMk normFourOrbitMk_neg
  normFourOrbitMk_rep normFourOrbit_rep_cases normFourOrbit_finite normFour_ne_zero
  normFourDoubleEquiv normFourDoubleDecode
  from D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades
open private axisPoint axisPoint_raw shell_pairing axisFiberEquiv
  from D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension

private abbrev S (D : LatticeData) :=
  fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)

private theorem E_neg (D : LatticeData) (a : Charge D) : E D (-a) = E D a := by
  simp [E, add_comm]

private theorem E_basis (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2) (b : NormFour D) :
    E D b.1 = (actualFixedEnergyTwoBasis D hD hroot (Sum.inr (normFourOrbitMk D b)) : Carrier D) := by
  rw [actualFixedEnergyTwoBasis_charge_coe]
  change E D b.1 = E D (normFourOrbitRep D (normFourOrbitMk D b)).1
  rcases normFourOrbit_rep_cases D b with h | h
  · rw [h]
  · have hv := congrArg (fun c : NormFour D => c.1) h
    change -(normFourOrbitRep D (normFourOrbitMk D b)).1 = b.1 at hv
    rw [← hv, E_neg]

private theorem E_mem (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (b : Charge D) (hb : bilinear D b b = 4) : E D b ∈ S D := by
  rw [E_basis D hD hroot ⟨b, hb⟩]
  exact (actualFixedEnergyTwoBasis D hD hroot _).2

private theorem R_mem (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (i : Fin D.rank) : R D a i ∈ S D := by
  unfold R
  exact (S D).sum_mem fun j _ => (S D).smul_mem _ (Q_mem D hD hroot j i)

private theorem A_mem (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) : quadraticState D a ∈ S D := by
  rw [quadratic_sum]
  exact (S D).sum_mem fun i _ => (S D).smul_mem _ (R_mem D hD hroot a i)

private theorem orbit_invariant (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) (b : NormFour D) :
    mode D a 1 0 (E D b.1) ∈ S D := by
  by_cases he : b.1 = a
  · rw [he, zero_mode_E D a ha]
    exact (S D).add_mem ((S D).smul_mem _ (A_mem D hD hroot a)) (E_mem D hD hroot a ha)
  by_cases he' : b.1 = -a
  · rw [he', E_neg, zero_mode_E D a ha]
    exact (S D).add_mem ((S D).smul_mem _ (A_mem D hD hroot a)) (E_mem D hD hroot a ha)
  have hb := norm_four_inner_bounds D hD hroot a b.1 ha b.2 he he'
  by_cases hp : bilinear D a b.1 = -2
  · rw [zero_mode_orbit_add D a b.1 1 hp]
    apply (S D).add_mem ((S D).smul_mem _ (E_mem D hD hroot b.1 b.2))
    apply (S D).smul_mem
    apply E_mem D hD hroot
    rw [← sub_neg_eq_add, norm_sub, bilinear_neg_left, bilinear_symmetric D b.1 a,
      bilinear_neg_neg, ha, b.2, hp]
    norm_num
  by_cases hp' : bilinear D a b.1 = 2
  · rw [zero_mode_orbit_sub D a b.1 1 hp']
    apply (S D).add_mem ((S D).smul_mem _ (E_mem D hD hroot b.1 b.2))
    apply (S D).smul_mem
    apply E_mem D hD hroot
    rw [norm_sub, bilinear_symmetric D b.1 a, ha, b.2, hp']
    norm_num
  rw [zero_mode_orbit_middle D a b.1 1 (by omega) (by omega)]
  exact (S D).smul_mem _ (E_mem D hD hroot b.1 b.2)

private theorem invariant (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) :
    ∀ v ∈ S D, mode D a 1 0 v ∈ S D := by
  let b := actualFixedEnergyTwoBasis D hD hroot
  have hb (j : FixedTwoIndex D) : mode D a 1 0 (b j : Carrier D) ∈ S D := by
    rcases j with p | q
    · change mode D a 1 0 (actualFixedEnergyTwoBasis D hD hroot (Sum.inl p) : Carrier D) ∈ _
      rw [actual_basis_neutral_coe]
      rcases p with ⟨p, hp⟩
      obtain ⟨i, j, rfl⟩ := Multiset.card_eq_two.mp hp
      rw [pairOccupation_pair]
      have hQ : mode D a 1 0 (Q D i j) ∈ S D := by
        rw [zero_mode_Q]
        exact (S D).add_mem ((S D).add_mem
          ((S D).smul_mem _ (R_mem D hD hroot a j))
          ((S D).smul_mem _ (R_mem D hD hroot a i)))
          ((S D).smul_mem _ (E_mem D hD hroot a ha))
      simpa only [Q, monomial_add_single, ← X_pow_eq_monomial, pow_one] using hQ
    · change mode D a 1 0 (actualFixedEnergyTwoBasis D hD hroot (Sum.inr q) : Carrier D) ∈ _
      rw [actualFixedEnergyTwoBasis_charge_coe]
      exact orbit_invariant D hD hroot a ha (normFourOrbitRep D q)
  intro v hv
  letI : Finite (NormFourOrbit D) := normFourOrbit_finite D hD
  letI : Fintype (FixedTwoIndex D) := Fintype.ofFinite _
  have hs := congrArg (fun w : S D => (w : Carrier D)) (b.sum_repr ⟨v, hv⟩)
  rw [← hs]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  exact (S D).sum_mem fun j _ => (S D).smul_mem _ (hb j)

private def L (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) : Module.End ℂ (S D) :=
  (mode D a 1 0).restrict (invariant D hD hroot a ha)

private def pair {ι : Type*} (i j : ι) : Sym ι 2 := ⟨{i, j}, by simp⟩

private theorem pair_cancel_right {ι : Type*} (i j k : ι) :
    pair i k = pair j k ↔ i = j := by
  change (⟨i ::ₘ {k}, _⟩ : Sym ι 2) = ⟨j ::ₘ {k}, _⟩ ↔ _
  simp only [Subtype.mk.injEq, Multiset.cons_inj_left]

private theorem pair_cancel_left {ι : Type*} (i j k : ι) :
    pair k i = pair k j ↔ i = j := by
  change (⟨k ::ₘ {i}, _⟩ : Sym ι 2) = ⟨k ::ₘ {j}, _⟩ ↔ _
  simp only [Subtype.mk.injEq, Multiset.cons_inj_right, Multiset.singleton_inj]

private theorem Q_basis (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2) (i j : Fin D.rank) :
    (actualFixedEnergyTwoBasis D hD hroot (Sum.inl (pair i j)) : Carrier D) = Q D i j := by
  rw [actual_basis_neutral_coe, pair, pairOccupation_pair]
  simp only [Q, monomial_add_single, ← X_pow_eq_monomial, pow_one]

private def qstate (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2) (i j : Fin D.rank) : S D :=
  actualFixedEnergyTwoBasis D hD hroot (Sum.inl (pair i j))

private def estate (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2) (b : NormFour D) : S D :=
  actualFixedEnergyTwoBasis D hD hroot (Sum.inr (normFourOrbitMk D b))

private def rstate (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2) (a : Charge D) (i : Fin D.rank) : S D :=
  ∑ k, (a k : ℂ) • qstate D hD hroot k i

private theorem rstate_coe (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2) (a : Charge D) (i : Fin D.rank) :
    (rstate D hD hroot a i : Carrier D) = R D a i := by
  simp only [rstate, Submodule.coe_sum, Submodule.coe_smul, qstate, Q_basis, R]

private theorem neutral_diagonal (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) (p : Sym (Fin D.rank) 2) :
    (actualFixedEnergyTwoBasis D hD hroot).repr
        (L D hD hroot a ha (actualFixedEnergyTwoBasis D hD hroot (Sum.inl p))) (Sum.inl p) =
      ((p.1.map fun i => (a i : ℂ) * Gi D i a).sum) / 8 := by
  rcases p with ⟨p, hp⟩
  obtain ⟨i, j, rfl⟩ := Multiset.card_eq_two.mp hp
  let B := actualFixedEnergyTwoBasis D hD hroot
  have he : L D hD hroot a ha (B (Sum.inl (pair i j))) =
      (Gi D i a / 8) • rstate D hD hroot a j +
      (Gi D j a / 8) • rstate D hD hroot a i +
      (Gi D i a * Gi D j a / 4) • estate D hD hroot ⟨a, ha⟩ := by
    apply Subtype.ext
    change mode D a 1 0 (B (Sum.inl (pair i j)) : Carrier D) = _
    rw [Q_basis, zero_mode_Q]
    simp only [Submodule.coe_add, Submodule.coe_smul, rstate_coe,
      estate, ← E_basis, one_mul]
  change B.repr (L D hD hroot a ha (B (Sum.inl (pair i j)))) (Sum.inl (pair i j)) = _
  rw [he]
  have hj : (B.repr (rstate D hD hroot a j)) (Sum.inl (pair i j)) = (a i : ℂ) := by
    simp [rstate, qstate, B, Finsupp.single_apply, pair_cancel_right, eq_comm]
  have hi : (B.repr (rstate D hD hroot a i)) (Sum.inl (pair i j)) = (a j : ℂ) := by
    have hc (k : Fin D.rank) : pair k i = pair i j ↔ k = j := by
      rw [show pair i j = pair j i by apply Subtype.ext; exact Multiset.pair_comm i j]
      exact pair_cancel_right k j i
    simp [rstate, qstate, B, Finsupp.single_apply, hc, eq_comm]
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hj, hi]
  simp [estate, B, pair, Finsupp.single_apply]
  ring

private theorem sum_pair_weights {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    (∑ p : Sym ι 2, (p.1.map w).sum) =
      (Fintype.card ι + 1 : ℂ) * ∑ i, w i := by
  classical
  let f (p : Sym2 ι) : ℂ := (((Sym2.equivSym ι) p).1.map w).sum
  have hf (i j : ι) : f s(i, j) = w i + w j := by
    change (Multiset.map w ({i, j} : Multiset ι)).sum = _
    simp
  have hs (s : Finset ι) : ∑ p ∈ s.sym2, f p = (s.card + 1 : ℂ) * ∑ i ∈ s, w i := by
    induction s using Finset.cons_induction with
    | empty => simp
    | cons i s hi ih =>
      rw [Finset.sym2_cons, Finset.sum_disjUnion, Finset.sum_map]
      simp only [Sym2.mkEmbedding_apply, hf, Finset.sum_cons, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul, Finset.card_cons]
      rw [ih]
      push_cast
      ring
  have hu : (Finset.univ : Finset ι).sym2 = Finset.univ := by ext p; simp
  have h := hs Finset.univ
  rw [hu] at h
  exact ((Sym2.equivSym ι).sum_comp (fun p : Sym ι 2 => (p.1.map w).sum)).symm.trans h

private theorem neutral_trace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) :
    (∑ p : Sym (Fin D.rank) 2, (actualFixedEnergyTwoBasis D hD hroot).repr
      (L D hD hroot a ha (actualFixedEnergyTwoBasis D hD hroot (Sum.inl p))) (Sum.inl p)) =
      (D.rank + 1 : ℂ) / 2 := by
  simp_rw [neutral_diagonal]
  rw [← Finset.sum_div, sum_pair_weights, Fintype.card_fin, charge_contract, ha]
  push_cast
  ring

private def eigenvalue : Fin 4 → ℂ := ![0, 1/16, 1/2, 2]

private def projection {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) : Fin 4 → Module.End ℂ V :=
  ![1 - (37/2 : ℂ) • T + (41 : ℂ) • (T*T) - (16 : ℂ) • (T*T*T),
    (4096/217 : ℂ) • (T*T*T - (5/2 : ℂ) • (T*T) + T),
    (-64/21 : ℂ) • (T*T*T - (33/16 : ℂ) • (T*T) + (1/8 : ℂ) • T),
    (16/93 : ℂ) • (T*T*T - (9/16 : ℂ) • (T*T) + (1/32 : ℂ) • T)]

private theorem spectral_projections {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V)
    (hq : T * (T - (1/16 : ℂ) • 1) * (T - (1/2 : ℂ) • 1) *
      (T - (2 : ℂ) • 1) = 0) :
    (∀ i, LinearMap.IsProj (T.eigenspace (eigenvalue i)) (projection T i)) ∧
    (∑ i, projection T i) = 1 ∧
    (∑ i, eigenvalue i • projection T i) = T := by
  have hp (i : Fin 4) : (T - eigenvalue i • 1) * projection T i = 0 := by
    have he : (T - eigenvalue i • 1) * projection T i =
        (![(-16 : ℂ), 4096/217, -64/21, 16/93] i) •
          (T * (T - (1/16 : ℂ) • 1) * (T - (1/2 : ℂ) • 1) *
            (T - (2 : ℂ) • 1)) := by
      fin_cases i <;> ext v <;>
        simp only [projection, eigenvalue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Module.End.mul_apply,
          LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
          Module.End.one_apply, map_sub, map_add, map_smul] <;> module
    rw [he, hq, smul_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    constructor
    · intro v
      apply Module.End.mem_eigenspace_iff.mpr
      have h := LinearMap.congr_fun (hp i) v
      simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, LinearMap.zero_apply, sub_eq_zero] using h
    · intro v hv
      have he := Module.End.mem_eigenspace_iff.mp hv
      fin_cases i <;>
        simp only [projection, eigenvalue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Module.End.mul_apply,
          LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
          Module.End.one_apply] at he ⊢ <;>
        simp only [he, map_smul] <;> module
  · ext v
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
      projection, Matrix.cons_val_zero, Matrix.cons_val_succ, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.zero_apply,
      Module.End.one_apply]
    module
  · ext v
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
      projection, eigenvalue, Matrix.cons_val_zero, Matrix.cons_val_succ,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.zero_apply, Module.End.one_apply]
    module

end D5.S3.VertexAlgebra.Lattice.LeechPeirceMultiplicities
