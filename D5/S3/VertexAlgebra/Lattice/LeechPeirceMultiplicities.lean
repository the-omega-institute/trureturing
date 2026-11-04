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
import Mathlib.Algebra.BigOperators.Sym
import Batteries.Tactic.OpenPrivate

/-! Ordinary untwisted theta-fixed energy two for the actual Golay Leech lattice.
The lattice vertex construction follows Bakalov--Kac and FLM. The norm-four
Ising formula is due to Dong--Mason--Zhu, as recalled by Shimakura (1.3).
No orbifold, Monster module or string completion is asserted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace D5.S3.VertexAlgebra.Lattice.LeechPeirceMultiplicities
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeActualProductKernel LatticeActualGeneratorLocality LatticePositiveEnergy
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
open private norm_sub bilinear_sub_left from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open private Q_mem from D5.S3.VertexAlgebra.Lattice.NormFourTwoEigenline
open private pairOccupation_pair pairOccupation_injective
  from D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
open private normFourNeg normFourNeg_ne normFourOrbitSetoid normFourOrbitMk normFourOrbitMk_neg
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
  change (↑(∑ i, b.repr ⟨v, hv⟩ i • b i) : Carrier D) = v at hs
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
    have hc' (k : Fin D.rank) : pair i j = pair k i ↔ k = j := by rw [eq_comm]; exact hc k
    simp only [rstate, map_sum, map_smul]
    rw [Finsupp.finsetSum_apply]
    simp only [qstate, B, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, Sum.inl.injEq, smul_eq_mul, hc, hc']
    simp
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hj, hi]
  simp [estate, B, pair, Finsupp.single_apply]
  ring

private theorem sum_pair_weights {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℂ) :
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
  calc
    _ = (∑ p : Sym (Fin D.rank) 2,
        (p.1.map fun i => (a i : ℂ) * Gi D i a).sum) / 8 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun p _ => neutral_diagonal D hD hroot a ha p
    _ = ((Fintype.card (Fin D.rank) + 1 : ℂ) *
        ∑ i : Fin D.rank, (a i : ℂ) * Gi D i a) / 8 :=
      congrArg (fun z : ℂ => z / 8) (sum_pair_weights (fun i : Fin D.rank => (a i : ℂ) * Gi D i a))
    _ = _ := by rw [Fintype.card_fin, charge_contract, ha]; push_cast; ring

private def chargeCoeff (D : LatticeData) (b : Charge D) : Carrier D →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff (R := ℂ) 0).comp (Finsupp.lapply b)

private theorem charge_coordinate (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2) (q : NormFourOrbit D) :
    (actualFixedEnergyTwoBasis D hD hroot).coord (Sum.inr q) =
      (chargeCoeff D (normFourOrbitRep D q).1).comp (S D).subtype := by
  let B := actualFixedEnergyTwoBasis D hD hroot
  apply B.ext
  intro j
  change B.repr (B j) (Sum.inr q) = chargeCoeff D (normFourOrbitRep D q).1 (B j : Carrier D)
  rw [B.repr_self]
  dsimp only [B]
  rcases j with p | r
  · simp only [Finsupp.single_apply, Sum.inl_ne_inr, ite_false]
    change 0 = chargeCoeff D (normFourOrbitRep D q).1
      (actualFixedEnergyTwoBasis D hD hroot (Sum.inl p) : Carrier D)
    rw [actual_basis_neutral_coe]
    simp [chargeCoeff, normFour_ne_zero D (normFourOrbitRep D q), Finsupp.single_apply]
  · have hrep : (normFourOrbitRep D r).1 = (normFourOrbitRep D q).1 ↔ r = q := by
      constructor
      · intro h
        have he : normFourOrbitRep D r = normFourOrbitRep D q := Subtype.ext h
        simpa only [normFourOrbitMk_rep] using congrArg (normFourOrbitMk D) he
      · rintro rfl; rfl
    have hneg : -(normFourOrbitRep D r).1 ≠ (normFourOrbitRep D q).1 := by
      intro h
      have he : normFourNeg D (normFourOrbitRep D r) = normFourOrbitRep D q := Subtype.ext h
      have hrq : r = q := by
        simpa only [normFourOrbitMk_neg, normFourOrbitMk_rep] using congrArg (normFourOrbitMk D) he
      subst r
      exact normFourNeg_ne D _ he
    rw [actualFixedEnergyTwoBasis_charge_coe]
    simp only [chargeCoeff, LinearMap.comp_apply, Finsupp.lapply_apply,
      map_add, Finsupp.single_apply, hrep, hneg, ite_false, add_zero]
    by_cases hqr : q = r <;> simp [hqr, MvPolynomial.lcoeff_apply, eq_comm]

private theorem charge_E_coordinate (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (q : NormFourOrbit D) (b : NormFour D) :
    chargeCoeff D (normFourOrbitRep D q).1 (E D b.1) =
      if normFourOrbitMk D b = q then 1 else 0 := by
  rw [E_basis D hD hroot b]
  have h := LinearMap.congr_fun (charge_coordinate D hD hroot q)
    (actualFixedEnergyTwoBasis D hD hroot (Sum.inr (normFourOrbitMk D b)))
  simpa [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm] using h.symm

private theorem orbit_distinct (D : LatticeData) (b c : NormFour D)
    (hpos : bilinear D c.1 b.1 ≠ 4) (hneg : bilinear D c.1 b.1 ≠ -4) :
    normFourOrbitMk D c ≠ normFourOrbitMk D b := by
  intro h
  rcases Quotient.exact h with h | h
  · exact hpos (by rw [h, b.2])
  · apply hneg
    have he := congrArg (fun x : NormFour D => bilinear D x.1 b.1) h
    change bilinear D (-c.1) b.1 = bilinear D b.1 b.1 at he
    rw [bilinear_neg_left, b.2] at he
    omega

private theorem charge_diagonal (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) (q : NormFourOrbit D) :
    (actualFixedEnergyTwoBasis D hD hroot).repr
      (L D hD hroot a ha (actualFixedEnergyTwoBasis D hD hroot (Sum.inr q))) (Sum.inr q) =
      (bilinear D a (normFourOrbitRep D q).1 : ℂ)^2 / 16 := by
  change (actualFixedEnergyTwoBasis D hD hroot).coord (Sum.inr q) _ = _
  rw [charge_coordinate]
  change chargeCoeff D (normFourOrbitRep D q).1
    (mode D a 1 0 (actualFixedEnergyTwoBasis D hD hroot (Sum.inr q) : Carrier D)) = _
  rw [actualFixedEnergyTwoBasis_charge_coe]
  let b := normFourOrbitRep D q
  change chargeCoeff D b.1 (mode D a 1 0 (E D b.1)) = (bilinear D a b.1 : ℂ)^2 / 16
  have hE : chargeCoeff D b.1 (E D b.1) = 1 := by
    simpa only [b, normFourOrbitMk_rep, ite_true] using charge_E_coordinate D hD hroot q b
  have hA : chargeCoeff D b.1 (quadraticState D a) = 0 := by
    simp [chargeCoeff, quadraticState, Finsupp.single_apply, normFour_ne_zero D b, eq_comm]
  by_cases he : b.1 = a
  · rw [he, zero_mode_E D a ha]
    rw [he] at hE hA
    simp only [map_add, map_smul, hA, hE, smul_zero, zero_add]
    norm_num [he, ha]
  by_cases he' : b.1 = -a
  · have hEa : E D b.1 = E D a := by rw [he', E_neg]
    rw [hEa, zero_mode_E D a ha]
    rw [hEa] at hE
    simp only [map_add, map_smul, hA, hE, smul_zero, zero_add]
    norm_num [he', bilinear_neg_right, ha]
  have hb := norm_four_inner_bounds D hD hroot a b.1 ha b.2 he he'
  by_cases hp : bilinear D a b.1 = -2
  · have hn : bilinear D (a+b.1) (a+b.1) = 4 := by
      rw [← sub_neg_eq_add, norm_sub, bilinear_neg_left, bilinear_symmetric D b.1 a,
        bilinear_neg_neg, ha, b.2, hp]; norm_num
    have hd : normFourOrbitMk D (⟨a+b.1, hn⟩ : NormFour D) ≠ q := by
      rw [← normFourOrbitMk_rep D q]
      apply orbit_distinct D b ⟨a+b.1, hn⟩
      all_goals
        rw [bilinear_symmetric D (a+b.1) b.1, bilinear_add_right,
          bilinear_symmetric D b.1 a, hp, b.2]
        norm_num
    rw [zero_mode_orbit_add D a b.1 1 hp, map_add, map_smul, map_smul,
      hE, charge_E_coordinate D hD hroot q ⟨a+b.1, hn⟩, if_neg hd]
    norm_num [hp]
  by_cases hp' : bilinear D a b.1 = 2
  · have hn : bilinear D (a-b.1) (a-b.1) = 4 := by
      rw [norm_sub, bilinear_symmetric D b.1 a, ha, b.2, hp']; norm_num
    have hd : normFourOrbitMk D (⟨a-b.1, hn⟩ : NormFour D) ≠ q := by
      rw [← normFourOrbitMk_rep D q]
      apply orbit_distinct D b ⟨a-b.1, hn⟩
      all_goals
        have hh : bilinear D (a-b.1) b.1 = -2 := by
          rw [bilinear_sub_left, hp', b.2]; norm_num
        rw [hh]; norm_num
    rw [zero_mode_orbit_sub D a b.1 1 hp', map_add, map_smul, map_smul,
      hE, charge_E_coordinate D hD hroot q ⟨a-b.1, hn⟩, if_neg hd]
    norm_num [hp']
  rw [zero_mode_orbit_middle D a b.1 1 (by omega) (by omega), map_smul, hE]
  exact mul_one _

private theorem full_basis_trace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) [Fintype (NormFour D)] :
    LinearMap.trace ℂ (S D) (L D hD hroot a ha) = (D.rank + 1 : ℂ) / 2 +
      (∑ b : NormFour D, (bilinear D a b.1 : ℂ)^2) / 32 := by
  classical
  letI : Finite (NormFour D) := normFour_finite D hD
  letI : Finite (NormFourOrbit D) := normFourOrbit_finite D hD
  letI : Fintype (NormFourOrbit D) := Fintype.ofFinite _
  let B := actualFixedEnergyTwoBasis D hD hroot
  have hd : (∑ b : NormFour D, (bilinear D a b.1 : ℂ)^2) =
      2 * ∑ q : NormFourOrbit D, (bilinear D a (normFourOrbitRep D q).1 : ℂ)^2 := by
    rw [← (normFourDoubleEquiv D).sum_comp (fun b : NormFour D => (bilinear D a b.1 : ℂ)^2)]
    change (∑ x : NormFourOrbit D × Bool,
      (bilinear D a (normFourDoubleDecode D x).1 : ℂ)^2) = _
    simp [Fintype.sum_prod_type, normFourDoubleDecode, normFourNeg, bilinear_neg_right,
      Finset.sum_add_distrib, two_mul]
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  rw [Fintype.sum_sum_type]
  dsimp only [B]
  rw [neutral_trace]
  simp_rw [charge_diagonal]
  rw [← Finset.sum_div, hd]
  ring

private def axis_pairing_fiber (D : LatticeData)
    (e : Charge D ≃ₗ[ℤ] RealLeech.lattice)
    (hp : ∀ b c : Charge D, (bilinear D b c : ℝ) =
      RealLeech.pairing (e b : RealLeech.Space) (e c : RealLeech.Space))
    (s : NormFour D ≃ LeechMinimalCount.Sphere)
    (hs : ∀ b : NormFour D, RealLeech.castLinear (s b).1 = (e b.1 : RealLeech.Space)) (t : ℤ) :
    {b : NormFour D // bilinear D (s.symm axisPoint).1 b.1 = t} ≃
    {x : Fin 24 → ℤ // Admissible code x ∧ squareSum x = 32 ∧
      dotProduct (Pi.single (0 : Fin 24) 4 + Pi.single (1 : Fin 24) 4) x = 8*t} where
  toFun b := ⟨(s b.1).1, (s b.1).2.1, (s b.1).2.2, by
    have h := shell_pairing D e hp s hs (s.symm axisPoint) b.1
    rw [s.apply_symm_apply, axisPoint_raw, b.2] at h
    exact h.symm⟩
  invFun x := ⟨s.symm ⟨x.1, x.2.1, x.2.2.1⟩, by
    have h := shell_pairing D e hp s hs (s.symm axisPoint)
      (s.symm ⟨x.1, x.2.1, x.2.2.1⟩)
    rw [s.apply_symm_apply, s.apply_symm_apply, axisPoint_raw] at h
    have hx := x.2.2.2
    dsimp only at h
    omega⟩
  left_inv b := Subtype.ext (s.symm_apply_apply b.1)
  right_inv x := by
    apply Subtype.ext
    exact congrArg (fun z : LeechMinimalCount.Sphere => z.1)
      (s.apply_symm_apply ⟨x.1, x.2.1, x.2.2.1⟩)

private theorem actual_axis_square_sum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (e : Charge D ≃ₗ[ℤ] RealLeech.lattice)
    (hp : ∀ b c : Charge D, (bilinear D b c : ℝ) =
      RealLeech.pairing (e b : RealLeech.Space) (e c : RealLeech.Space))
    (s : NormFour D ≃ LeechMinimalCount.Sphere)
    (hs : ∀ b : NormFour D, RealLeech.castLinear (s b).1 = (e b.1 : RealLeech.Space))
    [Fintype (NormFour D)] :
    (∑ b : NormFour D, (bilinear D (s.symm axisPoint).1 b.1 : ℂ)^2) = 131040 := by
  classical
  letI : Finite (NormFour D) := normFour_finite D hD
  let a := s.symm axisPoint
  let T : Finset ℤ := {-4, -2, -1, 0, 1, 2, 4}
  have hb (b : NormFour D) : bilinear D a.1 b.1 ∈ T := by
    by_cases h : b.1 = a.1
    · simp [h, a.2, T]
    by_cases h' : b.1 = -a.1
    · simp [h', bilinear_neg_right, a.2, T]
    obtain ⟨hlo, hhi⟩ := norm_four_inner_bounds D hD hroot a.1 b.1 a.2 b.2 h h'
    interval_cases hc : bilinear D a.1 b.1 <;> simp [T, hc]
  have hf (t : ℤ) : Nat.card {b : NormFour D // bilinear D a.1 b.1 = t} =
      if t = 4 ∨ t = -4 then 1 else
      if t = 2 ∨ t = -2 then 4600 else
      if t = 1 ∨ t = -1 then 47104 else
      if t = 0 then 93150 else 0 := by
    exact (Nat.card_congr (axis_pairing_fiber D e hp s hs t)).trans
      (LeechAxisDistribution.axis_distribution 0 1 (by decide +kernel) t).2
  have hsum := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := T)
    (g := fun b : NormFour D => bilinear D a.1 b.1) (fun b _ => hb b)
    (fun b : NormFour D => (bilinear D a.1 b.1 : ℂ)^2)
  change (∑ b : NormFour D, (bilinear D a.1 b.1 : ℂ)^2) = _
  rw [← hsum]
  have hi (t : ℤ) : (∑ b ∈ (Finset.univ : Finset (NormFour D)) with bilinear D a.1 b.1 = t,
        (bilinear D a.1 b.1 : ℂ)^2) =
      (Nat.card {b : NormFour D // bilinear D a.1 b.1 = t} : ℂ) * (t : ℂ)^2 := by
    calc
      _ = ∑ b ∈ (Finset.univ : Finset (NormFour D)) with bilinear D a.1 b.1 = t, (t : ℂ)^2 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [(Finset.mem_filter.mp hb).2]
      _ = _ := by simp [Nat.card_eq_fintype_card, Fintype.card_subtype, nsmul_eq_mul]
  simp_rw [hi, hf]
  norm_num [T]

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
        simp only [projection, eigenvalue, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
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
        simp only [projection, eigenvalue, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Module.End.mul_apply,
          LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
          Module.End.one_apply] at he ⊢ <;>
        (try simp only [he, map_smul]) <;> module
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

private theorem spectral_dimensions {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V)
    (hq : T * (T - (1 / 16 : ℂ) • 1) * (T - (1 / 2 : ℂ) • 1) *
      (T - (2 : ℂ) • 1) = 0)
    (hn : Module.finrank ℂ V = 98580)
    (htrace : LinearMap.trace ℂ V T = (8215 / 2 : ℂ))
    (hodd : Module.finrank ℂ (T.eigenspace (1 / 16 : ℂ)) = 47104)
    (htwo : Module.finrank ℂ (T.eigenspace (2 : ℂ)) = 1) :
    (⨆ i : Fin 4, T.eigenspace (eigenvalue i)) = ⊤ ∧
    ∀ i : Fin 4, Module.finrank ℂ (T.eigenspace (eigenvalue i)) =
      ![49152, 47104, 2323, 1] i := by
  obtain ⟨hp, hsum, hweighted⟩ := spectral_projections T hq
  have hdim : (∑ i : Fin 4, (Module.finrank ℂ (T.eigenspace (eigenvalue i)) : ℂ)) = 98580 := by
    calc
      _ = LinearMap.trace ℂ V (∑ i : Fin 4, projection T i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => (hp i).trace.symm
      _ = _ := by rw [hsum, LinearMap.trace_one, hn]; norm_num
  have hwt : (∑ i : Fin 4, eigenvalue i *
      (Module.finrank ℂ (T.eigenspace (eigenvalue i)) : ℂ)) = (8215 / 2 : ℂ) := by
    calc
      _ = LinearMap.trace ℂ V (∑ i : Fin 4, eigenvalue i • projection T i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, (hp i).trace, smul_eq_mul]
      _ = _ := by rw [hweighted, htrace]
  norm_num [Fin.sum_univ_succ, eigenvalue, hodd, htwo] at hdim hwt
  change (Module.finrank ℂ (T.eigenspace (0 : ℂ)) : ℂ) +
    ((Module.finrank ℂ (T.eigenspace (1 / 16 : ℂ)) : ℂ) +
      ((Module.finrank ℂ (T.eigenspace (1 / 2 : ℂ)) : ℂ) +
        (Module.finrank ℂ (T.eigenspace (2 : ℂ)) : ℂ))) = 98580 at hdim
  change (1 / 16 : ℂ) * (Module.finrank ℂ (T.eigenspace (1 / 16 : ℂ)) : ℂ) +
    ((1 / 2 : ℂ) * (Module.finrank ℂ (T.eigenspace (1 / 2 : ℂ)) : ℂ) +
      2 * (Module.finrank ℂ (T.eigenspace (2 : ℂ)) : ℂ)) = (8215 / 2 : ℂ) at hwt
  rw [hodd, htwo] at hdim hwt
  have hhalfC : (Module.finrank ℂ (T.eigenspace (1 / 2 : ℂ)) : ℂ) = 2323 := by
    linear_combination 2 * hwt
  have hhalf : Module.finrank ℂ (T.eigenspace (1 / 2 : ℂ)) = 2323 := by exact_mod_cast hhalfC
  have hzeroC : (Module.finrank ℂ (T.eigenspace (0 : ℂ)) : ℂ) = 49152 := by
    rw [hhalf] at hdim
    linear_combination hdim
  have hzero : Module.finrank ℂ (T.eigenspace (0 : ℂ)) = 49152 := by exact_mod_cast hzeroC
  constructor
  · apply top_unique
    intro v hv
    have he := LinearMap.congr_fun hsum v
    simp only [LinearMap.sum_apply, Module.End.one_apply] at he
    rw [← he]
    exact Submodule.sum_mem _ fun i _ =>
      (le_iSup (fun j : Fin 4 => T.eigenspace (eigenvalue j)) i) ((hp i).map_mem v)
  · intro i
    fin_cases i <;> simp [eigenvalue, hzero, hodd, hhalf, htwo]

private theorem restricted_eigenspace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) (t : ℂ) :
    S D ⊓ (mode D a 1 0).eigenspace t =
      ((L D hD hroot a ha).eigenspace t).map (S D).subtype :=
  (S D).inf_genEigenspace (mode D a 1 0) (invariant D hD hroot a ha)

/-- The constructed Golay Leech raw axis (4,4,0^22) has the actual ordinary
fixed-energy-two trace and complete independent four-eigenspace decomposition. -/
theorem actual_leech_peirce_multiplicities :
    ∃ (D : LatticeData) (e : Charge D ≃ₗ[ℤ] RealLeech.lattice) (a : Charge D),
      D.rank = 24 ∧ IsUnit D.G.det ∧
      (D.G.map (Int.castRingHom ℝ)).PosDef ∧
      (∀ b c : Charge D, (bilinear D b c : ℝ) =
        RealLeech.pairing (e b : RealLeech.Space) (e c : RealLeech.Space)) ∧
      (∀ b : Charge D, bilinear D b b ≠ 2) ∧
      (e a : RealLeech.Space) = RealLeech.castLinear
        (Pi.single (0 : Fin 24) 4 + Pi.single (1 : Fin 24) 4) ∧
      bilinear D a a = 4 ∧
      let U := fixedSpace D ⊓
        (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)
      (∀ v ∈ U, mode D a 1 0 v ∈ U) ∧ Module.finrank ℂ U = 98580 ∧
      ∃ T : Module.End ℂ U,
        (∀ v : U, (T v : Carrier D) = mode D a 1 0 (v : Carrier D)) ∧
        LinearMap.trace ℂ U T = (8215 / 2 : ℂ) ∧
        iSupIndep (fun i : Fin 4 => U ⊓ (mode D a 1 0).eigenspace
          (![0, 1/16, 1/2, 2] i)) ∧
        (⨆ i : Fin 4, U ⊓ (mode D a 1 0).eigenspace
          (![0, 1/16, 1/2, 2] i)) = U ∧
        (fun i : Fin 4 => Module.finrank ℂ ↥(U ⊓ (mode D a 1 0).eigenspace
          (![0, 1/16, 1/2, 2] i))) = ![49152, 47104, 2323, 1] := by
  obtain ⟨D, e, hrank, hunit, hpos, hpair, hroot, s, hs, hfinite, hcard, _⟩ :=
    LeechLowSpectrum.actual_leech_low_spectrum
  let a : NormFour D := s.symm axisPoint
  letI : Finite (NormFour D) := hfinite
  letI : Fintype (NormFour D) := Fintype.ofFinite _
  letI : Finite (NormFourOrbit D) := normFourOrbit_finite D hpos
  letI : FiniteDimensional ℂ (S D) :=
    (actualFixedEnergyTwoBasis D hpos hroot).finiteDimensional_of_finite
  let T := L D hpos hroot a.1 a.2
  have hdim : Module.finrank ℂ (S D) = 98580 := by
    have h := (actual_theta_fixed_rootless_low_spectrum D hpos hroot).2.2
    calc
      _ = Nat.choose (D.rank + 1) 2 + Nat.card (NormFour D) / 2 := h
      _ = 98580 := by rw [hcard, hrank]; norm_num [Nat.choose]
  have htrace : LinearMap.trace ℂ (S D) T = (8215 / 2 : ℂ) := by
    change LinearMap.trace ℂ (S D) (L D hpos hroot a.1 a.2) = _
    rw [full_basis_trace]
    change (D.rank + 1 : ℂ) / 2 +
      (∑ b : NormFour D, (bilinear D (s.symm axisPoint).1 b.1 : ℂ)^2) / 32 = _
    rw [actual_axis_square_sum D hpos hroot e hpair s hs, hrank]
    norm_num
  have hinter (t : ℂ) : S D ⊓ (mode D a.1 1 0).eigenspace t =
      (T.eigenspace t).map (S D).subtype := restricted_eigenspace D hpos hroot a.1 a.2 t
  have hfin (t : ℂ) : Module.finrank ℂ ↥(S D ⊓ (mode D a.1 1 0).eigenspace t) =
      Module.finrank ℂ (T.eigenspace t) := by
    rw [hinter, Submodule.finrank_map_subtype_eq]
  have hodd : Module.finrank ℂ (T.eigenspace (1 / 16 : ℂ)) = 47104 := by
    rw [← hfin, LeechPeirceDimension.actual_one_sixteenth_finrank D hpos hroot a.1 a.2,
      Nat.card_congr (axisFiberEquiv D e hpair s hs)]
    have hc := (LeechAxisDistribution.axis_distribution 0 1 (by decide +kernel) 1).2
    convert hc using 1 <;> norm_num
  have htwo : Module.finrank ℂ (T.eigenspace (2 : ℂ)) = 1 := by
    rw [← hfin, (NormFourTwoEigenline.actual_fixed_energy_two_eigenline
      D hpos hroot a.1 a.2 1 (by norm_num)).2]
    exact finrank_span_singleton
      (NormFourTwoEigenline.actual_fixed_energy_two_eigenline D hpos hroot a.1 a.2 1 (by norm_num)).1
  have hq : T * (T - (1 / 16 : ℂ) • 1) * (T - (1 / 2 : ℂ) • 1) *
      (T - (2 : ℂ) • 1) = 0 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have h := NormFourFixedPeirce.actual_fixed_energy_two_peirce
      D hpos hroot a.1 a.2 1 (by norm_num) v
    simpa only [T, L, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, LinearMap.zero_apply, LinearMap.restrict_apply,
      Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_zero] using h
  obtain ⟨hsup, hdims⟩ := spectral_dimensions T hq hdim htrace hodd htwo
  refine ⟨D, e, a.1, hrank, hunit, hpos, hpair, hroot, ?_, a.2,
    invariant D hpos hroot a.1 a.2, hdim, T, (fun _ => rfl), htrace, ?_, ?_, ?_⟩
  · rw [← hs a]
    change RealLeech.castLinear (s (s.symm axisPoint)).1 = _
    rw [s.apply_symm_apply, axisPoint_raw]
  · have hinj : Function.Injective eigenvalue := by
      intro i j h
      fin_cases i <;> fin_cases j <;> norm_num [eigenvalue] at h <;> rfl
    exact ((mode D a.1 1 0).eigenspaces_iSupIndep.comp hinj).mono fun _ => inf_le_right
  · change (⨆ i : Fin 4, S D ⊓ (mode D a.1 1 0).eigenspace (eigenvalue i)) = S D
    simp_rw [hinter]
    rw [← Submodule.map_iSup, hsup, Submodule.map_top, Submodule.range_subtype]
  · funext i
    rw [hfin]
    exact hdims i

#print axioms actual_leech_peirce_multiplicities

end D5.S3.VertexAlgebra.Lattice.LeechPeirceMultiplicities
