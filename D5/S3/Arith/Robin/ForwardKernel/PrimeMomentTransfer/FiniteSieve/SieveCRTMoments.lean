/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCRTMoments
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCRTMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Chinese-remainder finite-sieve moments identify uncentred products with the truncated singular series and centralisation with inclusion–exclusion. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CentredProductExpansion
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SingularSeriesTail

open scoped BigOperators Topology
open Set Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

open D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion

private instance (y : ℕ) : NeZero (primorial y) := ⟨primorial_ne_zero y⟩

private def primorialCRT (y : ℕ) :
    ZMod (primorial y) ≃+* ((p : y.primesLE) → ZMod (p : ℕ)) := by
  have hprod : (∏ p : y.primesLE, (p : ℕ)) = primorial y :=
    Finset.prod_coe_sort y.primesLE (fun p : ℕ => p)
  have hcop : Pairwise (fun p q : y.primesLE => Nat.Coprime (p : ℕ) (q : ℕ)) := by
    intro p q hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primesLE p.property)
      (Nat.prime_of_mem_primesLE q.property)).mpr (Subtype.coe_ne_coe.mpr hpq)
  exact (ZMod.ringEquivCongr hprod.symm).trans
    (ZMod.prodEquivPi (fun p : y.primesLE => (p : ℕ)) hcop)

private lemma coprime_iff_crt_nonzero (y d : ℕ) (x : ZMod (primorial y)) :
    (x + (d : ZMod (primorial y))).val.Coprime (primorial y) ↔
      ∀ p : y.primesLE, primorialCRT y x p + (d : ZMod (p : ℕ)) ≠ 0 := by
  have hunit : (x + (d : ZMod (primorial y))).val.Coprime (primorial y) ↔
      IsUnit (x + (d : ZMod (primorial y))) := by
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.isUnit_iff_coprime (x + (d : ZMod (primorial y))).val (primorial y)).symm
  rw [hunit, ← isUnit_map_iff (primorialCRT y), Pi.isUnit_iff]
  apply forall_congr'
  intro p
  let : Fact (Nat.Prime (p : ℕ)) := ⟨Nat.prime_of_mem_primesLE p.property⟩
  simp

private lemma local_survivor_card (p : ℕ) [NeZero p] (D : Finset ℕ) :
    Fintype.card {r : ZMod p // ∀ d ∈ D, r + (d : ZMod p) ≠ 0} =
      p - localResidueCount (D.image (fun d : ℕ => (d : ℤ))) p := by
  classical
  have hmem (r : ZMod p) :
      r ∈ (localResidueSet (D.image (fun d : ℕ => (d : ℤ))) p)ᶜ ↔
        ∀ d ∈ D, r + (d : ZMod p) ≠ 0 := by
    simp [localResidueSet, Finset.image_image, add_eq_zero_iff_eq_neg, eq_comm]
  rw [Fintype.card_of_subtype _ hmem, Finset.card_compl, ZMod.card]
  rfl

private lemma crt_survivor_card (y : ℕ) (D : Finset ℕ) :
    Fintype.card {x : ZMod (primorial y) //
      ∀ d ∈ D, (x + (d : ZMod (primorial y))).val.Coprime (primorial y)} =
      ∏ p ∈ y.primesLE,
        (p - localResidueCount (D.image (fun d : ℕ => (d : ℤ))) p) := by
  classical
  let (p : y.primesLE) : NeZero (p : ℕ) :=
    ⟨(Nat.prime_of_mem_primesLE p.property).ne_zero⟩
  let e := (primorialCRT y).toEquiv.subtypeEquiv
    (p := fun x => ∀ d ∈ D, (x + (d : ZMod (primorial y))).val.Coprime (primorial y))
    (q := fun f => ∀ p : y.primesLE, ∀ d ∈ D, f p + (d : ZMod (p : ℕ)) ≠ 0)
    (by
      intro x
      simp only [coprime_iff_crt_nonzero]
      exact ⟨fun h p d hd => h d hd p, fun h d hd p => h p d hd⟩)
  calc
    _ = Fintype.card ((p : y.primesLE) →
        {r : ZMod (p : ℕ) // ∀ d ∈ D, r + (d : ZMod (p : ℕ)) ≠ 0}) :=
      Fintype.card_congr (e.trans (Equiv.subtypePiEquivPi
        (β := fun p : y.primesLE => ZMod (p : ℕ))
        (p := fun p r => ∀ d ∈ D, r + (d : ZMod (p : ℕ)) ≠ 0)))
    _ = ∏ p : y.primesLE,
        ((p : ℕ) - localResidueCount (D.image (fun d : ℕ => (d : ℤ))) p) := by
      rw [Fintype.card_pi]
      exact Finset.prod_congr rfl (fun p _ => local_survivor_card p D)
    _ = _ := Finset.prod_coe_sort y.primesLE
      (fun p : ℕ => p - localResidueCount (D.image (fun d : ℕ => (d : ℤ))) p)

private lemma finite_series_eq_survivor_density (y : ℕ) (D : Finset ℕ) :
    finiteSingularSeries y D = sieveDensity ⟨primorial y, primorial_pos y⟩ ^ D.card *
      ((Fintype.card {x : ZMod (primorial y) //
        ∀ d ∈ D, (x + (d : ZMod (primorial y))).val.Coprime (primorial y)} : ℝ) /
        (primorial y : ℝ)) := by
  classical
  rw [finiteSingularSeries, primorial_ratio_eq_denominator_product, crt_survivor_card,
    Nat.cast_prod, primorial_eq_prod_primesLE, Nat.cast_prod,
    ← Finset.prod_pow, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  let : NeZero p := ⟨(Nat.prime_of_mem_primesLE hp).ne_zero⟩
  have hcount : localResidueCount (D.image (fun d : ℕ => (d : ℤ))) p ≤ p := by
    simpa only [ZMod.card, localResidueCount] using
      (localResidueSet (D.image (fun d : ℕ => (d : ℤ))) p).card_le_univ
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).ne_zero
  have hnum : ((p - localResidueCount (D.image (fun d : ℕ => (d : ℤ))) p : ℕ) : ℝ) /
      (p : ℝ) = 1 - (localResidueCount (D.image (fun d : ℕ => (d : ℤ))) p : ℝ) / p := by
    rw [Nat.cast_sub hcount, sub_div, div_self hpR]
  rw [hnum]
  simp only [div_eq_mul_inv]
  ring

/-- CRT identifies the uncentred sieve moment with the truncated singular series. -/
private theorem uncentered_sieve_moment (y : ℕ) (D : Finset ℕ) :
    sieveExpectation ⟨primorial y, primorial_pos y⟩
      (fun x => ∏ d ∈ D, (sieveVariable ⟨primorial y, primorial_pos y⟩ d x + 1)) = finiteSingularSeries y D := by
  classical
  let Q : ℕ+ := ⟨primorial y, primorial_pos y⟩
  have hpoint (x : ZMod (Q : ℕ)) :
      (∏ d ∈ D, (sieveVariable Q d x + 1)) = sieveDensity Q ^ D.card *
        (if ∀ d ∈ D, (x + (d : ZMod (Q : ℕ))).val.Coprime (Q : ℕ) then 1 else 0) := by
    simp only [sieveVariable, sub_add_cancel, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_boole]
  change (∑ x : ZMod (Q : ℕ), ∏ d ∈ D, (sieveVariable Q d x + 1)) / (Q : ℝ) = _
  simp_rw [hpoint]
  rw [← Finset.mul_sum, Finset.sum_boole, ← Fintype.card_subtype, mul_div_assoc]
  exact (finite_series_eq_survivor_density y D).symm

/-- The centred sieve moment is the inclusion–exclusion transform of the finite series. -/
theorem centered_sieve_moment (y : ℕ) (D : Finset ℕ) :
    sieveExpectation ⟨primorial y, primorial_pos y⟩
        (fun x => ∏ d ∈ D, sieveVariable ⟨primorial y, primorial_pos y⟩ d x) = center (finiteSingularSeries y) D := by
  classical
  let Q : ℕ+ := ⟨primorial y, primorial_pos y⟩
  unfold center centerFinite
  have hpoint :
      (fun x : ZMod (Q : ℕ) => ∏ d ∈ D, sieveVariable Q d x) =
        (fun x => ∑ J ∈ D.powerset, (-1 : ℝ) ^ (D.card - J.card) *
          ∏ d ∈ J, (sieveVariable Q d x + 1)) := by
    funext x
    simpa only [add_sub_cancel_right] using
      (prod_sub_one_expansion D (fun d => sieveVariable Q d x + 1))
  change sieveExpectation Q (fun x => ∏ d ∈ D, sieveVariable Q d x) = _
  rw [hpoint]
  have hsum :
      (fun x => ∑ J ∈ D.powerset, (-1 : ℝ) ^ (D.card - J.card) *
        ∏ d ∈ J, (sieveVariable Q d x + 1)) =
      (∑ J ∈ D.powerset, (-1 : ℝ) ^ (D.card - J.card) •
        (fun x => ∏ d ∈ J, (sieveVariable Q d x + 1))) := by
    funext x
    simp [Finset.sum_apply, smul_eq_mul]
  rw [hsum]
  change sieveFunctional Q
      (∑ J ∈ D.powerset, (-1 : ℝ) ^ (D.card - J.card) •
        (fun x => ∏ d ∈ J, (sieveVariable Q d x + 1))) = _
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro J hJ
  have hJ' : sieveFunctional Q (fun x => ∏ d ∈ J, (sieveVariable Q d x + 1)) = finiteSingularSeries y J := by
    change sieveExpectation Q (fun x => ∏ d ∈ J, (sieveVariable Q d x + 1)) = _
    simpa [Q] using uncentered_sieve_moment y J
  rw [hJ']
  simp [smul_eq_mul]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
