/- GID: D5/S3/VertexAlgebra/Sewing/CanonicalOccupation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sewing/CanonicalOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal canonical occupation coefficients for scalar lattice sewing. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
import D5.S3.VertexAlgebra.FactorialFockMetric
import D5.S3.VertexAlgebra.LatticePositiveEnergy
import D5.S3.VertexAlgebra.LatticeActualAnnihilation
import D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.CanonicalOccupationSewing

open LatticeGeneratingFieldLocality LatticeSectorIntertwiner
open ActualSeriesDerivation MvPolynomial
open scoped BigOperators

noncomputable section

abbrev Occ (D : LatticeData) := Index D →₀ ℕ

def level (D : LatticeData) (d : Occ D) : ℕ :=
  LatticePositiveEnergy.oscillatorEnergy d

def b (D : LatticeData) (d : Occ D) : Oscillator D :=
  MvPolynomial.monomial d (1 : ℂ)

/-- The factorial coordinate-resolution form; no invariant BPZ property is asserted. -/
def H (D : LatticeData) (p t : Oscillator D) : ℂ :=
  FactorialFockMetric.inner p t

def A (D : LatticeData) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (d : Occ D) : ℂ :=
  H D p (canonical D α (β + γ) u (r + (level D d : ℤ)) (b D d)) *
    (H D (b D d) (canonical D β γ v (s - (level D d : ℤ)) w) /
      (FactorialFockMetric.weight d : ℂ))

def sewnTerm (D : LatticeData) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (q : ℂ) (d : Occ D) : ℂ :=
  q ^ level D d * A D α β γ u v w p r s d

/-- The original exponential's factorial-free occupation numerator. -/
def creationCoordinate (D : LatticeData) (α : Charge D) (d : Occ D) : ℂ :=
  d.prod fun x n => ((α x.1 : ℂ) / (x.2 + 1 : ℂ)) ^ n

private theorem creation_partial (D : LatticeData) (α : Charge D) (x : Index D)
    (t : ℤ) :
    pderiv x (creationCoeff D α t) =
      ((α x.1 : ℂ) / (x.2 + 1 : ℂ)) •
        creationCoeff D α (t - (x.2 + 1 : ℕ)) := by
  classical
  have hlin (n : ℕ) :
      pderiv x (∑ j : Fin D.rank, (α j : ℂ) • (X (j,n) : Oscillator D)) =
        if x.2 = n then (α x.1 : ℂ) • (1 : Oscillator D) else 0 := by
    rcases x with ⟨i,k⟩
    simp [map_sum, map_smul, pderiv_X, Prod.mk.injEq, eq_comm]
  have hlog : seriesDerivation D (pderiv x) (creationSeries D α) =
      PowerSeries.C (((α x.1 : ℂ) / (x.2 + 1 : ℂ)) • (1 : Oscillator D)) *
        PowerSeries.X ^ (x.2 + 1) := by
    apply PowerSeries.ext
    intro n
    rw [series_coeff]
    cases n with
    | zero => simp [creationSeries]
    | succ n =>
      simp only [creationSeries, PowerSeries.coeff_mk,
        dif_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
        map_smul, hlin, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      by_cases hx : x.2 = n
      · rw [if_pos hx]
        simp [hx, div_eq_mul_inv, smul_smul, mul_comm]
      · rw [if_neg hx]
        simp [hx, Ne.symm hx]
  have hnat (n : ℕ) : pderiv x (PowerSeries.coeff n (creationExponential D α)) =
      if x.2 + 1 ≤ n then
        ((α x.1 : ℂ) / (x.2 + 1 : ℂ)) •
          PowerSeries.coeff (n - (x.2 + 1)) (creationExponential D α) else 0 := by
    have h := congrArg (PowerSeries.coeff n)
      (actual_exponential_derivation D (pderiv x) α)
    rw [series_coeff, hlog, ← mul_assoc, PowerSeries.coeff_mul_X_pow'] at h
    rw [h]
    split_ifs
    · rw [PowerSeries.coeff_mul_C, mul_smul_comm, mul_one]
    · rfl
  by_cases ht : t < 0
  · rw [creationCoeff, dif_pos ht, map_zero, creationCoeff,
      dif_pos (show t - (x.2 + 1 : ℕ) < 0 by omega), smul_zero]
  · rw [creationCoeff, dif_neg ht, hnat]
    by_cases hx : x.2 + 1 ≤ t.toNat
    · rw [if_pos hx, creationCoeff, dif_neg (by omega),
        show (t - (x.2 + 1 : ℕ)).toNat = t.toNat - (x.2 + 1) by omega]
    · rw [if_neg hx, creationCoeff, dif_pos (by omega), smul_zero]

/-- Exact occupation coefficient of the original creation exponential.
The factorial is supplied by the original polynomial derivations, not postulated. -/
theorem creation_coefficient_factorial (D : LatticeData) (α : Charge D)
    (d : Occ D) :
    (creationCoeff D α (level D d)).coeff d * (FactorialFockMetric.weight d : ℂ) =
      creationCoordinate D α d := by
  classical
  have hstep (e : Occ D) (x : Index D) :
      (creationCoeff D α (level D (e + Finsupp.single x 1))).coeff
          (e + Finsupp.single x 1) * (FactorialFockMetric.weight (e + Finsupp.single x 1) : ℂ) =
        ((creationCoeff D α (level D e)).coeff e * (FactorialFockMetric.weight e : ℂ)) *
          ((α x.1 : ℂ) / (x.2 + 1 : ℂ)) := by
    have hlev : level D (e + Finsupp.single x 1) = level D e + (x.2 + 1) := by
      simp [level, LatticePositiveEnergy.oscillatorEnergy, map_add, Finsupp.weight_single]
    have he := congrArg (fun p : Oscillator D => p.coeff e)
      (creation_partial D α x (level D (e + Finsupp.single x 1)))
    rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_smul] at he
    have hidx : (level D (e + Finsupp.single x 1) : ℤ) - (x.2 + 1 : ℕ) =
        (level D e : ℤ) := by rw [hlev]; omega
    rw [hidx] at he
    rw [FactorialFockMetric.weight_add_single]
    push_cast
    calc
      _ = ((creationCoeff D α (level D (e + Finsupp.single x 1))).coeff
          (e + Finsupp.single x 1) * (e x + 1 : ℂ)) *
            (FactorialFockMetric.weight e : ℂ) := by ring
      _ = _ := by rw [he]; ring
  have hprod (e : Occ D) (x : Index D) :
      creationCoordinate D α (e + Finsupp.single x 1) =
        creationCoordinate D α e * ((α x.1 : ℂ) / (x.2 + 1 : ℂ)) := by
    unfold creationCoordinate
    rw [Finsupp.prod_add_index' (by simp) (by intros; exact pow_add _ _ _)]
    simp
  have haux : ∀ n : ℕ, ∀ d : Occ D, level D d = n →
      (creationCoeff D α (level D d)).coeff d * (FactorialFockMetric.weight d : ℂ) =
        creationCoordinate D α d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hd
      by_cases hz : d = 0
      · subst d
        have hc := LatticeSugawaraConformal.exponential_constant D α
        simp [level, LatticePositiveEnergy.oscillatorEnergy, creationCoeff, hc,
          creationCoordinate, FactorialFockMetric.weight]
      · obtain ⟨x, hx⟩ : ∃ x : Index D, d x ≠ 0 := by
          by_contra h
          push_neg at h
          exact hz (Finsupp.ext h)
        let e := d - Finsupp.single x 1
        have hed : e + Finsupp.single x 1 = d :=
          Finsupp.sub_add_single_one_cancel hx
        have hlev : level D e + (x.2 + 1) = level D d := by
          rw [← hed]
          simp [level, LatticePositiveEnergy.oscillatorEnergy, map_add, Finsupp.weight_single]
        have hi := ih (level D e) (by omega) e rfl
        rw [← hed, hstep, hi, hprod]
  exact haux (level D d) d rfl

#print axioms creation_coefficient_factorial

end
end D5.S3.VertexAlgebra.CanonicalOccupationSewing
