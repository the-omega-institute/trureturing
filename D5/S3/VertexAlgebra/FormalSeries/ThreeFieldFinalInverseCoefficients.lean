/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalInverseCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalInverseCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite coefficients of the three actual native inverse-binomial factors. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalCone
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution

/-! proof_shape: content
admission_basis: escape-witness
escape_witness: finite_inverse_box reindexes the finite coefficient convolution
with both cumulative guards before comparison with the admissible Laurent fiber.
The binomial-series suppliers are Scott Carnahan's Mathlib results.
All sums below are finite coefficient fibers. No exchange of infinite sums,
finite-support premise on P, or new raw Laurent candidate is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldFinalInverseCoefficients
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open ThreeFieldFinalLaurentFiber ThreeFieldFinalCone
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R] [Algebra ℂ R]

private theorem index_ext (d : Fin 3 →₀ ℕ) : d = index3 (d 0) (d 1) (d 2) := by
  ext i
  fin_cases i <;> simp [index3]

private theorem binomial_coeff (z : ℤ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.binomialSeries R z) =
      integerBinomial z n • (1 : R) := by
  simp [PowerSeries.binomialSeries_coeff, integerBinomial, Int.cast_smul_eq_zsmul]

private def xKernel (z : ℤ) : MvPowerSeries (Fin 3) R :=
  PowerSeries.subst (MvPowerSeries.X 0) (PowerSeries.binomialSeries R z)

private def yKernel (z : ℤ) : MvPowerSeries (Fin 3) R :=
  PowerSeries.subst (MvPowerSeries.X 1) (PowerSeries.binomialSeries R z)

private def middleKernel (z : ℤ) : MvPowerSeries (Fin 3) R :=
  PowerSeries.subst (MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1)
    (PowerSeries.binomialSeries R z)

private theorem middle_legal : PowerSeries.HasSubst
    (MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1 :
      MvPowerSeries (Fin 3) R) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  simp

private theorem x_coeff (z : ℤ) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (xKernel (R := R) z) =
      if s = 0 then if t = 0 then integerBinomial z r • (1 : R) else 0 else 0 := by
  classical
  rw [xKernel, PowerSeries.coeff_subst_single]
  have h : index3 r s t = Finsupp.single 0 ((index3 r s t) 0) ↔ s = 0 ∧ t = 0 := by
    constructor
    · intro h
      have h1 := congrArg (fun d : Fin 3 →₀ ℕ => d 1) h
      have h2 := congrArg (fun d : Fin 3 →₀ ℕ => d 2) h
      simpa [index3] using And.intro h1 h2
    · rintro ⟨rfl, rfl⟩
      simp [index3]
  simp only [h]
  by_cases hs : s = 0 <;> by_cases ht : t = 0 <;>
    simp [hs, ht, index3, binomial_coeff, integerBinomial, Algebra.smul_def]

private theorem y_coeff (z : ℤ) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (yKernel (R := R) z) =
      if r = 0 then if t = 0 then integerBinomial z s • (1 : R) else 0 else 0 := by
  classical
  rw [yKernel, PowerSeries.coeff_subst_single]
  have h : index3 r s t = Finsupp.single 1 ((index3 r s t) 1) ↔ r = 0 ∧ t = 0 := by
    constructor
    · intro h
      have h0 := congrArg (fun d : Fin 3 →₀ ℕ => d 0) h
      have h2 := congrArg (fun d : Fin 3 →₀ ℕ => d 2) h
      simpa [index3] using And.intro h0 h2
    · rintro ⟨rfl, rfl⟩
      simp [index3]
  simp only [h]
  by_cases hr : r = 0 <;> by_cases ht : t = 0 <;>
    simp [hr, ht, index3, binomial_coeff, integerBinomial, Algebra.smul_def]

private theorem one_add_X_coeff (q r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t)
      ((1 + MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) ^ q) =
      if s = 0 then if t = 0 then (q.choose r : R) else 0 else 0 := by
  have nat_subst :
      (1 + MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) ^ q = xKernel (q : ℤ) := by
    rw [xKernel, ← PowerSeries.coe_substAlgHom (R := R) (PowerSeries.HasSubst.X 0),
      PowerSeries.binomialSeries_nat, map_pow, map_add, map_one,
      PowerSeries.substAlgHom_X]
  rw [nat_subst, x_coeff]
  simp [integerBinomial, Ring.choose_natCast, Algebra.smul_def]

/-- The middle monomial calculation is valid for every q and every native
index, including h>q, nonzero spectator degree, and wrong Y degree. -/
private theorem middle_pow_coeff (q r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t)
      ((MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        MvPowerSeries (Fin 3) R) ^ q) =
      if s = q then if t = 0 then (q.choose r : R) else 0 else 0 := by
  classical
  have factor :
      (MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        MvPowerSeries (Fin 3) R) = (1 + MvPowerSeries.X 0) * MvPowerSeries.X 1 := by ring
  rw [factor, mul_pow, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_mul_monomial]
  have le_iff : Finsupp.single 1 q ≤ index3 r s t ↔ q ≤ s := by
    constructor
    · intro h
      simpa [index3] using h 1
    · intro h i
      fin_cases i <;> simp [index3, h]
  have sub : index3 r s t - Finsupp.single 1 q = index3 r (s - q) t := by
    ext i
    fin_cases i <;> simp [index3, Finsupp.tsub_apply]
  by_cases hqs : q ≤ s
  · rw [if_pos (le_iff.mpr hqs), sub, one_add_X_coeff, mul_one]
    have eq : s - q = 0 ↔ s = q := by omega
    simp only [eq]
  · have hsq : s ≠ q := by omega
    rw [if_neg (fun h => hqs (le_iff.mp h))]
    simp [hsq]

/-- A SINGLE relevant power survives in the substitution coefficient.
This is the finite-fiber justification, rather than an infinite interchange. -/
private theorem middle_coeff (z : ℤ) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (middleKernel (R := R) z) =
      if t = 0 then (integerBinomial z s * (s.choose r : ℂ)) • (1 : R) else 0 := by
  classical
  rw [middleKernel, PowerSeries.coeff_subst middle_legal,
    finsum_eq_single _ s]
  · rw [middle_pow_coeff, if_pos rfl, binomial_coeff]
    by_cases ht : t = 0
    · simp only [if_pos ht]
      simp [Algebra.smul_def, mul_assoc]
    · simp [ht]
  · intro q hq
    rw [middle_pow_coeff, if_neg (Ne.symm hq), smul_zero]

private theorem factor_inverse (B : MvPowerSeries (Fin 3) R)
    (hB : PowerSeries.HasSubst B) (n : ℕ) :
    (1 + B) ^ n * PowerSeries.subst B (PowerSeries.binomialSeries R (-(n : ℤ))) = 1 := by
  let φ := PowerSeries.substAlgHom (R := R) hB
  have nat_image : φ (PowerSeries.binomialSeries R (n : ℤ)) = (1 + B) ^ n := by
    rw [PowerSeries.binomialSeries_nat, map_pow, map_add, map_one]
    simp only [φ, PowerSeries.substAlgHom_X]
  calc
    _ = φ (PowerSeries.binomialSeries R (n : ℤ)) *
        φ (PowerSeries.binomialSeries R (-(n : ℤ))) := by
      rw [nat_image, PowerSeries.coe_substAlgHom]
    _ = φ (PowerSeries.binomialSeries R ((n : ℤ) + -(n : ℤ))) := by
      rw [PowerSeries.binomialSeries_add, map_mul]
    _ = 1 := by simp

private theorem inverse_as_kernels (k : ℕ) (a : Fin 3 → ℕ) :
    (↑((chartUnit R k a)⁻¹) : MvPowerSeries (Fin 3) R) =
      xKernel (-(k : ℤ)) * middleKernel (-(a 0 : ℤ)) * yKernel (-(a 1 : ℤ)) := by
  let H : MvPowerSeries (Fin 3) R :=
    xKernel (-(k : ℤ)) * middleKernel (-(a 0 : ℤ)) * yKernel (-(a 1 : ℤ))
  have hx := factor_inverse (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R)
    (PowerSeries.HasSubst.X 0) k
  have hm := factor_inverse
    (MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1 :
      MvPowerSeries (Fin 3) R) middle_legal (a 0)
  have hy := factor_inverse (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R)
    (PowerSeries.HasSubst.X 1) (a 1)
  have cancel : chartUnitSeries R k a * H = 1 := by
    change (1 + MvPowerSeries.X 0) ^ k *
      (1 + MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ a 0 *
      (1 + MvPowerSeries.X 1) ^ a 1 *
      (xKernel (-(k : ℤ)) * middleKernel (-(a 0 : ℤ)) * yKernel (-(a 1 : ℤ))) = 1
    have hm' :
        (1 + MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ a 0 *
          middleKernel (R := R) (-(a 0 : ℤ)) = 1 := by
      simpa only [middleKernel, add_assoc] using hm
    calc
      _ =
        ((1 + MvPowerSeries.X 0) ^ k * xKernel (R := R) (-(k : ℤ))) *
        ((1 + MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ a 0 *
          middleKernel (R := R) (-(a 0 : ℤ))) *
        ((1 + MvPowerSeries.X 1) ^ a 1 * yKernel (R := R) (-(a 1 : ℤ))) := by ring
      _ = 1 := by
        rw [show (1 + MvPowerSeries.X 0) ^ k * xKernel (R := R) (-(k : ℤ)) = 1 from hx,
          hm', show (1 + MvPowerSeries.X 1) ^ a 1 * yKernel (R := R) (-(a 1 : ℤ)) = 1 from hy]
        simp
  have invval :
      (↑((chartUnit R k a)⁻¹) : MvPowerSeries (Fin 3) R) * chartUnitSeries R k a = 1 :=
    (chartUnit R k a).inv_val
  calc
    _ = (↑((chartUnit R k a)⁻¹) : MvPowerSeries (Fin 3) R) *
        (chartUnitSeries R k a * H) := by rw [cancel, mul_one]
    _ = H := by rw [← mul_assoc, invval, one_mul]

/-- Exact finite antidiagonal parametrization in the existing three variables. -/
private theorem coeff_mul_box (F G : MvPowerSeries (Fin 3) R) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (F * G) =
      ∑ u ∈ Finset.range (r + 1), ∑ v ∈ Finset.range (s + 1),
        ∑ w ∈ Finset.range (t + 1),
          MvPowerSeries.coeff (index3 u v w) F *
            MvPowerSeries.coeff (index3 (r - u) (s - v) (t - w)) G := by
  classical
  rw [MvPowerSeries.coeff_mul]
  symm
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_bij
    (fun p _ => (index3 p.1.1 p.1.2 p.2,
      index3 (r - p.1.1) (s - p.1.2) (t - p.2))) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    apply Finset.HasAntidiagonal.mem_antidiagonal.mpr
    ext i
    fin_cases i <;> simp [index3] <;> omega
  · intro p hp q hq eq
    have h0 := congrArg (fun x : (Fin 3 →₀ ℕ) × (Fin 3 →₀ ℕ) => x.1 0) eq
    have h1 := congrArg (fun x : (Fin 3 →₀ ℕ) × (Fin 3 →₀ ℕ) => x.1 1) eq
    have h2 := congrArg (fun x : (Fin 3 →₀ ℕ) × (Fin 3 →₀ ℕ) => x.1 2) eq
    simp only [index3, Finsupp.add_apply, Finsupp.single_apply] at h0 h1 h2
    norm_num at h0 h1 h2
    exact Prod.ext (Prod.ext h0 h1) h2
  · intro p hp
    have eq := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have h0 := congrArg (fun d : Fin 3 →₀ ℕ => d 0) eq
    have h1 := congrArg (fun d : Fin 3 →₀ ℕ => d 1) eq
    have h2 := congrArg (fun d : Fin 3 →₀ ℕ => d 2) eq
    simp only [Finsupp.add_apply, index3, Finsupp.single_apply] at h0 h1 h2
    norm_num at h0 h1 h2
    refine ⟨((p.1 0, p.1 1), p.1 2), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      omega
    · apply Prod.ext
      · exact (index_ext p.1).symm
      · ext i
        fin_cases i <;> simp [index3] <;> omega
  · intro p hp
    rfl

private theorem x_mul_coeff (z : ℤ) (G : MvPowerSeries (Fin 3) R) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (xKernel z * G) =
      ∑ j ∈ Finset.range (r + 1), integerBinomial z j •
        MvPowerSeries.coeff (index3 (r - j) s t) G := by
  rw [coeff_mul_box]
  simp [x_coeff, smul_mul_assoc]

private theorem y_mul_coeff (z : ℤ) (G : MvPowerSeries (Fin 3) R) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (yKernel z * G) =
      ∑ l ∈ Finset.range (s + 1), integerBinomial z l •
        MvPowerSeries.coeff (index3 r (s - l) t) G := by
  rw [coeff_mul_box]
  simp [y_coeff, smul_mul_assoc]

private theorem middle_mul_coeff (z : ℤ) (G : MvPowerSeries (Fin 3) R) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (middleKernel z * G) =
      ∑ q ∈ Finset.range (s + 1), ∑ h ∈ Finset.range (r + 1),
        (integerBinomial z q * (q.choose h : ℂ)) •
          MvPowerSeries.coeff (index3 (r - h) (s - q) t) G := by
  rw [coeff_mul_box]
  simp only [middle_coeff]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
    Nat.zero_lt_succ, if_true, Nat.sub_zero, smul_mul_assoc, one_mul]
  rw [Finset.sum_comm]

private def coefficientBox (r s : ℕ) : Finset LaurentIndex :=
  ((Finset.range (r + 1)).product (Finset.range (s + 1))).product
    ((Finset.range (r + 1)).product (Finset.range (s + 1)))

private theorem finite_inverse_box (P : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t)
      ((↑((chartUnit R k a)⁻¹) : MvPowerSeries (Fin 3) R) * nativeChart P) =
      ∑ i ∈ coefficientBox r s,
        if i.1.1 + i.2.1 ≤ r ∧ i.1.2 + i.2.2 ≤ s then
          laurentWeight k a i • MvPowerSeries.coeff
            (index3 (r - i.1.1 - i.2.1) (s - i.1.2 - i.2.2) t) (nativeChart P)
        else 0 := by
  classical
  rw [inverse_as_kernels, mul_assoc, mul_assoc, x_mul_coeff]
  simp_rw [middle_mul_coeff, y_mul_coeff, Finset.smul_sum, smul_smul]
  simp only [coefficientBox, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := by simpa using Finset.mem_range.mp hj
  apply Finset.sum_congr rfl
  intro q hq
  have hqs : q ≤ s := by simpa using Finset.mem_range.mp hq
  let f (h l : ℕ) : R := laurentWeight k a ((j, q), (h, l)) •
    MvPowerSeries.coeff (index3 (r - j - h) (s - q - l) t) (nativeChart P)
  simp only [← mul_assoc]
  change (∑ h ∈ Finset.range (r - j + 1), ∑ l ∈ Finset.range (s - q + 1), f h l) =
    ∑ h ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (s + 1),
      if j + h ≤ r ∧ q + l ≤ s then f h l else 0
  have inner (h : ℕ) (hh : h ≤ r - j) :
      (∑ l ∈ Finset.range (s - q + 1), f h l) =
        ∑ l ∈ Finset.range (s + 1), if j + h ≤ r ∧ q + l ≤ s then f h l else 0 := by
    calc
      _ = ∑ l ∈ Finset.range (s - q + 1),
          if j + h ≤ r ∧ q + l ≤ s then f h l else 0 := by
        apply Finset.sum_congr rfl
        intro l hl
        have hls : l ≤ s - q := by simpa using Finset.mem_range.mp hl
        rw [if_pos (by constructor <;> omega)]
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro l hl hout
        have hn : ¬ (j + h ≤ r ∧ q + l ≤ s) := by
          simp only [Finset.mem_range, not_lt] at hout
          omega
        rw [if_neg hn]
  calc
    _ = ∑ h ∈ Finset.range (r - j + 1), ∑ l ∈ Finset.range (s + 1),
        if j + h ≤ r ∧ q + l ≤ s then f h l else 0 := by
      apply Finset.sum_congr rfl
      intro h hh
      exact inner h (by simpa using Finset.mem_range.mp hh)
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro h hh hout
      have hn : r - j < h := by
        simp only [Finset.mem_range, not_lt] at hout
        omega
      apply Finset.sum_eq_zero
      intro l hl
      rw [if_neg (by omega)]

/-- Every native coefficient of the ACTUAL chartUnit inverse equals the
EXISTING old j/q/h/l fiber expression. Native indices need not be sorted. -/
theorem inverse_coefficients (P : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) (n : Fin 3 → ℕ) :
    MvPowerSeries.coeff (index3 (n 0) (n 1) (n 2))
      ((↑((chartUnit R k a)⁻¹) : MvPowerSeries (Fin 3) R) * nativeChart P) =
      laurentCoefficient P k a (decode k a n) := by
  classical
  rw [finite_inverse_box, old_coefficient_chart_sum]
  have e0 : decode k a n 0 + k = (n 0 : ℤ) := by simp [decode]
  have e01 : decode k a n 0 + decode k a n 1 + 3 * k = (n 1 : ℤ) := by
    simp only [decode, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have fiber : laurentFiber k a (decode k a n) =
      (coefficientBox (n 0) (n 1)).filter (LaurentAdmissible k a (decode k a n)) := by
    simp only [laurentFiber, e0, e01, Int.toNat_natCast, coefficientBox]
  rw [fiber, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases balances : i.1.1 + i.2.1 ≤ n 0 ∧ i.1.2 + i.2.2 ≤ n 1
  · rw [if_pos balances]
    by_cases admissible : LaurentAdmissible k a (decode k a n) i
    · rw [if_pos admissible]
    · rw [if_neg admissible]
      by_cases hsplit : i.2.1 ≤ i.1.2
      · have unsorted : ¬ (n 0 - i.1.1 - i.2.1 ≤ n 1 - i.1.2 - i.2.2 ∧
            n 1 - i.1.2 - i.2.2 ≤ n 2) := by
          intro sorted
          apply admissible
          refine ⟨hsplit, ?_⟩
          intro c
          fin_cases c <;> dsimp [laurentInput, decode] <;> omega
        have zero : MvPowerSeries.coeff
            (index3 (n 0 - i.1.1 - i.2.1) (n 1 - i.1.2 - i.2.2) (n 2))
            (nativeChart P) = 0 := by
          simpa [MvPowerSeries.coeff_apply, nativeChart, index3] using
            (if_neg unsorted :
              (if n 0 - i.1.1 - i.2.1 ≤ n 1 - i.1.2 - i.2.2 ∧
                  n 1 - i.1.2 - i.2.2 ≤ n 2 then
                MvPowerSeries.coeff (index3 (n 0 - i.1.1 - i.2.1)
                  ((n 1 - i.1.2 - i.2.2) - (n 0 - i.1.1 - i.2.1))
                  (n 2 - (n 1 - i.1.2 - i.2.2))) P else 0) = 0)
        rw [zero, smul_zero]
      · have hzero : i.1.2.choose i.2.1 = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [laurentWeight, hzero]
  · rw [if_neg balances]
    have inadmissible : ¬ LaurentAdmissible k a (decode k a n) i := by
      intro ha
      have hb := laurent_bounds k a (decode k a n) i ha
      rw [e0, e01] at hb
      omega
    rw [if_neg inadmissible]

end
end D5.S3.VertexAlgebra.ThreeFieldFinalInverseCoefficients
