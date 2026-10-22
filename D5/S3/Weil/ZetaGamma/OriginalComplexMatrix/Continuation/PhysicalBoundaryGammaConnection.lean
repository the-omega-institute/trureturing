/- GID: D5/S3/Weil/ZetaGamma/OriginalComplexMatrix/Continuation/PhysicalBoundaryGammaConnection
   Source-only repair candidate. No native elaboration or axiom certificate.
   Literal dx/Ioc carrier, arbitrary complex profiles and all signed modes. -/
import D5.S3.Weil.ZetaGamma.FormCore.LatticeBoundary
import D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
import D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain
import D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
import D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation.OriginalComplexGammaFinalAssembly

noncomputable section
open MeasureTheory Set Filter AddCircle
open scoped ComplexConjugate ENNReal Topology BigOperators
open D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
open D5.S3.Weil.ZetaGamma.FormCore
open D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
open D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy
open D5.S3.Weil.ZetaGamma.FormCore.Corner

namespace D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation

/-- Finite polynomial in the literal normalized signed modes. -/
def physicalPolynomial (L : ℝ) (v : ℤ → ℂ) (S : Finset ℤ) : ℝ → ℂ :=
  fun x => ∑ n ∈ S, v n * mode L n x

lemma physicalPolynomial_continuous (L : ℝ) (v : ℤ → ℂ) (S : Finset ℤ) :
    Continuous (physicalPolynomial L v S) := by
  unfold physicalPolynomial
  exact continuous_finset_sum _ fun n _ =>
    continuous_const.mul (mode_continuous L n)

lemma physicalPolynomial_memLp (L : ℝ) (hL : 0 < L)
    (v : ℤ → ℂ) (S : Finset ℤ) :
    MemLp (physicalPolynomial L v S) 2 (windowMeasure L (-L / 2)) :=
  continuous_memLp_window L (physicalPolynomial_continuous L v S)

lemma physicalPolynomial_physicalCoeff (L : ℝ) [Fact (0 < L)] (hL : 0 < L)
    (v : ℤ → ℂ) (S : Finset ℤ) (k : ℤ) :
    physicalCoeff (AddCircle.liftIoc L (-L / 2) (physicalPolynomial L v S)) k =
      if k ∈ S then v k else 0 := by
  classical
  let f : AddCircle L → ℂ := AddCircle.liftIoc L (-L / 2)
    (physicalPolynomial L v S)
  have hfinite : f = fun c =>
      ∑ n ∈ S, (v n * (Real.sqrt L : ℂ)⁻¹) * _root_.fourier n c := by
    funext c
    change (∑ n ∈ S, v n * mode L n (AddCircle.equivIoc L (-L / 2) c)) = _
    apply Finset.sum_congr rfl
    intro n hn
    rw [mode_fourier, AddCircle.coe_equivIoc]
    ring
  have hcoeff : fourierCoeff f k =
      if k ∈ S then v k * (Real.sqrt L : ℂ)⁻¹ else 0 := by
    rw [hfinite]
    have hfun : (fun c : AddCircle L =>
        ∑ n ∈ S, (v n * (Real.sqrt L : ℂ)⁻¹) * _root_.fourier n c) =
        ∑ n ∈ S, (fun c => (v n * (Real.sqrt L : ℂ)⁻¹) * _root_.fourier n c) := by
      ext c
      simp only [Finset.sum_apply]
    rw [hfun, fourierCoeff.sum S _ (fun n _ =>
      (((_root_.fourier n).memLp (p := 2) AddCircle.haarAddCircle ℂ).integrable
        (by norm_num)).const_mul (v n * (Real.sqrt L : ℂ)⁻¹))]
    simp only [Finset.sum_apply, fourierCoeff.const_mul, fourierCoeff_fourier,
      Pi.single_apply]
    simp [mul_ite]
  change (Real.sqrt L : ℂ) * fourierCoeff f k = _
  rw [hcoeff]
  have hs : (Real.sqrt L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'
  split_ifs <;> field_simp [hs] <;> ring

/-- Endpoint transport is a measure equality, not an equality of the sets. -/
lemma cutoffBoundaryPair_eq_actualMixed_re
    (L : ℝ) (hL : 0 < L) (u : ℝ → ℂ) :
    cutoffBoundaryPair L (-L / 2) 0 u =
      (actualIocBoundaryMixed (L / 2) 0 u u).re := by
  have hend : -L / 2 + L = L / 2 := by ring
  have hneg : -(L / 2) = -L / 2 := by ring
  have hperiod : 2 * (L / 2) = L := by ring
  have hpair : cutoffBoundaryPair L (-L / 2) 0 u =
      actualIocBoundaryPair (L / 2) 0 u := by
    simp only [cutoffBoundaryPair, actualIocBoundaryPair,
      DomainPassage.intervalMeasure, hend, hneg, hperiod, cutoffKernel,
      DomainPassage.density, Corner.actualDensity,
      apply_ite ((↑) : ℝ → ℂ), Complex.ofReal_zero]
  exact hpair.trans (actualIocBoundaryMixed_self_re (L / 2) 0 u).symm

/-- Finite quadratic expansion. Every coefficient-scaled cross term has its
own L1 proof; no integrability of a squared L1 function is used. -/
private lemma integral_norm_sq_finite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (v : ℤ → ℂ) (S : Finset ℤ) (f : ℤ → X → ℂ)
    (hf : ∀ n ∈ S, MemLp (f n) 2 μ) :
    (∫ x, ‖∑ n ∈ S, v n * f n x‖ ^ 2 ∂μ) =
      (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) *
        (∫ x, conj (f m x) * f n x ∂μ)).re := by
  classical
  let q (m n : ℤ) (x : X) :=
    (conj (v m) * v n) * (conj (f m x) * f n x)
  have hq (m : ℤ) (hm : m ∈ S) (n : ℤ) (hn : n ∈ S) :
      Integrable (q m n) μ :=
    (l2_complex_correlation_integrable (hf m hm) (hf n hn)).const_mul _
  have hrow (m : ℤ) (hm : m ∈ S) : Integrable (fun x => ∑ n ∈ S, q m n x) μ :=
    integrable_finsetSum S (hq m hm)
  have htotal : Integrable (fun x => ∑ m ∈ S, ∑ n ∈ S, q m n x) μ :=
    integrable_finsetSum S hrow
  have hcomplex (x : X) :
      conj (∑ n ∈ S, v n * f n x) * (∑ n ∈ S, v n * f n x) =
        ∑ m ∈ S, ∑ n ∈ S, q m n x := by
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [q]
    ring
  have hpoint (x : X) : ‖∑ n ∈ S, v n * f n x‖ ^ 2 =
      (∑ m ∈ S, ∑ n ∈ S, q m n x).re := by
    calc
      _ = (conj (∑ n ∈ S, v n * f n x) * (∑ n ∈ S, v n * f n x)).re := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
          Complex.normSq_eq_norm_sq]
      _ = _ := congrArg Complex.re (hcomplex x)
  simp_rw [hpoint]
  calc
    (∫ x, Complex.re (∑ m ∈ S, ∑ n ∈ S, q m n x) ∂μ) =
        (∫ x, ∑ m ∈ S, ∑ n ∈ S, q m n x ∂μ).re := integral_re htotal
    _ = (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) *
        ∫ x, conj (f m x) * f n x ∂μ).re := by
      rw [integral_finsetSum S hrow]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [integral_finsetSum S (hq m hm)]
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_const_mul _ _

/-- The second finite exchange is on the positive s measure, after each
mixed-mode integral (including its scalar coefficient) is known integrable. -/
private lemma integral_re_finite_pairs {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ℤ) (c : ℤ → ℤ → ℂ)
    (F : ℤ → ℤ → X → ℂ)
    (hF : ∀ m ∈ S, ∀ n ∈ S, Integrable (F m n) μ) :
    (∫ x, (∑ m ∈ S, ∑ n ∈ S, c m n * F m n x).re ∂μ) =
      (∑ m ∈ S, ∑ n ∈ S, c m n * ∫ x, F m n x ∂μ).re := by
  have hterm (m : ℤ) (hm : m ∈ S) (n : ℤ) (hn : n ∈ S) :=
    (hF m hm n hn).const_mul (c m n)
  have hrow (m : ℤ) (hm : m ∈ S) := integrable_finsetSum S (hterm m hm)
  calc
    (∫ x, Complex.re (∑ m ∈ S, ∑ n ∈ S, c m n * F m n x) ∂μ) =
        (∫ x, ∑ m ∈ S, ∑ n ∈ S, c m n * F m n x ∂μ).re :=
      integral_re (integrable_finsetSum S hrow)
    _ = (∑ m ∈ S, ∑ n ∈ S, c m n * ∫ x, F m n x ∂μ).re := by
      rw [integral_finsetSum S hrow]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [integral_finsetSum S (hterm m hm)]
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_const_mul _ _

/-- The actual finite matrix correction equals the physical image correction. -/
theorem finite_polynomial_boundaryEntry_eq_cutoff
    (L : ℝ) (hL : 0 < L) (v : ℤ → ℂ) (S : Finset ℤ)
    (hfinite : IntegrableOn
      (zeroEnergyDensity L (-L / 2) (physicalPolynomial L v S)) (Ioi 0)) :
    cutoffBoundaryPair L (-L / 2) 0 (physicalPolynomial L v S) =
      (boundaryQuadratic L v S).re := by
  classical
  letI : Fact (0 < L) := ⟨hL⟩
  have hp : physicalPolynomial L v S = ∑ n ∈ S, v n • mode L n := by
    ext x
    simp only [physicalPolynomial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hzeroMem (s : ℝ) (n : ℤ) :
      MemLp (zeroGapMap L (-L / 2) s (mode L n)) 2 volume := by
    have hz := zero_extension_memLp L (-L / 2) (mode L n)
      (continuous_memLp_window L (mode_continuous L n))
    exact hz.sub (hz.comp_measurePreserving (measurePreserving_sub_right volume s))
  have hperMem (s : ℝ) (n : ℤ) :
      MemLp (periodicGapMap L (-L / 2) s (mode L n)) 2
        (windowMeasure L (-L / 2)) := by
    have hn := continuous_memLp_window L (mode_continuous L n)
    exact hn.sub (periodic_shift_memLp L (-L / 2) (mode L n) hn s)
  have hzeroSlice (s : ℝ) :
      (∫ x, Complex.normSq (zeroGapMap L (-L / 2) s (physicalPolynomial L v S) x)) =
      (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) * displacementPair L m n s).re := by
    have h := integral_norm_sq_finite volume v S
      (fun n => zeroGapMap L (-L / 2) s (mode L n)) (fun n _ => hzeroMem s n)
    rw [hp]
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Complex.normSq_eq_norm_sq, zeroGapMap, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Function.comp_apply, displacementPair, zeroMode_eq] using h
  have hperSlice (s : ℝ) :
      (∫ x, Complex.normSq (periodicGapMap L (-L / 2) s (physicalPolynomial L v S) x)
        ∂windowMeasure L (-L / 2)) =
      (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) * periodicPair L m n s).re := by
    have h := integral_norm_sq_finite (windowMeasure L (-L / 2)) v S
      (fun n => periodicGapMap L (-L / 2) s (mode L n)) (fun n _ => hperMem s n)
    rw [hp]
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Complex.normSq_eq_norm_sq, periodicGapMap, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Function.comp_apply, periodicPair_eq_mode, windowMeasure,
      ← window_eq] using h
  have hzeroI (m n : ℤ) : IntegrableOn (fun s => (density s : ℂ) *
      displacementPair L m n s) (Ioi 0) := by
    simpa only [displacementPair, zeroMode_eq] using
      finite_energy_mixed_integrable L (-L / 2) (mode L m) (mode L n)
        (continuous_memLp_window L (mode_continuous L m))
        (continuous_memLp_window L (mode_continuous L n))
        (mode_actual_energy_integrable L m) (mode_actual_energy_integrable L n)
  have hzeroExpand :
      (∫ s in Ioi 0, zeroEnergyDensity L (-L / 2) (physicalPolynomial L v S) s) =
      (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) *
        (∫ s in Ioi 0, (density s : ℂ) * displacementPair L m n s)).re := by
    have hpoint (s : ℝ) :
        zeroEnergyDensity L (-L / 2) (physicalPolynomial L v S) s =
        (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) *
          ((density s : ℂ) * displacementPair L m n s)).re := by
      change density s * (∫ x, Complex.normSq
        (zeroGapMap L (-L / 2) s (physicalPolynomial L v S) x)) = _
      rw [hzeroSlice]
      rw [show density s *
          (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) * displacementPair L m n s).re =
          ((density s : ℂ) *
            (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) * displacementPair L m n s)).re by
              simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                zero_mul, sub_zero]]
      congr 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      ring
    simp_rw [hpoint]
    exact integral_re_finite_pairs _ S (fun m n => conj (v m) * v n)
      (fun m n s => (density s : ℂ) * displacementPair L m n s)
      (fun m _ n _ => hzeroI m n)
  have hperExpand :
      (∫ s in Ioi 0, periodicEnergyDensity L (-L / 2) (physicalPolynomial L v S) s) =
      (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) *
        (∫ s in Ioi 0, (density s : ℂ) * periodicPair L m n s)).re := by
    have hpoint (s : ℝ) :
        periodicEnergyDensity L (-L / 2) (physicalPolynomial L v S) s =
        (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) *
          ((density s : ℂ) * periodicPair L m n s)).re := by
      change density s * (∫ x, Complex.normSq
        (periodicGapMap L (-L / 2) s (physicalPolynomial L v S) x)
          ∂windowMeasure L (-L / 2)) = _
      rw [hperSlice]
      rw [show density s *
          (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) * periodicPair L m n s).re =
          ((density s : ℂ) *
            (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) * periodicPair L m n s)).re by
              simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                zero_mul, sub_zero]]
      congr 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      ring
    simp_rw [hpoint]
    exact integral_re_finite_pairs _ S (fun m n => conj (v m) * v n)
      (fun m n s => (density s : ℂ) * periodicPair L m n s)
      (fun m _ n _ => (periodic_mixed_integral L m n).1)
  have hu : MemLp (physicalPolynomial L v S) 2
      (volume.restrict (Ioc (-(L / 2)) (L / 2))) := by
    simpa only [windowMeasure, show -L / 2 + L = L / 2 by ring,
      show -(L / 2) = -L / 2 by ring] using physicalPolynomial_memLp L hL v S
  have hcore := actual_centered_gamma_full_domain_equivalence (L / 2) (by linarith) _ hu
  simp only [show 2 * (L / 2) = L by ring,
    show -(L / 2) = -L / 2 by ring] at hcore
  have hidentity := hcore.2 (hcore.1.mp hfinite)
  have hmatrix :
      (∫ s in Ioi 0, zeroEnergyDensity L (-L / 2) (physicalPolynomial L v S) s) =
      (∫ s in Ioi 0, periodicEnergyDensity L (-L / 2) (physicalPolynomial L v S) s) +
        (boundaryQuadratic L v S).re := by
    rw [hzeroExpand, hperExpand]
    simp_rw [full_rate_entry, (periodic_mixed_integral L _ _).2]
    simp only [mul_add, Finset.sum_add_distrib, Complex.add_re, boundaryQuadratic]
  linarith

/-- Finite high-support physical image bound, consuming the signed supplier. -/
theorem finite_polynomial_physical_boundary_lower_bound
    (L : ℝ) (hL : 0 < L) (M : ℕ) (hM : 2 ≤ M)
    (v : ℤ → ℂ) (S : Finset ℤ)
    (hv : ∀ n ∉ S, v n = 0)
    (hhigh : ∀ n ∈ S, M ≤ Int.natAbs n)
    (hfinite : IntegrableOn
      (zeroEnergyDensity L (-L / 2) (physicalPolynomial L v S)) (Ioi 0)) :
    -(Real.pi / 2 + L / (Real.pi ^ 2 * ((M : ℝ) - 1))) *
        ∑ n ∈ S, ‖v n‖ ^ 2 ≤
      cutoffBoundaryPair L (-L / 2) 0 (physicalPolynomial L v S) := by
  rw [finite_polynomial_boundaryEntry_eq_cutoff L hL v S hfinite]
  exact boundaryEntry_odd_lower_bound L hL M hM v S hv hhigh

private lemma finite_sum_re (S : Finset ℤ) (f : ℤ → ℂ) :
    (∑ n ∈ S, f n).re = ∑ n ∈ S, (f n).re := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert n S hn ih => simp only [Finset.sum_insert hn, Complex.add_re, ih]

/-- Parseval on dx, obtained from the finite cross-term expansion and the
original normalized mode_inner owner, with an explicit diagonal collapse. -/
lemma physicalPolynomial_mass_eq_sum
    (L : ℝ) (hL : 0 < L) (v : ℤ → ℂ) (S : Finset ℤ) :
    (∫ x in window L, ‖physicalPolynomial L v S x‖ ^ 2) =
      ∑ n ∈ S, ‖v n‖ ^ 2 := by
  classical
  letI : Fact (0 < L) := ⟨hL⟩
  have hm (n : ℤ) : MemLp (mode L n) 2 (volume.restrict (window L)) := by
    simpa only [windowMeasure, ← window_eq] using
      continuous_memLp_window L (mode_continuous L n)
  have h := integral_norm_sq_finite (volume.restrict (window L)) v S
    (mode L) (fun n _ => hm n)
  change (∫ x in window L, ‖∑ n ∈ S, v n * mode L n x‖ ^ 2) = _
  rw [h]
  simp_rw [mode_inner]
  have hdiag :
      (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) * (if m = n then (1 : ℂ) else 0)) =
      ∑ m ∈ S, conj (v m) * v m := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_eq_single m]
    · simp
    · intro n hn hnm
      simp [Ne.symm hnm]
    · exact fun hnot => False.elim (hnot hm)
  rw [hdiag]
  simp only [finite_sum_re, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- Every original finite truncation equals its high-support polynomial.
The finite index net is unchanged; no cofinality claim is made. -/
lemma actualFourierTruncation_eq_physicalPolynomial_filter
    (L : ℝ) [Fact (0 < L)] (hL : 0 < L) (u : ℝ → ℂ) (S : Finset ℤ)
    (M : ℕ) (c : ℤ → ℂ)
    (hc : ∀ n, c n = physicalCoeff (AddCircle.liftIoc L (-L / 2) u) n)
    (hlow : ∀ n, Int.natAbs n < M → c n = 0) :
    actualFourierTruncation L (-L / 2) u S =
      physicalPolynomial L (fun n => if n ∈ S.filter (fun n => M ≤ Int.natAbs n)
        then c n else 0) (S.filter (fun n => M ≤ Int.natAbs n)) := by
  classical
  have hs : (Real.sqrt L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'
  have hterm (n : ℤ) (x : ℝ) :
      fourierCoeff (AddCircle.liftIoc L (-L / 2) u) n *
        _root_.fourier n (x : AddCircle L) = c n * mode L n x := by
    rw [hc n, physicalCoeff, mode_fourier]
    field_simp [hs]
  funext x
  change (∑ n ∈ S, fourierCoeff (AddCircle.liftIoc L (-L / 2) u) n *
      _root_.fourier n (x : AddCircle L)) = _
  simp_rw [hterm]
  unfold physicalPolynomial
  trans ∑ n ∈ S.filter (fun n => M ≤ Int.natAbs n), c n * mode L n x
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hh : M ≤ Int.natAbs n
    · simp [hh]
    · simp [hh, hlow n (Nat.lt_of_not_ge hh)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [if_pos hn]

/-- The restricted L2 mass is the squared norm of its actual Lp class. -/
private lemma mass_eq_toLp_norm_sq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  calc
    _ = ∫ x, (inner ℂ (hf.toLp f x) (hf.toLp f x)).re ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (f x)).symm
    _ = (inner ℂ (hf.toLp f) (hf.toLp f)).re :=
      integral_re (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hf.toLp f))
    _ = _ := inner_self_eq_norm_sq (𝕜 := ℂ) _

private lemma sqrt_mass_eq_toLp_norm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (hf : MemLp f 2 μ) :
    Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ := by
  rw [mass_eq_toLp_norm_sq μ f hf, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

/-- Convergence is in L2 for the specified measure, including when it is a
restricted Ioc measure. No global integrability assertion is introduced. -/
private lemma toLp_tendsto_of_residual_mass
    {X J : Type*} [MeasurableSpace X] (μ : Measure X) (l : Filter J)
    (u : X → ℂ) (hu : MemLp u 2 μ) (T : J → X → ℂ)
    (hT : ∀ j, MemLp (T j) 2 μ)
    (hres : Tendsto (fun j => ∫ x, ‖u x - T j x‖ ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun j => (hT j).toLp (T j)) l (𝓝 (hu.toLp u)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hsmall := (Real.continuous_sqrt.tendsto 0).comp hres
  have hdist (j : J) : dist ((hT j).toLp (T j)) (hu.toLp u) =
      Real.sqrt (∫ x, ‖u x - T j x‖ ^ 2 ∂μ) := by
    rw [dist_comm, dist_eq_norm, ← hu.toLp_sub (hT j)]
    exact (sqrt_mass_eq_toLp_norm μ _ (hu.sub (hT j))).symm
  simpa only [hdist, Function.comp_def, Real.sqrt_zero] using hsmall

/-- Two-slot continuity of the literal physical image correction. -/
lemma cutoffBoundaryPair_truncation_tendsto
    (L : ℝ) (hL : 0 < L) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-L / 2) (L / 2))))
    (T : Finset ℤ → ℝ → ℂ)
    (hT : ∀ S, MemLp (T S) 2 (volume.restrict (Ioc (-L / 2) (L / 2))))
    (hres : Tendsto (fun S : Finset ℤ =>
        ∫ x in Ioc (-L / 2) (L / 2), ‖u x - T S x‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun S : Finset ℤ => cutoffBoundaryPair L (-L / 2) 0 (T S))
      atTop (𝓝 (cutoffBoundaryPair L (-L / 2) 0 u)) := by
  let μ := volume.restrict (Ioc (-L / 2) (L / 2))
  let E (f : ℝ → ℂ) := ∫ x, ‖f x‖ ^ 2 ∂μ
  let C := 2 * gammaCk * Real.pi + 2 * (L / 2) * actualCtail (L / 2)
  have hμ : Corner.intervalMeasure (L / 2) = μ := by
    rw [show Corner.intervalMeasure (L / 2) =
      volume.restrict (Ioc (-(L / 2)) (L / 2)) from restrict_Ioo_eq_restrict_Ioc]
    simp only [μ, neg_div]
  have hu' : MemLp u 2 (Corner.intervalMeasure (L / 2)) := by rw [hμ]; exact hu
  have hT' (S : Finset ℤ) : MemLp (T S) 2 (Corner.intervalMeasure (L / 2)) := by
    rw [hμ]
    exact hT S
  have hLp := toLp_tendsto_of_residual_mass μ atTop u hu T hT hres
  have hTnorm : Tendsto (fun S => Real.sqrt (E (T S))) atTop
      (𝓝 (Real.sqrt (E u))) := by
    simpa only [E, sqrt_mass_eq_toLp_norm μ _ (hT _),
      sqrt_mass_eq_toLp_norm μ _ hu] using hLp.norm
  have hsmall : Tendsto (fun S => Real.sqrt (E (fun x => u x - T S x)))
      atTop (𝓝 0) := by
    simpa only [E, Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hres
  have hbound (S : Finset ℤ) :
      ‖cutoffBoundaryPair L (-L / 2) 0 (T S) - cutoffBoundaryPair L (-L / 2) 0 u‖ ≤
        C * Real.sqrt (E (fun x => u x - T S x)) *
          (Real.sqrt (E (T S)) + Real.sqrt (E u)) := by
    have hleft := actualIocBoundaryMixed_left_sub_norm_le (L / 2) 0 (by linarith)
      (hT' S) hu' (hT' S)
    have hright := actualIocBoundaryMixed_right_sub_norm_le (L / 2) 0 (by linarith)
      hu' (hT' S) hu'
    have hswap : (fun x => ‖T S x - u x‖ ^ 2) =
        fun x => ‖u x - T S x‖ ^ 2 := by
      funext x
      rw [norm_sub_rev]
    simp only [hμ, hswap] at hleft hright
    let A := actualIocBoundaryMixed (L / 2) 0 (T S) (T S) -
      actualIocBoundaryMixed (L / 2) 0 u (T S)
    let B := actualIocBoundaryMixed (L / 2) 0 u (T S) -
      actualIocBoundaryMixed (L / 2) 0 u u
    have hsplit : cutoffBoundaryPair L (-L / 2) 0 (T S) -
        cutoffBoundaryPair L (-L / 2) 0 u = A.re + B.re := by
      rw [cutoffBoundaryPair_eq_actualMixed_re L hL,
        cutoffBoundaryPair_eq_actualMixed_re L hL]
      simp only [A, B, Complex.sub_re]
      ring
    have h1 : ‖A.re‖ ≤ ‖A‖ := by
      simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm A
    have h2 : ‖B.re‖ ≤ ‖B‖ := by
      simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm B
    rw [hsplit]
    calc
      _ ≤ ‖A‖ + ‖B‖ := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ C * Real.sqrt (E (fun x => u x - T S x)) * Real.sqrt (E (T S)) +
          C * Real.sqrt (E u) * Real.sqrt (E (fun x => u x - T S x)) :=
        add_le_add hleft hright
      _ = _ := by ring
  have hmajor : Tendsto (fun S =>
      C * Real.sqrt (E (fun x => u x - T S x)) *
        (Real.sqrt (E (T S)) + Real.sqrt (E u))) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (tendsto_const_nhds.mul hsmall).mul (hTnorm.add tendsto_const_nhds)
  have hzero : Tendsto (fun S =>
      ‖cutoffBoundaryPair L (-L / 2) 0 (T S) - cutoffBoundaryPair L (-L / 2) 0 u‖)
      atTop (𝓝 0) := squeeze_zero (fun S => norm_nonneg _) hbound hmajor
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm] using hzero

/-- Arbitrary complex finite-energy original-Ioc input, with all low physical
Fourier coefficients zero. The loss uses the real denominator M-1. -/
theorem physical_boundary_high_frequency_lower_bound
    (L : ℝ) [Fact (0 < L)] (hL : 0 < L) (M : ℕ) (hM : 2 ≤ M)
    (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-L / 2) (L / 2))))
    (henergy : IntegrableOn (zeroEnergyDensity L (-L / 2) u) (Ioi 0))
    (hlow : ∀ n : ℤ, Int.natAbs n < M →
      physicalCoeff (AddCircle.liftIoc L (-L / 2) u) n = 0) :
    -(Real.pi / 2 + L / (Real.pi ^ 2 * ((M : ℝ) - 1))) *
        (∫ x in Ioc (-L / 2) (L / 2), ‖u x‖ ^ 2) ≤
      cutoffBoundaryPair L (-L / 2) 0 u := by
  classical
  let T (S : Finset ℤ) := actualFourierTruncation L (-L / 2) u S
  have hu' : MemLp u 2 (volume.restrict (Ioc (-(L / 2)) (L / 2))) := by
    simpa only [neg_div] using hu
  have hcore := actual_fourier_truncation_form_core (L / 2) (by linarith) u hu'
  simp only [show 2 * (L / 2) = L by ring,
    show -(L / 2) = -L / 2 by ring] at hcore
  obtain ⟨hTdomain, hTconv⟩ := hcore henergy
  have hmass0 : Tendsto (fun S : Finset ℤ =>
      ∫ x in Ioc (-L / 2) (L / 2), ‖u x - T S x‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun S => integral_nonneg (fun x => sq_nonneg _)) _ hTconv
    intro S
    exact le_add_of_nonneg_right (integral_nonneg_of_ae (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      exact mul_nonneg (density_nonneg hs)
        (integral_nonneg fun x => Complex.normSq_nonneg _)))
  have hTmem (S : Finset ℤ) : MemLp (T S) 2
      (volume.restrict (Ioc (-L / 2) (L / 2))) := by
    simpa only [T, show -L / 2 + L = L / 2 by ring] using
      actualFourierTruncation_memLp (d := L) (-L / 2) u S
  have hBlim := cutoffBoundaryPair_truncation_tendsto L hL u hu T hTmem hmass0
  have hmassT : Tendsto (fun S => ∫ x in Ioc (-L / 2) (L / 2), ‖T S x‖ ^ 2)
      atTop (𝓝 (∫ x in Ioc (-L / 2) (L / 2), ‖u x‖ ^ 2)) := by
    have hLp := toLp_tendsto_of_residual_mass _ atTop u hu T hTmem hmass0
    simpa only [mass_eq_toLp_norm_sq _ _ (hTmem _),
      mass_eq_toLp_norm_sq _ _ hu] using hLp.norm.pow 2
  have hfinite (S : Finset ℤ) :
      -(Real.pi / 2 + L / (Real.pi ^ 2 * ((M : ℝ) - 1))) *
        (∫ x in Ioc (-L / 2) (L / 2), ‖T S x‖ ^ 2) ≤
        cutoffBoundaryPair L (-L / 2) 0 (T S) := by
    let H := S.filter (fun n => M ≤ Int.natAbs n)
    let c (n : ℤ) := physicalCoeff (AddCircle.liftIoc L (-L / 2) u) n
    let v (n : ℤ) := if n ∈ H then c n else 0
    have hpoly : T S = physicalPolynomial L v H :=
      actualFourierTruncation_eq_physicalPolynomial_filter L hL u S M c
        (fun n => rfl) hlow
    letI : Fact (0 < 2 * (L / 2)) := ⟨by nlinarith⟩
    have hPdom : IntegrableOn
        (zeroEnergyDensity L (-L / 2) (physicalPolynomial L v H)) (Ioi 0) := by
      rw [← hpoly]
      dsimp [T]
      have hdomain := (hTdomain S).1
      have htrunc_congr (d₁ d₂ : ℝ) [Fact (0 < d₁)] [Fact (0 < d₂)]
          (hd : d₁ = d₂) :
          actualFourierTruncation d₁ (-L / 2) u S =
            actualFourierTruncation d₂ (-L / 2) u S := by
        subst d₂
        rfl
      have htrunc : actualFourierTruncation L (-L / 2) u S =
          actualFourierTruncation (2 * (L / 2)) (-L / 2) u S := by
        exact htrunc_congr L (2 * (L / 2)) (by ring)
      rw [htrunc]
      exact hdomain
    have hv : ∀ n ∉ H, v n = 0 := by intro n hn; simp only [v, if_neg hn]
    have hhigh : ∀ n ∈ H, M ≤ Int.natAbs n := fun n hn => (Finset.mem_filter.mp hn).2
    have hbound := finite_polynomial_physical_boundary_lower_bound L hL M hM v H
      hv hhigh hPdom
    have hmass := physicalPolynomial_mass_eq_sum L hL v H
    simp only [hpoly]
    change -(Real.pi / 2 + L / (Real.pi ^ 2 * ((M : ℝ) - 1))) *
        (∫ x in window L, ‖physicalPolynomial L v H x‖ ^ 2) ≤ _
    rw [hmass]
    exact hbound
  exact le_of_tendsto_of_tendsto'
    (tendsto_const_nhds.mul hmassT) hBlim hfinite

/-- A nontrivial spectral consumer: the entire signed high-frequency spectral
term is retained. Finiteness is derived before passing from ENNReal to real.
This does not discard the periodic spectrum to obtain a negative bound on an
already nonnegative jump energy. -/
private theorem zeroExtension_jump_spectral_lower_bound
    (L : ℝ) [Fact (0 < L)] (hL : 0 < L) (M : ℕ) (hM : 2 ≤ M)
    (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-L / 2) (L / 2))))
    (henergy : IntegrableOn (zeroEnergyDensity L (-L / 2) u) (Ioi 0))
    (hlow : ∀ n : ℤ, Int.natAbs n < M →
      physicalCoeff (AddCircle.liftIoc L (-L / 2) u) n = 0) :
    Summable (fun n : ℤ => gammaIncrement (angularFrequency (d := L) n) *
      ‖physicalCoeff (AddCircle.liftIoc L (-L / 2) u) n‖ ^ 2) ∧
    (∑' n : ℤ, gammaIncrement (angularFrequency (d := L) n) *
      ‖physicalCoeff (AddCircle.liftIoc L (-L / 2) u) n‖ ^ 2) -
      (Real.pi / 2 + L / (Real.pi ^ 2 * ((M : ℝ) - 1))) *
        (∫ x in Ioc (-L / 2) (L / 2), ‖u x‖ ^ 2) ≤
      ∫ s in Ioi 0, zeroEnergyDensity L (-L / 2) u s := by
  have hu' : MemLp u 2 (volume.restrict (Ioc (-(L / 2)) (L / 2))) := by
    simpa only [neg_div] using hu
  have hcore := actual_centered_gamma_full_domain_equivalence (L / 2) (by linarith) u hu'
  simp only [show 2 * (L / 2) = L by ring,
    show -(L / 2) = -L / 2 by ring] at hcore
  have hperiodic := hcore.1.mp henergy
  have hperiodic' : IntegrableOn (periodicEnergyDensity L (-L / 2) u) (Ioi 0) := by
    letI : Fact (0 < 2 * (L / 2)) := ⟨by nlinarith⟩
    have hper := hperiodic
    have hper_congr (d₁ d₂ : ℝ) [Fact (0 < d₁)] [Fact (0 < d₂)]
        (hd : d₁ = d₂) :
        periodicEnergyDensity d₁ (-L / 2) u =
          periodicEnergyDensity d₂ (-L / 2) u := by
      subst d₂
      rfl
    have hperfun : periodicEnergyDensity (2 * (L / 2)) (-L / 2) u =
        periodicEnergyDensity L (-L / 2) u :=
      hper_congr (2 * (L / 2)) L (by ring)
    rw [hperfun] at hper
    exact hper
  have hidentity := hcore.2 hperiodic
  have huWindow : MemLp u 2 (volume.restrict (Ioc (-L / 2) (-L / 2 + L))) := by
    simpa only [show -L / 2 + L = L / 2 by ring] using hu
  let w (n : ℤ) := gammaIncrement (angularFrequency (d := L) n) *
    ‖physicalCoeff (AddCircle.liftIoc L (-L / 2) u) n‖ ^ 2
  have hw (n : ℤ) : 0 ≤ w n := mul_nonneg
    (ArchimedeanJumpDecomposition.digamma_increment_nonnegative _) (sq_nonneg _)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      periodicEnergyDensity L (-L / 2) u := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (density_nonneg hs) (integral_nonneg fun x => Complex.normSq_nonneg _)
  have he : ENNReal.ofReal (∫ s in Ioi 0, periodicEnergyDensity L (-L / 2) u s) =
      ∑' n : ℤ, ENNReal.ofReal (w n) := by
    rw [ofReal_integral_eq_lintegral_ofReal hperiodic' hnn,
      periodic_energy_eq_weighted_sum (-L / 2) u huWindow]
    apply tsum_congr
    intro n
    exact (ENNReal.ofReal_mul
      (ArchimedeanJumpDecomposition.digamma_increment_nonnegative _)).symm
  have hfiniteSum : (∑' n : ℤ, ENNReal.ofReal (w n)) ≠ ∞ := by
    rw [← he]
    exact ENNReal.ofReal_ne_top
  have hsum : Summable w := by
    simpa only [ENNReal.toReal_ofReal (hw _)] using ENNReal.summable_toReal hfiniteSum
  have hper : (∫ s in Ioi 0, periodicEnergyDensity L (-L / 2) u s) = ∑' n, w n := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hw hsum] at he
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hnn)
      (tsum_nonneg hw)).mp he
  have hboundary := physical_boundary_high_frequency_lower_bound L hL M hM u hu
    henergy hlow
  refine ⟨hsum, ?_⟩
  rw [hper] at hidentity
  linarith

/-- Original mu-Gamma high-frequency consumer, on the whole arbitrary-complex
finite-energy Ioc domain. The signed constant is kept, and the spectral term is
not dropped. The reused finite_plus_quadratics_of_memLp owner proves BOTH the
mass and increment identities with exactly 1/(2*pi), before mu_quadratic_of_memLp
combines them using delta_eq_mu. No desired identity is an input hypothesis. -/
theorem actual_zeroExtension_gamma_high_frequency_lower_bound
    (L : ℝ) [Fact (0 < L)] (hL : 0 < L) (M : ℕ) (hM : 2 ≤ M)
    (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-L / 2) (L / 2))))
    (henergy : IntegrableOn (zeroEnergyDensity L (-L / 2) u) (Ioi 0))
    (hlow : ∀ n : ℤ, Int.natAbs n < M →
      physicalCoeff (AddCircle.liftIoc L (-L / 2) u) n = 0) :
    let F := zeroExtension L (-L / 2) u
    Integrable (fun t : ℝ => Zeta23.mu t * Complex.normSq (Zeta23.paperFT F (t : ℂ))) ∧
    Summable (fun n : ℤ => gammaIncrement (angularFrequency (d := L) n) *
      ‖physicalCoeff (AddCircle.liftIoc L (-L / 2) u) n‖ ^ 2) ∧
    ((Complex.digamma (1 / 4)).re - Real.log Real.pi) *
        (∫ x in Ioc (-L / 2) (L / 2), ‖u x‖ ^ 2) +
      (∑' n : ℤ, gammaIncrement (angularFrequency (d := L) n) *
        ‖physicalCoeff (AddCircle.liftIoc L (-L / 2) u) n‖ ^ 2) -
      (Real.pi / 2 + L / (Real.pi ^ 2 * ((M : ℝ) - 1))) *
        (∫ x in Ioc (-L / 2) (L / 2), ‖u x‖ ^ 2) ≤
      ∫ t : ℝ, Zeta23.mu t * Complex.normSq (Zeta23.paperFT F (t : ℂ)) := by
  dsimp only
  have huWindow : MemLp u 2 (windowMeasure L (-L / 2)) := by
    simpa only [windowMeasure, show -L / 2 + L = L / 2 by ring] using hu
  have hmu := mu_quadratic_of_memLp L u huWindow henergy
  dsimp only at hmu
  have hmass : (∫ x, Complex.normSq (zeroExtension L (-L / 2) u x)) =
      ∫ x in Ioc (-L / 2) (L / 2), ‖u x‖ ^ 2 := by
    simpa only [Complex.normSq_eq_norm_sq, windowEnergy, windowMeasure,
      show -L / 2 + L = L / 2 by ring] using
      zero_extension_energy_eq L (-L / 2) u
  rw [hmass] at hmu
  have hspec := zeroExtension_jump_spectral_lower_bound L hL M hM u hu henergy hlow
  refine ⟨hmu.1, hspec.1, ?_⟩
  have heq : (∫ t : ℝ, Zeta23.mu t *
      Complex.normSq (Zeta23.paperFT (zeroExtension L (-L / 2) u) (t : ℂ))) =
      ((Complex.digamma (1 / 4)).re - Real.log Real.pi) *
        (∫ x in Ioc (-L / 2) (L / 2), ‖u x‖ ^ 2) +
      ∫ s in Ioi 0, zeroEnergyDensity L (-L / 2) u s := hmu.2
  rw [heq]
  linarith [hspec.2]

end D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation
