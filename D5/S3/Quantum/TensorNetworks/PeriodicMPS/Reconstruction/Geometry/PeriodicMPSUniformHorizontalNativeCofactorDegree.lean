/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalNativeCofactorDegree
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalNativeCofactorDegree
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Native cofactor degrees in the radical chart. -/
-- Adapted from uniform-horizontal-radical-degree/work_target.
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformHorizontalRadicalLaurent
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformHorizontalClearedHermite
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Resultants.PeriodicMPSUniformHorizontalDeterminantDegree
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformHorizontalNativeDegree

/-! Cleared Hermite entries and minors restricted to the MPS radical charts. -/

set_option autoImplicit false

namespace UniformMPSHorizontalSpectral

open MvPolynomial
open D5.S3.Quantum.TensorNetworks
open UniformMPSHorizontalNativeDegree

noncomputable section

variable {σ R : Type*} [CommRing R]

/-- Square rules and the five ambient-coordinate images for a filtered substitution. -/
structure MPSRadicalChart (σ R : Type*) [CommRing R] where
  D : MvPolynomial σ R
  E : MvPolynomial σ R
  firstRule : D.totalDegree ≤ 6
  secondRule : E.totalDegree ≤ 12
  coordinates : Fin 5 → RadicalAlgebra D E
  coordinateBound : ∀ j, RadicalDegreeLE 9 (coordinates j)

namespace MPSRadicalChart

def ofSpectrumU (v : Fin 4 → MvPolynomial σ R) (hv : ∀ j, (v j).totalDegree ≤ 1)
    (U k two : Rˣ) : MPSRadicalChart σ R := by
  let a := spectralElementary v 2
  let b := spectralElementary v 3
  let c := spectralElementary v 4
  have ha := spectralElementary_totalDegree v hv 2
  have hb := spectralElementary_totalDegree v hv 3
  have hc := spectralElementary_totalDegree v hv 4
  have h := chart_quadratic_totalDegrees a b c U k ↑(k⁻¹) ha hb hc
  exact ⟨_, _, h.2.2.2.1, h.2.2.2.2.1, radicalCoordinatesU a b c U k two,
    radicalCoordinatesU_degreeLE a b c U k two ha hb hc⟩

def ofSpectrumK (v : Fin 4 → MvPolynomial σ R) (hv : ∀ j, (v j).totalDegree ≤ 1)
    (U k two : Rˣ) : MPSRadicalChart σ R := by
  let a := spectralElementary v 2
  let b := spectralElementary v 3
  let c := spectralElementary v 4
  have ha := spectralElementary_totalDegree v hv 2
  have hb := spectralElementary_totalDegree v hv 3
  have hc := spectralElementary_totalDegree v hv 4
  have h := chart_quadratic_totalDegrees a b c U k ↑(k⁻¹) ha hb hc
  exact ⟨_, _, h.2.2.2.1, h.2.2.2.2.2, radicalCoordinatesK a b c U k two,
    radicalCoordinatesK_degreeLE a b c U k two ha hb hc⟩

end MPSRadicalChart

/-- The actual U and k charts use the two Laurent indeterminates as units. -/
def laurentRadicalChart (two₀ : Rˣ) (scaledSecondDifference : Bool)
    (v : Fin 4 → MvPolynomial σ (ChartLaurent R)) (hv : ∀ j, (v j).totalDegree ≤ 1) :
    MPSRadicalChart σ (ChartLaurent R) :=
  let two := Units.map (chartLaurentC (R := R)).toMonoidHom two₀
  if scaledSecondDifference then MPSRadicalChart.ofSpectrumK v hv chartU chartK two
  else MPSRadicalChart.ofSpectrumU v hv chartU chartK two

variable (chart : MPSRadicalChart σ R)

def radicalSubstitute {S : Type*} [CommRing S] (f : S →+* R) :
    MvPolynomial (Fin 5) S →+* RadicalAlgebra chart.D chart.E :=
  eval₂Hom (((algebraMap (MvPolynomial σ R) (RadicalAlgebra chart.D chart.E)).comp C).comp f)
    chart.coordinates

/-- Ambient total degree scales by at most nine in the four reduced basis coefficients. -/
theorem radicalSubstitute_degreeLE {S : Type*} [CommRing S]
    (f : S →+* R) (p : MvPolynomial (Fin 5) S) :
    RadicalDegreeLE (9 * p.totalDegree) (radicalSubstitute chart f p) :=
  eval₂Hom_radicalDegreeLE f _ chart.firstRule chart.secondRule chart.coordinateBound p

private def twoSiteBits (a : Fin 4) : Fin 2 → Fin 2 :=
  ![⟨a.val / 2, by omega⟩, ⟨a.val % 2, by omega⟩]

private def ambientWord {S : Type*} [CommRing S] (bra : Bool)
    {n : ℕ} (w : Fin n → Fin 2) : MvPolynomial (Fin 5) S :=
  SevenSiteTraceBase.wordPolynomial 1 0 (X (if bra then 1 else 0))
    (X (if bra then 3 else 2)) (X 4) (List.ofFn w)

private theorem ambientWord_degreeLE {S : Type*} [CommRing S] [Nontrivial S]
    (bra : Bool) {n : ℕ} (w : Fin n → Fin 2) :
    (ambientWord (S := S) bra w).totalDegree ≤ n / 2 := by
  let z : Fin 3 → MvPolynomial (Fin 5) S :=
    ![X (if bra then 1 else 0), X 4, X (if bra then 3 else 2)]
  have hz (i : Fin 3) : (z i).totalDegree ≤ 1 := by
    fin_cases i <;> simp [z]
  simpa [ambientWord, z] using wordPolynomial_aligned_totalDegree z hz (List.ofFn w)

/-- The computational-basis transfer-power moment, with the bra marking the row
and the ket marking the column. -/
def nativePowerGram {S : Type*} [CommRing S] (r : Fin 8) (ab : Fin 4 × Fin 4) :
    MvPolynomial (Fin 5) S :=
  ∑ w : Fin r.val → Fin 2,
    ambientWord true (Fin.append (twoSiteBits ab.1) w) *
    ambientWord false (Fin.append (twoSiteBits ab.2) w)

theorem nativePowerGram_totalDegree_le {S : Type*} [CommRing S] [Nontrivial S]
    (r : Fin 8) (ab : Fin 4 × Fin 4) :
    (nativePowerGram (S := S) r ab).totalDegree ≤ 8 := by
  unfold nativePowerGram
  apply totalDegree_finsetSum_le
  intro w _
  apply (totalDegree_mul _ _).trans
  have hb := ambientWord_degreeLE (S := S) true (Fin.append (twoSiteBits ab.1) w)
  have hk := ambientWord_degreeLE (S := S) false (Fin.append (twoSiteBits ab.2) w)
  have hr := r.isLt
  omega

/-- The three one-site generators used by the deleted-row minors. -/
private def nativeGenerator (j : Fin 3) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![0, 1; 0, 0], !![0, 0; 1, 0], !![1, 0; 0, -1]] j

private def twoSiteGenerator (j : Fin 3) (a b : Fin 4) : ℤ :=
  let g := nativeGenerator j
  g (twoSiteBits a 0) (twoSiteBits b 0) * (if twoSiteBits a 1 = twoSiteBits b 1 then 1 else 0) +
    (if twoSiteBits a 0 = twoSiteBits b 0 then 1 else 0) * g (twoSiteBits a 1) (twoSiteBits b 1)

private def nativePowerRotation {S : Type*} [CommRing S]
    (r : Fin 8) (ab : Fin 4 × Fin 4) (j : Fin 3) : MvPolynomial (Fin 5) S :=
  ∑ i : Fin 4,
    (C (twoSiteGenerator j ab.1 i : S) * nativePowerGram r (i, ab.2) -
      C (twoSiteGenerator j i ab.2 : S) * nativePowerGram r (ab.1, i))

private theorem nativePowerRotation_totalDegree_le {S : Type*} [CommRing S] [Nontrivial S]
    (r : Fin 8) (ab : Fin 4 × Fin 4) (j : Fin 3) :
    (nativePowerRotation (S := S) r ab j).totalDegree ≤ 8 := by
  unfold nativePowerRotation
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_sub _ _).trans
  apply max_le
  all_goals
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, zero_add]
    exact nativePowerGram_totalDegree_le _ _

/-- The five ambient partials, Gram entry, and three commutator entries at fixed transfer power. -/
def nativePowerEntry {S : Type*} [CommRing S]
    (r : Fin 8) (ab : Fin 4 × Fin 4) (j : Fin 9) : MvPolynomial (Fin 5) S :=
  Fin.addCases (fun p : Fin 5 => pderiv p (nativePowerGram r ab))
    (Fin.addCases (fun _ : Fin 1 => nativePowerGram r ab) (nativePowerRotation r ab)) j

def ambientColumnBudget (j : Fin 9) : ℕ := if j.val < 5 then 7 else 8

theorem nativePowerEntry_totalDegree_le {S : Type*} [CommRing S] [Nontrivial S]
    (r : Fin 8) (ab : Fin 4 × Fin 4) (j : Fin 9) :
    (nativePowerEntry (S := S) r ab j).totalDegree ≤ ambientColumnBudget j := by
  refine Fin.addCases (m := 5) (n := 4) ?_ ?_ j
  · intro j
    have h := (pderiv_totalDegree_le (p := nativePowerGram (S := S) r ab) j).trans
      (Nat.sub_le_sub_right (nativePowerGram_totalDegree_le (S := S) r ab) 1)
    simpa [nativePowerEntry, ambientColumnBudget, j.isLt] using h
  · intro j
    have hbudget : ambientColumnBudget (Fin.natAdd 5 j) = 8 := by
      unfold ambientColumnBudget
      simp
    simp only [nativePowerEntry, Fin.addCases_right, hbudget]
    refine Fin.addCases (m := 1) (n := 3) ?_ ?_ j
    · intro i
      simpa using nativePowerGram_totalDegree_le (S := S) r ab
    · intro i
      simpa using nativePowerRotation_totalDegree_le (S := S) r ab i

/-- The fixed ten reconstruction rows in their determinant order. -/
def nativeRows : Fin 10 → Fin 4 × Fin 4 :=
  ![(0,0), (0,1), (0,3), (1,0), (1,1), (1,2), (1,3), (3,0), (3,1), (3,3)]

def nativeDeletedRows (last : Bool) (i : Fin 9) : Fin 4 × Fin 4 :=
  nativeRows ((if last then (9 : Fin 10) else 0).succAbove i)

/-- The native row and column after inserting the cleared Hermite numerator. -/
def clearedNativeEntry {S : Type*} [CommRing S] (f : S →+* R)
    (v : Fin 4 → MvPolynomial σ R) (w : Fin 4 → R) (μ : R)
    (ab : Fin 4 × Fin 4) (j : Fin 9) :
    RadicalAlgebra chart.D chart.E :=
  ∑ r : Fin 8, algebraMap (MvPolynomial σ R) _
    ((clearedHermite v (C ∘ w) (C μ)).coeff r) *
      radicalSubstitute chart f (nativePowerEntry (S := S) r ab j)

theorem clearedNativeEntry_degreeLE {S : Type*} [CommRing S] [Nontrivial S]
    (f : S →+* R) (v : Fin 4 → MvPolynomial σ R) (hv : ∀ j, (v j).totalDegree ≤ 1)
    (w : Fin 4 → R) (μ : R) (ab : Fin 4 × Fin 4) (j : Fin 9) :
    RadicalDegreeLE (if j.val < 5 then 85 else 94) (clearedNativeEntry chart f v w μ ab j) := by
  unfold clearedNativeEntry
  apply RadicalDegreeLE.sum
  intro r _
  have hc := clearedHermite_coeff_totalDegree v w μ hv r
  have hp := nativePowerEntry_totalDegree_le (S := S) r ab j
  have hs := (radicalSubstitute_degreeLE chart f (nativePowerEntry (S := S) r ab j)).mono
    (Nat.mul_le_mul_left 9 hp)
  apply ((radicalScalar_degreeLE (hc.trans (Nat.sub_le _ _))).mul chart.firstRule
    chart.secondRule hs).mono
  unfold ambientColumnBudget
  split <;> decide

/-- The four-coefficient analogue of the columnwise determinant degree estimate. -/
theorem radicalDet_degreeLE {n : Type*} [Fintype n] [DecidableEq n]
    {D E : MvPolynomial σ R} (hD : D.totalDegree ≤ 6) (hE : E.totalDegree ≤ 12)
    (M : Matrix n n (RadicalAlgebra D E)) (budget : n → ℕ)
    (hM : ∀ i j, RadicalDegreeLE (budget j) (M i j)) :
    RadicalDegreeLE (∑ j, budget j) M.det := by
  rw [Matrix.det_apply']
  apply RadicalDegreeLE.sum
  intro p _
  have hsign : RadicalDegreeLE 0 (↑(Equiv.Perm.sign p) : RadicalAlgebra D E) := by
    let s : ℤ := Equiv.Perm.sign p
    have h : (C (s : R) : MvPolynomial σ R).totalDegree ≤ 0 := (totalDegree_C _).le
    simpa only [map_intCast] using radicalScalar_degreeLE (D := D) (E := E) h
  simpa only [zero_add] using hsign.mul hD hE
    (RadicalDegreeLE.prod hD hE _ _ budget fun j _ => hM _ j)

/-- Select nine Pauli rows. The choice of row indices includes either deleted-row minor. -/
def clearedNativeMinor {S : Type*} [CommRing S] (f : S →+* R)
    (v : Fin 4 → MvPolynomial σ R) (w : Fin 4 → R) (μ : R)
    (rows : Fin 9 → Fin 4 × Fin 4) : RadicalAlgebra chart.D chart.E :=
  (Matrix.of fun i j => clearedNativeEntry chart f v w μ (rows i) j).det

theorem clearedNativeMinor_degreeLE {S : Type*} [CommRing S] [Nontrivial S]
    (f : S →+* R) (v : Fin 4 → MvPolynomial σ R) (hv : ∀ j, (v j).totalDegree ≤ 1)
    (w : Fin 4 → R) (μ : R) (rows : Fin 9 → Fin 4 × Fin 4) :
    RadicalDegreeLE 801 (clearedNativeMinor chart f v w μ rows) := by
  unfold clearedNativeMinor
  refine (radicalDet_degreeLE chart.firstRule chart.secondRule _
    (fun j => if j.val < 5 then 85 else 94) (fun i j => ?_)).mono ?_
  · exact clearedNativeEntry_degreeLE chart f v hv w μ (rows i) j
  · decide +kernel

theorem radicalDegreeLE_star {D E : MvPolynomial σ R} {n : ℕ} {z : RadicalAlgebra D E}
    (h : RadicalDegreeLE n z) : RadicalDegreeLE n (star z) := by
  intro i j
  fin_cases j
  · simpa [radicalCoeff] using h i 0
  · fin_cases i
    · simpa [radicalCoeff] using h 0 1
    · simpa [radicalCoeff] using h 1 1

/-- If the simultaneous sign reversal has removed the even slots, the crossed product
is the scalar given by the two concrete square rules. -/
theorem crossedProduct_eq_scalar_of_odd {D E : MvPolynomial σ R}
    (z : RadicalAlgebra D E)
    (h00 : radicalCoeff z 0 0 = 0) (h11 : radicalCoeff z 1 1 = 0) :
    z * star z = algebraMap (MvPolynomial σ R) _
      (D * (radicalCoeff z 1 0) ^ 2 - E * (radicalCoeff z 0 1) ^ 2) := by
  change z.re.re = 0 at h00
  change z.im.im = 0 at h11
  ext <;> simp [radicalCoeff, h00, h11, pow_two] <;> ring

/-- Pair a minor with its second-radical sign reversal and bound all four coefficients. -/
theorem clearedNativeCrossedProduct_degreeLE {S : Type*} [CommRing S] [Nontrivial S]
    (f : S →+* R) (v : Fin 4 → MvPolynomial σ R) (hv : ∀ j, (v j).totalDegree ≤ 1)
    (w : Fin 4 → R) (μ : R) (rows : Fin 9 → Fin 4 × Fin 4) :
    let m := clearedNativeMinor chart f v w μ rows
    RadicalDegreeLE 1602 (m * star m) := by
  have h := clearedNativeMinor_degreeLE chart f v hv w μ rows
  exact h.mul chart.firstRule chart.secondRule (radicalDegreeLE_star h)

theorem RadicalDegreeLE.coeff_totalDegree_le {D E : MvPolynomial σ R} {n : ℕ}
    {z : RadicalAlgebra D E} (h : RadicalDegreeLE n z) (i j : Fin 2) :
    (radicalCoeff z i j).totalDegree ≤ n := by
  rcases h i j with hzero | hle
  · simp [hzero]
  · omega

/-- The scalar-slot Laurent polynomial of either of the two actual crossed products. -/
def nativeCrossedScalar (two₀ : Rˣ) (scaledSecondDifference last : Bool)
    (v : Fin 4 → MvPolynomial σ (ChartLaurent R)) (hv : ∀ j, (v j).totalDegree ≤ 1)
    (w : Fin 4 → ChartLaurent R) (μ : ChartLaurent R) :
    MvPolynomial σ (ChartLaurent R) :=
  let m := clearedNativeMinor (laurentRadicalChart two₀ scaledSecondDifference v hv)
    chartLaurentC v w μ (nativeDeletedRows last)
  radicalCoeff (m * star m) 0 0

theorem nativeCrossedScalar_totalDegree_le [Nontrivial R] (two₀ : Rˣ) (scaledSecondDifference last : Bool)
    (v : Fin 4 → MvPolynomial σ (ChartLaurent R)) (hv : ∀ j, (v j).totalDegree ≤ 1)
    (w : Fin 4 → ChartLaurent R) (μ : ChartLaurent R) :
    (nativeCrossedScalar two₀ scaledSecondDifference last v hv w μ).totalDegree ≤ 1602 :=
  (clearedNativeCrossedProduct_degreeLE (laurentRadicalChart two₀ scaledSecondDifference v hv)
    chartLaurentC v hv w μ (nativeDeletedRows last)).coeff_totalDegree_le 0 0

/-- In both projections every shifted Laurent coefficient keeps the 1602 spectral bound.
The U clearing uses shifts `(6, 0)` and the k division uses `(0, -2)`. -/
theorem nativeCrossedScalar_shiftedCoeff_totalDegree_le [Nontrivial R]
    (two₀ : Rˣ) (scaledSecondDifference last : Bool)
    (v : Fin 4 → MvPolynomial σ (ChartLaurent R)) (hv : ∀ j, (v j).totalDegree ≤ 1)
    (w : Fin 4 → ChartLaurent R) (μ : ChartLaurent R) (u k i j : ℤ) :
    let p := nativeCrossedScalar two₀ scaledSecondDifference last v hv w μ
    (laurentSpectralCoeff (shiftChartLaurent p u k) i j).totalDegree ≤ 1602 :=
  (shiftedLaurent_totalDegree_le _ u k i j).trans
    (nativeCrossedScalar_totalDegree_le two₀ scaledSecondDifference last v hv w μ)

end
end UniformMPSHorizontalSpectral
