/- GID: D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Sectorwise computational/Fourier projectors attain every n-partite partial bound. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Observer.WindowRegister

/-! Partial tightness of the multipartite entangled-measurement bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.SLDSpectralEnergy

namespace D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness

abbrev jointIndex (n d : ℕ) := Fin n → ZMod d

/-- The winning outcome of the n-partite sum-and-difference game. -/
def winningOutcome {n d : ℕ} [NeZero n] (x y : jointIndex n d) : jointIndex n d :=
  fun k => if k = 0 then ∑ i, x i else y k - y 0

private def tensorEntry {n d : ℕ}
    (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (x : jointIndex n d) (y : jointIndex n d) (i j : jointIndex n d) : ℂ :=
  ∏ k, U k (x k) (y k) (i k) (j k)

private def tensorMatrix {n d : ℕ}
    (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (x : jointIndex n d) (y : jointIndex n d) :
    Matrix (jointIndex n d) (jointIndex n d) ℂ :=
  fun i j => tensorEntry U x y i j

private def tensorAdjointMatrix {n d : ℕ}
    (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (x : jointIndex n d) (y : jointIndex n d) :
    Matrix (jointIndex n d) (jointIndex n d) ℂ :=
  fun i j => star (tensorEntry U x y j i)

/-- The average winning score for local unitary encodings and a joint measurement. -/
def score {n d : ℕ}
    [NeZero n] [NeZero d] [Fintype (jointIndex n d)] [DecidableEq (jointIndex n d)]
    (ρ : Matrix (jointIndex n d) (jointIndex n d) ℂ)
    (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (M : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ) : ℝ :=
  ((d : ℝ) ^ (2 * n))⁻¹ *
    ∑ x, ∑ y,
      (Matrix.trace
        (tensorMatrix U x y * ρ * tensorAdjointMatrix U x y *
          M (winningOutcome x y))).re

/-- A finite sum of positive product operators is fully separable. -/
def IsFullySeparable {n d : ℕ}
    (A : Matrix (jointIndex n d) (jointIndex n d) ℂ) : Prop :=
  ∃ k : ℕ, ∃ S : Fin k → Fin n → Matrix (ZMod d) (ZMod d) ℂ,
    (∀ a v, (S a v).PosSemidef) ∧
      ∀ i j, A i j = ∑ a, ∏ v, S a v (i v) (j v)

def IsProjectiveMeasurement {n d : ℕ} [NeZero n] [NeZero d]
    [Fintype (jointIndex n d)] [DecidableEq (jointIndex n d)]
    (M : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ) : Prop :=
  (∀ b, (M b).PosSemidef ∧ M b * M b = M b) ∧ ∑ b, M b = 1

private theorem neZeroOfTwo (n : ℕ) (h : 2 ≤ n) : NeZero n :=
  ⟨by omega⟩

def claim : Prop := by
  classical
  exact ∀ n d m : ℕ, (hn : 2 ≤ n) → (hd : 2 ≤ d) → m ≤ d ^ (n - 1) →
    letI : NeZero n := neZeroOfTwo n hn
    letI : NeZero d := neZeroOfTwo d hd
    ∃ (ρ : Matrix (jointIndex n d) (jointIndex n d) ℂ)
      (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
      (M : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ),
      IsDensity ρ ∧
      (∀ k x y, U k x y ∈ Matrix.unitaryGroup (ZMod d) ℂ) ∧
      IsProjectiveMeasurement M ∧
      ((Finset.univ.filter (fun b => IsFullySeparable (M b))).card = d * m) ∧
      score ρ U M = ((d : ℝ) ^ n - d * m + m) / (d : ℝ) ^ n

private def sectorPoint {n d : ℕ} (t : ZMod d) (r : jointIndex n d) : jointIndex n d :=
  fun k => t + r k

private def sectorLabel {n d : ℕ} [NeZero n] (b : jointIndex n d) : jointIndex n d :=
  fun k => if k = 0 then 0 else b k

private def sectorCoordinate {n d : ℕ} [NeZero n] (i : jointIndex n d) : jointIndex n d :=
  fun k => i k - i 0

private def computationalVector {n d : ℕ} (t : ZMod d) (r : jointIndex n d) :
    jointIndex n d → ℂ := by
  classical
  exact fun i => if i = sectorPoint t r then 1 else 0

private def fourierVector {n d : ℕ} [NeZero n] [NeZero d]
    (a : ZMod d) (r : jointIndex n d) : jointIndex n d → ℂ := by
  classical
  exact fun i => if i = sectorPoint (i 0) r then
    (Real.sqrt d : ℂ)⁻¹ * ZMod.stdAddChar (a * i 0) else 0

private def selectedVector {n d : ℕ} [NeZero n] [NeZero d]
    (r : Finset (jointIndex n d)) (b : jointIndex n d) : jointIndex n d → ℂ := by
  classical
  exact if sectorLabel b ∈ r then computationalVector (b 0) (sectorLabel b)
    else fourierVector (b 0) (sectorLabel b)

private def selectedMeasurement {n d : ℕ} [NeZero n] [NeZero d]
    (r : Finset (jointIndex n d)) (b : jointIndex n d) :
    Matrix (jointIndex n d) (jointIndex n d) ℂ :=
  Matrix.vecMulVec (selectedVector r b) (star (selectedVector r b))

private def ghzDensity (n d : ℕ) [NeZero n] [NeZero d] :
    Matrix (jointIndex n d) (jointIndex n d) ℂ :=
  Matrix.vecMulVec (fourierVector 0 (0 : jointIndex n d))
    (star (fourierVector 0 (0 : jointIndex n d)))

private def localEncoding (n d : ℕ) [NeZero d] :
    Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ :=
  fun _ x y => D5.S3.Observer.WindowRegister.clockMatrix d ^ x.val *
    D5.S3.Observer.WindowRegister.shiftMatrix d ^ y.val

private theorem sectorLabel_zero {n d : ℕ} [NeZero n] (b : jointIndex n d) :
    sectorLabel b 0 = 0 := by
  change (if (0 : Fin n) = 0 then (0 : ZMod d) else b 0) = 0
  exact if_pos rfl

private theorem sector_coordinates {n d : ℕ} [NeZero n] (i : jointIndex n d) :
    sectorCoordinate i 0 = 0 ∧ sectorPoint (i 0) (sectorCoordinate i) = i := by
  constructor
  · change i 0 - i 0 = 0
    exact sub_self _
  · funext k
    change i 0 + (i k - i 0) = i k
    abel

private theorem sectorPoint_injective {n d : ℕ} [NeZero n]
    (r s : jointIndex n d) (hr : r 0 = 0) (hs : s 0 = 0) (t u : ZMod d)
    (h : sectorPoint t r = sectorPoint u s) : t = u ∧ r = s := by
  have ht : t = u := by
    have h0 := congrFun h 0
    change t + r 0 = u + s 0 at h0
    simpa only [hr, hs, add_zero] using h0
  refine ⟨ht, ?_⟩
  funext k
  have hk := congrFun h k
  change t + r k = u + s k at hk
  rw [ht] at hk
  exact add_left_cancel hk

private theorem computational_projector_separable {n d : ℕ}
    (t : ZMod d) (r : jointIndex n d) :
    IsFullySeparable (Matrix.vecMulVec (computationalVector t r)
      (star (computationalVector t r))) := by
  classical
  let p : Fin n → Matrix (ZMod d) (ZMod d) ℂ := fun k =>
    Matrix.vecMulVec (Pi.single (t + r k) 1) (star (Pi.single (t + r k) 1))
  refine ⟨1, fun _ => p, ?_, ?_⟩
  · intro a k
    exact Matrix.posSemidef_vecMulVec_self_star _
  · intro i j
    change computationalVector t r i * star (computationalVector t r j) =
      ∑ _ : Fin 1, ∏ k, p k (i k) (j k)
    rw [Fin.sum_univ_one]
    by_cases hi : i = sectorPoint t r
    · by_cases hj : j = sectorPoint t r
      · subst i
        subst j
        change (if sectorPoint t r = sectorPoint t r then (1 : ℂ) else 0) *
          star (if sectorPoint t r = sectorPoint t r then (1 : ℂ) else 0) = _
        simp only [if_pos rfl, star_one, mul_one]
        apply (Finset.prod_eq_one _)
        intro k _
        change (Pi.single (t + r k) (1 : ℂ)) (t + r k) *
          star ((Pi.single (t + r k) (1 : ℂ)) (t + r k)) = 1
        simp only [Pi.single_eq_same, star_one, mul_one]
      · have hjk : ∃ k, j k ≠ t + r k := by
          by_contra h
          apply hj
          funext k
          exact not_not.mp (not_exists.mp h k)
        obtain ⟨k, hk⟩ := hjk
        change (if i = sectorPoint t r then (1 : ℂ) else 0) *
          star (if j = sectorPoint t r then (1 : ℂ) else 0) = _
        rw [if_neg hj, star_zero, mul_zero]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ k)
        change (Pi.single (t + r k) (1 : ℂ)) (i k) *
          star ((Pi.single (t + r k) (1 : ℂ)) (j k)) = 0
        rw [Pi.single_eq_of_ne hk, star_zero, mul_zero]
    · have hik : ∃ k, i k ≠ t + r k := by
        by_contra h
        apply hi
        funext k
        exact not_not.mp (not_exists.mp h k)
      obtain ⟨k, hk⟩ := hik
      change (if i = sectorPoint t r then (1 : ℂ) else 0) *
        star (if j = sectorPoint t r then (1 : ℂ) else 0) = _
      rw [if_neg hi, zero_mul]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      change (Pi.single (t + r k) (1 : ℂ)) (i k) *
        star ((Pi.single (t + r k) (1 : ℂ)) (j k)) = 0
      rw [Pi.single_eq_of_ne hk, zero_mul]

private theorem encodings_unitary (n d : ℕ) [NeZero d] :
    ∀ k x y, localEncoding n d k x y ∈ Matrix.unitaryGroup (ZMod d) ℂ := by
  intro k x y
  obtain ⟨hx, hz⟩ := D5.S3.Observer.WindowRegister.window_unitary (M := d)
  have hxmem : D5.S3.Observer.WindowRegister.shiftMatrix d ∈
      Matrix.unitaryGroup (ZMod d) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hx
  have hzmem : D5.S3.Observer.WindowRegister.clockMatrix d ∈
      Matrix.unitaryGroup (ZMod d) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hz
  change D5.S3.Observer.WindowRegister.clockMatrix d ^ x.val *
    D5.S3.Observer.WindowRegister.shiftMatrix d ^ y.val ∈ Matrix.unitaryGroup (ZMod d) ℂ
  exact (Matrix.unitaryGroup _ _).mul_mem
    ((Matrix.unitaryGroup _ _).pow_mem hzmem x.val)
    ((Matrix.unitaryGroup _ _).pow_mem hxmem y.val)

private theorem sector_basis (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (a c : ZMod d) (r s : jointIndex n d)
    (hr : r 0 = 0) (hs : s 0 = 0) :
    star (fourierVector a r) ⬝ᵥ fourierVector c s =
      if a = c ∧ r = s then 1 else 0 := by
  have hcoords := sector_coordinates (sectorPoint (0 : ZMod d) r)
  have hinj := sectorPoint_injective r s hr hs
  sorry

private theorem ghz_density (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) : IsDensity (ghzDensity n d) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  change Matrix.trace (Matrix.vecMulVec (fourierVector 0 (0 : jointIndex n d))
    (star (fourierVector 0 (0 : jointIndex n d)))) = 1
  rw [Matrix.trace_vecMulVec]
  have h := sector_basis n d hn hd 0 0 0 0 rfl rfl
  simpa only [and_self, if_pos rfl, dotProduct_comm] using h

private theorem selected_orthonormal (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d))
    (b c : jointIndex n d) :
    star (selectedVector r b) ⬝ᵥ selectedVector r c = if b = c then 1 else 0 := by
  have hb := sector_basis n d hn hd (b 0) (c 0) (sectorLabel b) (sectorLabel c)
    (sectorLabel_zero b) (sectorLabel_zero c)
  sorry

private theorem sector_measurement (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d)) :
    IsProjectiveMeasurement (selectedMeasurement r) := by
  have horth := selected_orthonormal n d hn hd r
  sorry

private theorem rankOne_separable_product (n d : ℕ) [NeZero n] [NeZero d]
    (v : jointIndex n d → ℂ) (hv : star v ⬝ᵥ v = 1)
    (hsep : IsFullySeparable (Matrix.vecMulVec v (star v))) :
    ∃ f : Fin n → ZMod d → ℂ, v = fun i => ∏ k, f k (i k) := by
  sorry

private theorem fourier_not_product (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (a : ZMod d) (r : jointIndex n d)
    (hr : r 0 = 0) :
    ¬ ∃ f : Fin n → ZMod d → ℂ, fourierVector a r = fun i => ∏ k, f k (i k) := by
  sorry

private theorem selected_separable_iff (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d)) (b : jointIndex n d) :
    IsFullySeparable (selectedMeasurement r b) ↔ sectorLabel b ∈ r := by
  classical
  by_cases hb : sectorLabel b ∈ r
  · refine ⟨fun _ => hb, fun _ => ?_⟩
    change IsFullySeparable (Matrix.vecMulVec (selectedVector r b) (star (selectedVector r b)))
    have hvec : selectedVector r b = computationalVector (b 0) (sectorLabel b) :=
      if_pos hb
    rw [hvec]
    exact computational_projector_separable _ _
  · refine ⟨fun hsep => ?_, fun h => (hb h).elim⟩
    have hvec : selectedVector r b = fourierVector (b 0) (sectorLabel b) := if_neg hb
    change IsFullySeparable (Matrix.vecMulVec (selectedVector r b) (star (selectedVector r b))) at hsep
    rw [hvec] at hsep
    have hv := sector_basis n d hn hd (b 0) (b 0) (sectorLabel b) (sectorLabel b)
      (sectorLabel_zero b) (sectorLabel_zero b)
    rw [if_pos ⟨rfl, rfl⟩] at hv
    exact (fourier_not_product n d hn hd (b 0) (sectorLabel b) (sectorLabel_zero b)
      (rankOne_separable_product n d _ hv hsep)).elim

private theorem sector_count (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d))
    (hr : ∀ s ∈ r, s 0 = 0) :
    (Finset.univ.filter (fun b => sectorLabel b ∈ r)).card = d * r.card := by
  classical
  sorry

private theorem sector_separability_count (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d))
    (hr : ∀ s ∈ r, s 0 = 0) :
    (letI : DecidablePred (fun b => IsFullySeparable (selectedMeasurement r b)) := Classical.decPred _;
      (Finset.univ.filter (fun b => IsFullySeparable (selectedMeasurement r b))).card = d * r.card) := by
  classical
  have heq : (Finset.univ.filter (fun b => IsFullySeparable (selectedMeasurement r b))) =
      Finset.univ.filter (fun b => sectorLabel b ∈ r) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      selected_separable_iff n d hn hd r b]
  rw [heq]
  exact sector_count n d hn hd r hr

private theorem choose_sectors (n d m : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hm : m ≤ d ^ (n - 1)) :
    ∃ r : Finset (jointIndex n d), r.card = m ∧ ∀ s ∈ r, s 0 = 0 := by
  sorry

private theorem encoded_ghz (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (x y : jointIndex n d) :
    ∃ z : ℂ, Complex.normSq z = 1 ∧
      tensorMatrix (localEncoding n d) x y *ᵥ fourierVector 0 (0 : jointIndex n d) =
        z • fourierVector (∑ k, x k) (sectorCoordinate y) := by
  sorry

private theorem winning_probability (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d))
    (x y : jointIndex n d) :
    (Matrix.trace (tensorMatrix (localEncoding n d) x y * ghzDensity n d *
      tensorAdjointMatrix (localEncoding n d) x y *
      selectedMeasurement r (winningOutcome x y))).re =
        if sectorCoordinate y ∈ r then (d : ℝ)⁻¹ else 1 := by
  have hencoded := encoded_ghz n d hn hd x y
  have horth := sector_basis n d hn hd (∑ k, x k) (∑ k, x k)
    (sectorCoordinate y) (sectorCoordinate y) (sector_coordinates y).1 (sector_coordinates y).1
  sorry

private theorem sector_score (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d))
    (hr : ∀ s ∈ r, s 0 = 0) :
    score (ghzDensity n d) (localEncoding n d) (selectedMeasurement r) =
      ((d : ℝ) ^ n - d * r.card + r.card) / (d : ℝ) ^ n := by
  have hprob := winning_probability n d hn hd r
  have hcount := sector_count n d hn hd r hr
  sorry

theorem result : claim := by
  intro n d m hn hd hm
  letI : NeZero n := neZeroOfTwo n hn
  letI : NeZero d := neZeroOfTwo d hd
  obtain ⟨r, hcard, hr⟩ := choose_sectors n d m hn hm
  refine ⟨ghzDensity n d, localEncoding n d, selectedMeasurement r,
    ghz_density n d hn hd, encodings_unitary n d,
    sector_measurement n d hn hd r, ?_, ?_⟩
  · have h := sector_separability_count n d hn hd r hr
    simpa only [hcard] using h
  · have h := sector_score n d hn hd r hr
    simpa only [hcard] using h

end D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness
