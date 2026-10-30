/- GID: D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Sectorwise computational/Fourier projectors attain every n-partite partial bound. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Observer.MatrixUnitCertificate
import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment

/-! Partial tightness of the multipartite entangled-measurement bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.SLDSpectralEnergy
open D5.S3.Observer.WindowRegister

namespace D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness

abbrev jointIndex (n d : ℕ) := Fin n → ZMod d

/-- The winning outcome of the n-partite sum-and-difference game. -/
def winningOutcome {n d : ℕ} [NeZero n] (x y : jointIndex n d) : jointIndex n d :=
  fun k => if k = 0 then ∑ i, x i else y k - y 0

private def tensorMatrix {n d : ℕ}
    (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (x : jointIndex n d) (y : jointIndex n d) :
    Matrix (jointIndex n d) (jointIndex n d) ℂ :=
  D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap (fun _ : Fin n => ZMod d)
    (fun k => U k (x k) (y k))

/-- The average winning score for local unitary encodings and a joint measurement. -/
def score {n d : ℕ}
    [NeZero n] [NeZero d] [Fintype (jointIndex n d)] [DecidableEq (jointIndex n d)]
    (ρ : Matrix (jointIndex n d) (jointIndex n d) ℂ)
    (u : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (p : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ) : ℝ :=
  ((d : ℝ) ^ (2 * n))⁻¹ *
    ∑ x, ∑ y,
      (Matrix.trace
        (tensorMatrix u x y * ρ * (tensorMatrix u x y)ᴴ *
          p (winningOutcome x y))).re

/-- A finite sum of positive product operators is fully separable. -/
def IsFullySeparable {n d : ℕ}
    (a : Matrix (jointIndex n d) (jointIndex n d) ℂ) : Prop :=
  ∃ k : ℕ, ∃ s : Fin k → Fin n → Matrix (ZMod d) (ZMod d) ℂ,
    (∀ j v, (s j v).PosSemidef) ∧
      ∀ i j, a i j = ∑ q, ∏ v, s q v (i v) (j v)

def IsProjectiveMeasurement {n d : ℕ} [NeZero n] [NeZero d]
    [Fintype (jointIndex n d)] [DecidableEq (jointIndex n d)]
    (p : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ) : Prop :=
  (∀ b, IsStarProjection (p b)) ∧ ∑ b, p b = 1

private theorem neZeroOfTwo (n : ℕ) (h : 2 ≤ n) : NeZero n :=
  NeZero.of_pos (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) h)

def claim : Prop := by
  classical
  exact ∀ n d m : ℕ, (hn : 2 ≤ n) → (hd : 2 ≤ d) → m ≤ d ^ (n - 1) →
    letI : NeZero n := neZeroOfTwo n hn
    letI : NeZero d := neZeroOfTwo d hd
    ∃ (ρ : Matrix (jointIndex n d) (jointIndex n d) ℂ)
      (u : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
      (p : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ),
      IsDensity ρ ∧
      (∀ k x y, u k x y ∈ Matrix.unitaryGroup (ZMod d) ℂ) ∧
      IsProjectiveMeasurement p ∧
      ((Finset.univ.filter (fun b => IsFullySeparable (p b))).card = d * m) ∧
      score ρ u p = ((d : ℝ) ^ n - d * m + m) / (d : ℝ) ^ n

private def sectorPoint {n d : ℕ} (t : ZMod d) (r : jointIndex n d) : jointIndex n d :=
  fun k => t + r k

private def sectorCoordinate {n d : ℕ} [NeZero n] (i : jointIndex n d) : jointIndex n d :=
  fun k => i k - i 0

private def fourierVector {n d : ℕ} [NeZero n] [NeZero d]
    (a : ZMod d) (r : jointIndex n d) : jointIndex n d → ℂ := by
  classical
  exact fun i => if i = sectorPoint (i 0) r then
    (Real.sqrt d : ℂ)⁻¹ * ZMod.stdAddChar (a * i 0) else 0

private def selectedVector {n d : ℕ} [NeZero n] [NeZero d]
    (r : Finset (jointIndex n d)) (b : jointIndex n d) : jointIndex n d → ℂ := by
  classical
  exact if Function.update b 0 0 ∈ r then
    Pi.single (sectorPoint (b 0) (Function.update b 0 0)) 1
    else fourierVector (b 0) (Function.update b 0 0)

private def selectedMeasurement {n d : ℕ} [NeZero n] [NeZero d]
    (r : Finset (jointIndex n d)) (b : jointIndex n d) :
    Matrix (jointIndex n d) (jointIndex n d) ℂ :=
  D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (selectedVector r b)

private def ghzDensity (n d : ℕ) [NeZero n] [NeZero d] :
    Matrix (jointIndex n d) (jointIndex n d) ℂ :=
  D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity
    (fourierVector 0 (0 : jointIndex n d))

private def localEncoding (n d : ℕ) [NeZero d] :
    Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ :=
  fun _ x y => D5.S3.Observer.WindowRegister.clockMatrix d ^ x.val *
    D5.S3.Observer.WindowRegister.shiftMatrix d ^ y.val

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

private theorem computational_projector_separable {n d : ℕ} [NeZero d]
    (t : ZMod d) (r : jointIndex n d) :
    IsFullySeparable (Matrix.vecMulVec (Pi.single (sectorPoint t r) (1 : ℂ))
      (star (Pi.single (sectorPoint t r) (1 : ℂ)))) := by
  classical
  let p : Fin n → Matrix (ZMod d) (ZMod d) ℂ := fun k =>
    Matrix.vecMulVec (Pi.single (t + r k) 1) (star (Pi.single (t + r k) 1))
  refine ⟨1, fun _ => p, ?_, ?_⟩
  · intro a k
    exact Matrix.posSemidef_vecMulVec_self_star _
  · intro i j
    change (Pi.single (sectorPoint t r) 1 : jointIndex n d → ℂ) i *
      star ((Pi.single (sectorPoint t r) 1 : jointIndex n d → ℂ) j) =
      ∑ _ : Fin 1, ∏ k, p k (i k) (j k)
    rw [Fin.sum_univ_one]
    simp only [Pi.single_apply]
    by_cases hi : i = sectorPoint t r
    · by_cases hj : j = sectorPoint t r
      · subst i
        subst j
        change (if sectorPoint t r = sectorPoint t r then (1 : ℂ) else 0) *
          star (if sectorPoint t r = sectorPoint t r then (1 : ℂ) else 0) = _
        simp only [ite_true, star_one, mul_one]
        symm
        apply Finset.prod_eq_one
        intro k _
        change (Pi.single (t + r k) 1 : ZMod d → ℂ) (t + r k) *
          star ((Pi.single (t + r k) 1 : ZMod d → ℂ) (t + r k)) = 1
        simp only [Pi.single_eq_same, star_one, mul_one]
      · have hjk : ∃ k, j k ≠ t + r k := by
          by_contra h
          apply hj
          funext k
          exact not_not.mp (not_exists.mp h k)
        obtain ⟨k, hk⟩ := hjk
        change (if i = sectorPoint t r then (1 : ℂ) else 0) *
          star (if j = sectorPoint t r then (1 : ℂ) else 0) = _
        rw [ite_eq_right hj, star_zero, mul_zero]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ k)
        change (Pi.single (t + r k) 1 : ZMod d → ℂ) (i k) *
          star ((Pi.single (t + r k) 1 : ZMod d → ℂ) (j k)) = 0
        rw [Pi.single_eq_of_ne hk, star_zero, mul_zero]
    · have hik : ∃ k, i k ≠ t + r k := by
        by_contra h
        apply hi
        funext k
        exact not_not.mp (not_exists.mp h k)
      obtain ⟨k, hk⟩ := hik
      change (if i = sectorPoint t r then (1 : ℂ) else 0) *
        star (if j = sectorPoint t r then (1 : ℂ) else 0) = _
      rw [ite_eq_right hi, zero_mul]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      change (Pi.single (t + r k) 1 : ZMod d → ℂ) (i k) *
        star ((Pi.single (t + r k) 1 : ZMod d → ℂ) (j k)) = 0
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

private theorem fourier_at_point {n d : ℕ} [NeZero n] [NeZero d]
    (a t : ZMod d) (r : jointIndex n d) (hr : r 0 = 0) :
    fourierVector a r (sectorPoint t r) =
      (Real.sqrt d : ℂ)⁻¹ * ZMod.stdAddChar (a * t) := by
  classical
  change (if sectorPoint t r = sectorPoint (t + r 0) r then
    (Real.sqrt d : ℂ)⁻¹ * ZMod.stdAddChar (a * (t + r 0)) else 0) = _
  rw [hr, add_zero, ite_eq_left rfl]

private theorem fourier_off_sector {n d : ℕ} [NeZero n] [NeZero d]
    (a : ZMod d) (r i : jointIndex n d) (hi : i ≠ sectorPoint (i 0) r) :
    fourierVector a r i = 0 := by
  classical
  exact ite_eq_right hi

private theorem sector_sum {n d : ℕ} [NeZero n] [NeZero d]
    (r : jointIndex n d) (hr : r 0 = 0) (f : jointIndex n d → ℂ)
    (hf : ∀ i, i ≠ sectorPoint (i 0) r → f i = 0) :
    ∑ i, f i = ∑ t, f (sectorPoint t r) := by
  classical
  symm
  apply Fintype.sum_of_injective (sectorPoint · r)
    (fun t u h => (sectorPoint_injective r r hr hr t u h).1) _ _
  · intro i hi
    apply hf i
    intro h
    exact hi ⟨i 0, h.symm⟩
  · intro t
    rfl

private theorem sector_basis (n d : ℕ) [NeZero n] [NeZero d]
    (_hn : 2 ≤ n) (hd : 2 ≤ d) (a c : ZMod d) (r s : jointIndex n d)
    (hr : r 0 = 0) (hs : s 0 = 0) :
    star (fourierVector a r) ⬝ᵥ fourierVector c s =
      if a = c ∧ r = s then 1 else 0 := by
  classical
  by_cases hrs : r = s
  · subst s
    change (∑ i, star (fourierVector a r i) * fourierVector c r i) = _
    rw [sector_sum r hr _ (by
      intro i hi
      rw [fourier_off_sector a r i hi, star_zero, zero_mul])]
    have heach (t : ZMod d) :
        star (fourierVector a r (sectorPoint t r)) *
          fourierVector c r (sectorPoint t r) =
        ((Real.sqrt d : ℂ)⁻¹ * (Real.sqrt d : ℂ)⁻¹) *
          ZMod.stdAddChar (t * (c - a)) := by
      rw [fourier_at_point a t r hr, fourier_at_point c t r hr]
      simp only [star_mul, star_inv₀]
      have hstar : star (Real.sqrt d : ℂ) = (Real.sqrt d : ℂ) :=
        Complex.conj_ofReal _
      rw [hstar]
      have hchar : star (ZMod.stdAddChar (a * t)) =
          ZMod.stdAddChar (-(a * t)) :=
        (AddChar.map_neg_eq_conj _ _).symm
      rw [hchar]
      calc
        _ = ((Real.sqrt d : ℂ)⁻¹ * (Real.sqrt d : ℂ)⁻¹) *
            (ZMod.stdAddChar (-(a * t)) * ZMod.stdAddChar (c * t)) := by ring
        _ = _ := by
          rw [← AddChar.map_add_eq_mul]
          congr 2
          ring
    rw [Finset.sum_congr rfl (fun t _ => heach t)]
    rw [← Finset.mul_sum,
      AddChar.sum_mulShift (c - a) (ZMod.isPrimitive_stdAddChar d), ZMod.card]
    by_cases hac : a = c
    · subst c
      simp only [sub_self, and_true, ↓reduceIte]
      have hsqrt : (Real.sqrt d : ℂ) ≠ 0 := by
        apply Complex.ofReal_ne_zero.mpr
        apply Real.sqrt_ne_zero'.mpr
        exact_mod_cast (show 0 < d by omega)
      have hsq : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
        exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
      rw [← hsq]
      field_simp [hsqrt]
    · rw [ite_eq_right (sub_ne_zero.mpr (Ne.symm hac)), ite_eq_right (by tauto)]
      simp only [Nat.cast_zero, mul_zero]
  · rw [ite_eq_right (fun h => hrs h.2)]
    change (∑ i, star (fourierVector a r i) * fourierVector c s i) = 0
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i = sectorPoint (i 0) r
    · have his : i ≠ sectorPoint (i 0) s := by
        intro his
        exact hrs (sectorPoint_injective r s hr hs (i 0) (i 0) (hi.symm.trans his)).2
      rw [fourier_off_sector c s i his, mul_zero]
    · rw [fourier_off_sector a r i hi, star_zero, zero_mul]

private theorem ghz_density (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) : IsDensity (ghzDensity n d) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  change Matrix.trace (Matrix.vecMulVec (fourierVector 0 (0 : jointIndex n d))
    (star (fourierVector 0 (0 : jointIndex n d)))) = 1
  rw [Matrix.trace_vecMulVec]
  have h := sector_basis n d hn hd 0 0 0 0 rfl rfl
  rw [ite_eq_left ⟨rfl, rfl⟩] at h
  exact (dotProduct_comm _ _).trans h

private theorem outcome_pair_injective {n d : ℕ} [NeZero n]
    (b c : jointIndex n d) (hhead : b 0 = c 0)
    (hlabel : Function.update b 0 0 = Function.update c 0 0) :
    b = c := by
  funext k
  by_cases hk : k = 0
  · subst k
    exact hhead
  · have h := congrFun hlabel k
    simpa only [Function.update_of_ne hk] using h

private theorem fourier_other_sector {n d : ℕ} [NeZero n] [NeZero d]
    (a t : ZMod d) (r s : jointIndex n d) (hr : r 0 = 0) (hs : s 0 = 0)
    (hrs : r ≠ s) : fourierVector a s (sectorPoint t r) = 0 := by
  apply fourier_off_sector
  intro h
  have h0 : sectorPoint t r 0 = t := by
    change t + r 0 = t
    rw [hr, add_zero]
  rw [h0] at h
  exact hrs (sectorPoint_injective r s hr hs t t h).2

private theorem selected_orthonormal (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d))
    (b c : jointIndex n d) :
    star (selectedVector r b) ⬝ᵥ selectedVector r c = if b = c then 1 else 0 := by
  classical
  have hcomp (b c : jointIndex n d) (hb : (Function.update b 0 0) ∈ r) :
      star (selectedVector r b) ⬝ᵥ selectedVector r c = if b = c then 1 else 0 := by
    have hbvec : selectedVector r b =
        Pi.single (sectorPoint (b 0) (Function.update b 0 0)) 1 := ite_eq_left hb
    rw [hbvec, Pi.star_single, star_one, single_one_dotProduct]
    by_cases hc : (Function.update c 0 0) ∈ r
    · have hcvec : selectedVector r c =
          Pi.single (sectorPoint (c 0) (Function.update c 0 0)) 1 := ite_eq_left hc
      rw [hcvec]
      simp only [Pi.single_apply]
      change (if sectorPoint (b 0) (Function.update b 0 0) = sectorPoint (c 0) (Function.update c 0 0)
        then (1 : ℂ) else 0) = _
      have heq : sectorPoint (b 0) (Function.update b 0 0) =
          sectorPoint (c 0) (Function.update c 0 0) ↔ b = c := by
        constructor
        · intro h
          obtain ⟨hh, hl⟩ := sectorPoint_injective _ _
            (Function.update_self 0 0 b) (Function.update_self 0 0 c) _ _ h
          exact outcome_pair_injective b c hh hl
        · intro h
          subst c
          rfl
      exact ite_cond_congr (propext heq)
    · have hcvec : selectedVector r c = fourierVector (c 0) (Function.update c 0 0) := ite_eq_right hc
      rw [hcvec]
      have hlabels : (Function.update b 0 0) ≠ (Function.update c 0 0) := by
        intro h
        exact hc (h ▸ hb)
      rw [fourier_other_sector _ _ _ _
        (Function.update_self 0 0 b) (Function.update_self 0 0 c) hlabels]
      exact (ite_eq_right (fun h : b = c =>
        hlabels (congrArg (fun b => Function.update b 0 0) h))).symm
  by_cases hb : (Function.update b 0 0) ∈ r
  · exact hcomp b c hb
  · by_cases hc : (Function.update c 0 0) ∈ r
    · rw [star_dotProduct, hcomp c b hc]
      by_cases hbc : b = c
      · subst c
        exact (hb hc).elim
      · rw [ite_eq_right (Ne.symm hbc), ite_eq_right hbc, star_zero]
    · have hbvec : selectedVector r b = fourierVector (b 0) (Function.update b 0 0) := ite_eq_right hb
      have hcvec : selectedVector r c = fourierVector (c 0) (Function.update c 0 0) := ite_eq_right hc
      rw [hbvec, hcvec, sector_basis n d hn hd _ _ _ _
        (Function.update_self 0 0 b) (Function.update_self 0 0 c)]
      have heq : b 0 = c 0 ∧ (Function.update b 0 0) = (Function.update c 0 0) ↔ b = c :=
        ⟨fun h => outcome_pair_injective b c h.1 h.2, fun h => by subst c; exact ⟨rfl, rfl⟩⟩
      exact ite_cond_congr (propext heq)

private theorem sector_measurement (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d)) :
    IsProjectiveMeasurement (selectedMeasurement r) := by
  classical
  have horth := selected_orthonormal n d hn hd r
  change (∀ b, IsStarProjection (selectedMeasurement r b)) ∧
      ∑ b, selectedMeasurement r b = 1
  constructor
  · intro b
    refine ⟨?_, (Matrix.posSemidef_vecMulVec_self_star _).isHermitian⟩
    have hnorm := horth b b
    rw [ite_eq_left rfl] at hnorm
    exact (D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake
      (selectedVector r b) hnorm 1).1
  · let w : Matrix (jointIndex n d) (jointIndex n d) ℂ := fun i b => selectedVector r b i
    have hw : wᴴ * w = 1 := by
      ext b c
      change (star (selectedVector r b) ⬝ᵥ selectedVector r c) =
        (1 : Matrix (jointIndex n d) (jointIndex n d) ℂ) b c
      rw [horth b c, Matrix.one_apply]
    have hw' : w * wᴴ = 1 := mul_eq_one_comm.mp hw
    calc
      ∑ b, selectedMeasurement r b = w * wᴴ := by
        ext i j
        rw [Matrix.sum_apply, Matrix.mul_apply]
        change (∑ b, selectedVector r b i * star (selectedVector r b j)) =
          ∑ b, selectedVector r b i * star (selectedVector r b j)
        rfl
      _ = 1 := hw'

private theorem rankOne_separable_product (n d : ℕ) [NeZero n] [NeZero d]
    (v : jointIndex n d → ℂ) (hv : star v ⬝ᵥ v = 1)
    (hsep : IsFullySeparable (Matrix.vecMulVec v (star v))) :
    ∃ f : Fin n → ZMod d → ℂ, v = fun i => ∏ k, f k (i k) := by
  classical
  obtain ⟨l, s, hs, hsum⟩ := hsep
  let a : Fin l → Matrix (jointIndex n d) (jointIndex n d) ℂ :=
    fun j i k => ∏ t, s j t (i t) (k t)
  have hapsd (j : Fin l) : (a j).PosSemidef := by
    have hprod (t : Finset (Fin n)) :
        Matrix.PosSemidef (fun i k : jointIndex n d => ∏ u ∈ t, s j u (i u) (k u)) := by
      induction t using Finset.induction_on with
      | empty =>
        have he : (fun i k : jointIndex n d =>
            ∏ u ∈ (∅ : Finset (Fin n)), s j u (i u) (k u)) =
            Matrix.vecMulVec (fun _ => (1 : ℂ)) (star (fun _ => 1)) := by
          funext i k
          simp only [Finset.prod_empty, Matrix.vecMulVec_apply, Pi.star_apply,
            star_one, mul_one]
        rw [he]
        exact Matrix.posSemidef_vecMulVec_self_star _
      | @insert u t hu ih =>
        have he : (fun i k : jointIndex n d => ∏ w ∈ insert u t, s j w (i w) (k w)) =
            Matrix.hadamard ((s j u).submatrix (fun i : jointIndex n d => i u)
              (fun i => i u)) (fun i k => ∏ w ∈ t, s j w (i w) (k w)) := by
          funext i k
          exact Finset.prod_insert hu
        rw [he]
        exact ((hs j u).submatrix (fun i : jointIndex n d => i u)).hadamard ih
    exact hprod Finset.univ
  have hmatrix : ∑ j, a j = Matrix.vecMulVec v (star v) := by
    ext i k
    rw [Matrix.sum_apply]
    exact (hsum i k).symm
  have hker (j : Fin l) (x : jointIndex n d → ℂ) (hx : star v ⬝ᵥ x = 0) :
      a j *ᵥ x = 0 := by
    have hzero : ∑ q, star x ⬝ᵥ a q *ᵥ x = 0 := by
      calc
        _ = star x ⬝ᵥ (∑ q, a q) *ᵥ x := by
          rw [Matrix.sum_mulVec, dotProduct_sum]
        _ = 0 := by
          rw [hmatrix, Matrix.vecMulVec_mulVec, hx]
          have hzero : MulOpposite.op (0 : ℂ) • v = 0 := by
            ext k
            exact mul_zero (v k)
          rw [hzero, dotProduct_zero]
    apply (hapsd j).dotProduct_mulVec_zero_iff.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun q _ => (hapsd q).dotProduct_mulVec_nonneg x)).mp hzero j (Finset.mem_univ j)
  have hvne : v ≠ 0 := by
    intro h
    rw [h, star_zero, zero_dotProduct] at hv
    exact zero_ne_one hv
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hvne (funext h)
  obtain ⟨j, hj⟩ : ∃ j, a j i i ≠ 0 := by
    by_contra! h
    have he := hsum i i
    change v i * star (v i) = ∑ j, a j i i at he
    simp only [h, Finset.sum_const_zero] at he
    exact mul_ne_zero hi (star_ne_zero.mpr hi) he
  let z : ℂ := a j i i / v i
  have hz : (fun k => a j k i) = z • v := by
    funext k
    have hx : star v ⬝ᵥ (Pi.single k (star (v i)) - Pi.single i (star (v k))) = 0 := by
      simp only [dotProduct_sub, dotProduct_single, Pi.star_apply]
      ring
    have h := congrFun (hker j _ hx) i
    simp only [Matrix.mulVec_sub, Matrix.mulVec_single, Pi.sub_apply, Pi.zero_apply,
      Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Matrix.col_apply] at h
    have hstar := congrArg star h
    simp only [star_sub, star_mul, star_star, star_zero, (hapsd j).isHermitian.apply] at hstar
    change a j k i = a j i i / v i * v k
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hi).mpr
    linear_combination hstar
  have hz0 : z ≠ 0 := by
    intro h
    have he := congrFun hz i
    rw [h, zero_smul] at he
    exact hj he
  refine ⟨fun k t => (if k = 0 then z⁻¹ else 1) * s j k t (i k), ?_⟩
  funext k
  symm
  calc
    _ = z⁻¹ * a j k i := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
      rfl
    _ = z⁻¹ * (z * v k) := by
      rw [congrFun hz k]
      rfl
    _ = v k := inv_mul_cancel_left₀ hz0 (v k)

private theorem fourier_not_product (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (a : ZMod d) (r : jointIndex n d)
    (hr : r 0 = 0) :
    ¬ ∃ f : Fin n → ZMod d → ℂ, fourierVector a r = fun i => ∏ k, f k (i k) := by
  classical
  rintro ⟨f, hf⟩
  let i := sectorPoint (0 : ZMod d) r
  let j := sectorPoint (1 : ZMod d) r
  let q := Function.update i 0 (j 0)
  let p := Function.update j 0 (i 0)
  have hi : i = sectorPoint (i 0) r := by
    change sectorPoint 0 r = sectorPoint (0 + r 0) r
    rw [hr, add_zero]
  have hj : j = sectorPoint (j 0) r := by
    change sectorPoint 1 r = sectorPoint (1 + r 0) r
    rw [hr, add_zero]
  have hq0 : q 0 = 1 := by
    change Function.update i 0 (j 0) 0 = 1
    rw [Function.update_self]
    change 1 + r 0 = 1
    rw [hr, add_zero]
  have hq : q ≠ sectorPoint (q 0) r := by
    intro h
    let k : Fin n := ⟨1, by omega⟩
    have hk : k ≠ 0 := by
      intro hk
      have := congrArg Fin.val hk
      change 1 = 0 at this
      omega
    have hval := congrFun h k
    change Function.update i 0 (j 0) k = q 0 + r k at hval
    rw [Function.update_of_ne hk, hq0] at hval
    change 0 + r k = 1 + r k at hval
    have h10 : (1 : ZMod d) = 0 := (add_right_cancel hval).symm
    have := ZMod.one_eq_zero_iff.mp h10
    omega
  have hsqrt : (Real.sqrt d : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply Real.sqrt_ne_zero'.mpr
    exact_mod_cast (show 0 < d by omega)
  have hnonzero : ∀ t, t = sectorPoint (t 0) r → fourierVector a r t ≠ 0 := by
    intro t ht
    change (if t = sectorPoint (t 0) r then
      (Real.sqrt d : ℂ)⁻¹ * ZMod.stdAddChar (a * t 0) else 0) ≠ 0
    rw [ite_eq_left ht, ZMod.stdAddChar_apply]
    exact mul_ne_zero (inv_ne_zero hsqrt) (Circle.coe_ne_zero _)
  have hminor : fourierVector a r i * fourierVector a r j =
      fourierVector a r q * fourierVector a r p := by
    rw [hf]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    by_cases hk : k = 0
    · subst k
      change f 0 (i 0) * f 0 (j 0) =
        f 0 (Function.update i 0 (j 0) 0) * f 0 (Function.update j 0 (i 0) 0)
      rw [Function.update_self, Function.update_self, mul_comm]
    · change f k (i k) * f k (j k) =
        f k (Function.update i 0 (j 0) k) * f k (Function.update j 0 (i 0) k)
      rw [Function.update_of_ne hk, Function.update_of_ne hk]
  have hqzero : fourierVector a r q = 0 := by
    change (if q = sectorPoint (q 0) r then _ else 0) = 0
    exact ite_eq_right hq
  rw [hqzero, zero_mul] at hminor
  exact mul_ne_zero (hnonzero i hi) (hnonzero j hj) hminor

private theorem selected_separable_iff (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d)) (b : jointIndex n d) :
    IsFullySeparable (selectedMeasurement r b) ↔ (Function.update b 0 0) ∈ r := by
  classical
  by_cases hb : (Function.update b 0 0) ∈ r
  · refine ⟨fun _ => hb, fun _ => ?_⟩
    change IsFullySeparable (Matrix.vecMulVec (selectedVector r b) (star (selectedVector r b)))
    have hvec : selectedVector r b = (Pi.single (sectorPoint (b 0) (Function.update b 0 0)) 1) :=
      ite_eq_left hb
    rw [hvec]
    exact computational_projector_separable _ _
  · refine ⟨fun hsep => ?_, fun h => (hb h).elim⟩
    have hvec : selectedVector r b = fourierVector (b 0) (Function.update b 0 0) := ite_eq_right hb
    change IsFullySeparable (Matrix.vecMulVec (selectedVector r b) (star (selectedVector r b))) at hsep
    rw [hvec] at hsep
    have hv := sector_basis n d hn hd (b 0) (b 0) (Function.update b 0 0) (Function.update b 0 0)
      (Function.update_self 0 0 b) (Function.update_self 0 0 b)
    rw [ite_eq_left ⟨rfl, rfl⟩] at hv
    exact (fourier_not_product n d hn hd (b 0) (Function.update b 0 0) (Function.update_self 0 0 b)
      (rankOne_separable_product n d _ hv hsep)).elim

private theorem sectorLabel_replace {n d : ℕ} [NeZero n] (s : jointIndex n d)
    (hs : s 0 = 0) (a : ZMod d) : (Function.update (Function.update s 0 a) 0 0) = s := by
  classical
  rw [Function.update_idem, ← hs, Function.update_eq_self]

private theorem replace_sectorLabel {n d : ℕ} [NeZero n] (b : jointIndex n d) :
    Function.update (Function.update b 0 0) 0 (b 0) = b := by
  classical
  rw [Function.update_idem, Function.update_eq_self]

private theorem sector_count (n d : ℕ) [NeZero n] [NeZero d]
    (_hn : 2 ≤ n) (_hd : 2 ≤ d) (r : Finset (jointIndex n d))
    (hr : ∀ s ∈ r, s 0 = 0) :
    (Finset.univ.filter (fun b => (Function.update b 0 0) ∈ r)).card = d * r.card := by
  classical
  let e : {b : jointIndex n d // b ∈ Finset.univ.filter (fun b => (Function.update b 0 0) ∈ r)} ≃
      ZMod d × {s : jointIndex n d // s ∈ r} :=
    { toFun := fun b => (b.1 0, ⟨(Function.update b.1 0 0), (Finset.mem_filter.mp b.2).2⟩)
      invFun := fun q => ⟨Function.update q.2.1 0 q.1, by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [sectorLabel_replace q.2.1 (hr q.2.1 q.2.2) q.1]
        exact q.2.2⟩
      left_inv := fun b => Subtype.ext (replace_sectorLabel b.1)
      right_inv := fun q => by
        apply Prod.ext
        · change Function.update q.2.1 0 q.1 0 = q.1
          exact Function.update_self _ _ _
        · apply Subtype.ext
          exact sectorLabel_replace q.2.1 (hr q.2.1 q.2.2) q.1 }
  have h := Fintype.card_congr e
  rw [Fintype.card_coe, Fintype.card_prod, ZMod.card, Fintype.card_coe] at h
  exact h

private theorem sector_separability_count (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d))
    (hr : ∀ s ∈ r, s 0 = 0) :
    (letI : DecidablePred (fun b => IsFullySeparable (selectedMeasurement r b)) := Classical.decPred _;
      (Finset.univ.filter (fun b => IsFullySeparable (selectedMeasurement r b))).card = d * r.card) := by
  classical
  have heq : (Finset.univ.filter (fun b => IsFullySeparable (selectedMeasurement r b))) =
      Finset.univ.filter (fun b => (Function.update b 0 0) ∈ r) := by
    exact Finset.filter_congr (fun b _ => selected_separable_iff n d hn hd r b)
  rw [heq]
  exact sector_count n d hn hd r hr

private theorem choose_sectors (n d m : ℕ) [NeZero n] [NeZero d]
    (_hn : 2 ≤ n) (hm : m ≤ d ^ (n - 1)) :
    ∃ r : Finset (jointIndex n d), r.card = m ∧ ∀ s ∈ r, s 0 = 0 := by
  classical
  let s : Finset (jointIndex n d) := Finset.univ.filter (fun r => r 0 = 0)
  let e : {r : jointIndex n d // r ∈ s} ≃ ({k : Fin n // k ≠ 0} → ZMod d) := by
    refine (Equiv.subtypeEquivRight ?_).trans
      (Equiv.subtypePreimage (fun k : Fin n => k = 0) (fun _ => (0 : ZMod d)))
    intro r
    simp -congrConsts only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hr
      funext k
      simpa -congrConsts only [Function.comp_apply, k.property] using hr
    · intro h
      exact congrFun h ⟨0, rfl⟩
  have hc : Fintype.card {k : Fin n // k ≠ 0} = n - 1 := by
    simpa only [Fintype.card_fin, Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun k : Fin n => k = 0)
  have hs : s.card = d ^ (n - 1) := by
    have h := Fintype.card_congr e
    rw [Fintype.card_coe, Fintype.card_fun, ZMod.card, hc] at h
    exact h
  obtain ⟨r, hrs, hcard⟩ := Finset.exists_subset_card_eq (s := s) (hs.symm ▸ hm)
  exact ⟨r, hcard, fun t ht => (Finset.mem_filter.mp (hrs ht)).2⟩

private theorem encoding_entry (n d : ℕ) [NeZero d] (k : Fin n) (x y i j : ZMod d) :
    localEncoding n d k x y i j =
      if j = i - y then ZMod.stdAddChar (x * i) else 0 := by
  classical
  change (clockMatrix d ^ x.val * shiftMatrix d ^ y.val) i j = _
  rw [clockMatrix, Matrix.diagonal_pow, Matrix.diagonal_mul,
    D5.S3.Observer.MatrixUnitCertificate.shift_matrix_pow_apply]
  have hphase : (windowRoot d ^ i.val) ^ x.val = ZMod.stdAddChar (x * i) := by
    simpa only [D5.S3.Fourier.FinitePoisson.character_apply] using
      D5.S3.Observer.MatrixUnitCertificate.clock_phase_pow_eq_character i x
  simp only [Pi.pow_apply]
  rw [hphase, ZMod.natCast_zmod_val]
  by_cases h : j = i - y
  · rw [ite_eq_left h, ite_eq_left (by rw [h]; abel), mul_one]
  · rw [ite_eq_right h, ite_eq_right (by intro q; apply h; linear_combination -q), mul_zero]

private theorem encoded_ghz (n d : ℕ) [NeZero n] [NeZero d]
    (_hn : 2 ≤ n) (_hd : 2 ≤ d) (x y : jointIndex n d) :
    ∃ z : ℂ, Complex.normSq z = 1 ∧
      tensorMatrix (localEncoding n d) x y *ᵥ fourierVector 0 (0 : jointIndex n d) =
        z • fourierVector (∑ k, x k) (sectorCoordinate y) := by
  classical
  have htensor (i j : jointIndex n d) :
      tensorMatrix (localEncoding n d) x y i j =
        if j = (fun k => i k - y k) then ZMod.stdAddChar (∑ k, x k * i k) else 0 := by
    change (∏ k, localEncoding n d k (x k) (y k) (i k) (j k)) = _
    by_cases hj : j = (fun k => i k - y k)
    · rw [ite_eq_left hj]
      subst j
      calc
        _ = ∏ k, ZMod.stdAddChar (x k * i k) := by
          apply Finset.prod_congr rfl
          intro k _
          rw [encoding_entry, ite_eq_left rfl]
        _ = _ := (congrArg Additive.toMul
          (map_sum (ZMod.stdAddChar (N := d)).toAddMonoidHom
            (fun k => x k * i k) Finset.univ)).symm
    · rw [ite_eq_right hj]
      obtain ⟨k, hk⟩ : ∃ k, j k ≠ i k - y k := by
        by_contra! h
        exact hj (funext h)
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      rw [encoding_entry, ite_eq_right hk]
  refine ⟨ZMod.stdAddChar (∑ k, x k * (y k - y 0)), ?_, ?_⟩
  · rw [ZMod.stdAddChar_apply]
    exact Circle.normSq_coe _
  · funext i
    have hact : (tensorMatrix (localEncoding n d) x y *ᵥ
        fourierVector 0 (0 : jointIndex n d)) i =
        ZMod.stdAddChar (∑ k, x k * i k) *
          fourierVector 0 (0 : jointIndex n d) (fun k => i k - y k) := by
      change (∑ j, tensorMatrix (localEncoding n d) x y i j *
        fourierVector 0 (0 : jointIndex n d) j) = _
      rw [Finset.sum_eq_single (fun k => i k - y k)]
      · rw [htensor, ite_eq_left rfl]
      · intro j _ hj
        rw [htensor, ite_eq_right hj, zero_mul]
      · exact fun h => (h (Finset.mem_univ _)).elim
    rw [hact]
    change _ = ZMod.stdAddChar (∑ k, x k * (y k - y 0)) *
      (if i = sectorPoint (i 0) (sectorCoordinate y) then
        (Real.sqrt d : ℂ)⁻¹ * ZMod.stdAddChar ((∑ k, x k) * i 0) else 0)
    have hsector : (fun k => i k - y k) =
        sectorPoint ((fun k => i k - y k) 0) (0 : jointIndex n d) ↔
        i = sectorPoint (i 0) (sectorCoordinate y) := by
      constructor <;> intro h <;> funext k
      · have hk := congrFun h k
        change i k - y k = i 0 - y 0 + 0 at hk
        change i k = i 0 + (y k - y 0)
        linear_combination hk
      · have hk := congrFun h k
        change i k = i 0 + (y k - y 0) at hk
        change i k - y k = i 0 - y 0 + 0
        linear_combination hk
    change ZMod.stdAddChar (∑ k, x k * i k) *
      (if (fun k => i k - y k) = sectorPoint (i 0 - y 0) (0 : jointIndex n d) then
        (Real.sqrt d : ℂ)⁻¹ * ZMod.stdAddChar (0 * (i 0 - y 0)) else 0) = _
    by_cases hi : i = sectorPoint (i 0) (sectorCoordinate y)
    · rw [ite_eq_left hi, ite_eq_left (hsector.mpr hi), zero_mul,
        AddChar.map_zero_eq_one, mul_one]
      have hphase : (∑ k, x k * i k) =
          (∑ k, x k * (y k - y 0)) + (∑ k, x k) * i 0 := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        have hk : i k = i 0 + (y k - y 0) := congrFun hi k
        rw [hk]; ring
      rw [hphase, AddChar.map_add_eq_mul]
      ring
    · rw [ite_eq_right hi, ite_eq_right (fun h => hi (hsector.mp h)), mul_zero, mul_zero]

private theorem winning_probability (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d))
    (x y : jointIndex n d) :
    (Matrix.trace (tensorMatrix (localEncoding n d) x y * ghzDensity n d *
      (tensorMatrix (localEncoding n d) x y)ᴴ *
      selectedMeasurement r (winningOutcome x y))).re =
        if sectorCoordinate y ∈ r then (d : ℝ)⁻¹ else 1 := by
  classical
  obtain ⟨z, hz, hencoded⟩ := encoded_ghz n d hn hd x y
  have horth := sector_basis n d hn hd (∑ k, x k) (∑ k, x k)
    (sectorCoordinate y) (sectorCoordinate y) (sector_coordinates y).1 (sector_coordinates y).1
  rw [ite_eq_left ⟨rfl, rfl⟩] at horth
  have hzprod : z * star z = 1 := by
    calc
      _ = (Complex.normSq z : ℂ) := by
        rw [Complex.normSq_eq_conj_mul_self]
        exact mul_comm _ _
      _ = 1 := by rw [hz, Complex.ofReal_one]
  have hstate : tensorMatrix (localEncoding n d) x y * ghzDensity n d *
      (tensorMatrix (localEncoding n d) x y)ᴴ =
      Matrix.vecMulVec (fourierVector (∑ k, x k) (sectorCoordinate y))
        (star (fourierVector (∑ k, x k) (sectorCoordinate y))) := by
    change tensorMatrix (localEncoding n d) x y *
      Matrix.vecMulVec (fourierVector 0 (0 : jointIndex n d))
        (star (fourierVector 0 (0 : jointIndex n d))) *
        (tensorMatrix (localEncoding n d) x y)ᴴ = _
    rw [D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment.conjugate_outer,
      hencoded]
    ext i j
    change (z * fourierVector (∑ k, x k) (sectorCoordinate y) i) *
      star (z * fourierVector (∑ k, x k) (sectorCoordinate y) j) = _
    rw [star_mul]
    calc
      _ = (z * star z) * (fourierVector (∑ k, x k) (sectorCoordinate y) i *
          star (fourierVector (∑ k, x k) (sectorCoordinate y) j)) := by ring
      _ = _ := by rw [hzprod, one_mul]; rfl
  have hhead : winningOutcome x y 0 = ∑ k, x k := by
    exact ite_eq_left rfl
  have hlabel : (Function.update (winningOutcome x y) 0 0) = sectorCoordinate y := by
    funext k
    by_cases hk : k = 0
    · subst k
      rw [Function.update_self]
      exact (sector_coordinates y).1.symm
    · rw [Function.update_of_ne hk]
      change (if k = 0 then ∑ t, x t else y k - y 0) = y k - y 0
      exact ite_eq_right hk
  have htrace (v : jointIndex n d → ℂ) :
      Matrix.trace (Matrix.vecMulVec (fourierVector (∑ k, x k) (sectorCoordinate y))
        (star (fourierVector (∑ k, x k) (sectorCoordinate y))) *
          Matrix.vecMulVec v (star v)) =
      (star (fourierVector (∑ k, x k) (sectorCoordinate y)) ⬝ᵥ v) *
        (star v ⬝ᵥ fourierVector (∑ k, x k) (sectorCoordinate y)) := by
    rw [show Matrix.trace (Matrix.vecMulVec
        (fourierVector (∑ k, x k) (sectorCoordinate y))
        (star (fourierVector (∑ k, x k) (sectorCoordinate y))) *
        Matrix.vecMulVec v (star v)) =
        (Complex.normSq (star (fourierVector (∑ k, x k) (sectorCoordinate y)) ⬝ᵥ v) : ℂ) from
      D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.trace_projector_overlap
        (fourierVector (∑ k, x k) (sectorCoordinate y)) v]
    rw [Complex.normSq_eq_conj_mul_self]
    change star (star (fourierVector (∑ k, x k) (sectorCoordinate y)) ⬝ᵥ v) *
      (star (fourierVector (∑ k, x k) (sectorCoordinate y)) ⬝ᵥ v) = _
    rw [← Matrix.star_dotProduct v _, mul_comm]
  rw [hstate]
  change (Matrix.trace (_ * Matrix.vecMulVec
    (selectedVector r (winningOutcome x y)) (star (selectedVector r (winningOutcome x y))))).re = _
  rw [htrace]
  have hvec : selectedVector r (winningOutcome x y) =
      if sectorCoordinate y ∈ r then (Pi.single (sectorPoint (∑ k, x k) (sectorCoordinate y)) 1)
      else fourierVector (∑ k, x k) (sectorCoordinate y) := by
    change (if (Function.update (winningOutcome x y) 0 0) ∈ r then
      (Pi.single (sectorPoint (winningOutcome x y 0) ((Function.update (winningOutcome x y) 0 0))) 1)
      else fourierVector (winningOutcome x y 0) ((Function.update (winningOutcome x y) 0 0))) = _
    rw [hhead, hlabel]
  rw [hvec]
  by_cases hy : sectorCoordinate y ∈ r
  · rw [ite_eq_left hy, ite_eq_left hy, star_dotProduct, Pi.star_single, star_one, single_one_dotProduct,
      fourier_at_point _ _ _ (sector_coordinates y).1]
    have hchar : star (ZMod.stdAddChar ((∑ k, x k) * (∑ k, x k))) *
        ZMod.stdAddChar ((∑ k, x k) * (∑ k, x k)) = 1 := by
      simpa -congrConsts only
        [RCLike.star_def, AddChar.norm_apply, one_pow, Complex.ofReal_one] using
        Complex.conj_mul' (ZMod.stdAddChar ((∑ k, x k) * (∑ k, x k)))
    have hsstar : star (Real.sqrt d : ℂ) = (Real.sqrt d : ℂ) := Complex.conj_ofReal _
    have hsq : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    have hamp : star ((Real.sqrt d : ℂ)⁻¹ *
        ZMod.stdAddChar ((∑ k, x k) * (∑ k, x k))) *
        ((Real.sqrt d : ℂ)⁻¹ * ZMod.stdAddChar ((∑ k, x k) * (∑ k, x k))) =
        (d : ℂ)⁻¹ := by
      simp only [star_mul, star_inv₀, hsstar]
      calc
        _ = ((Real.sqrt d : ℂ)⁻¹ * (Real.sqrt d : ℂ)⁻¹) *
            (star (ZMod.stdAddChar ((∑ k, x k) * (∑ k, x k))) *
              ZMod.stdAddChar ((∑ k, x k) * (∑ k, x k))) := by ring
        _ = _ := by rw [hchar, mul_one, ← _root_.mul_inv_rev, hsq]
    rw [hamp]
    exact congrArg Complex.re (Complex.ofReal_inv (d : ℝ)).symm
  · rw [ite_eq_right hy, ite_eq_right hy, horth, one_mul]
    rfl

private theorem sector_score (n d : ℕ) [NeZero n] [NeZero d]
    (hn : 2 ≤ n) (hd : 2 ≤ d) (r : Finset (jointIndex n d))
    (hr : ∀ s ∈ r, s 0 = 0) :
    score (ghzDensity n d) (localEncoding n d) (selectedMeasurement r) =
      ((d : ℝ) ^ n - d * r.card + r.card) / (d : ℝ) ^ n := by
  classical
  have hprob := winning_probability n d hn hd r
  have hcount := sector_count n d hn hd r hr
  let e : jointIndex n d ≃ jointIndex n d :=
    { toFun := fun b => sectorPoint (b 0) (Function.update b 0 0)
      invFun := fun i => Function.update (sectorCoordinate i) 0 (i 0)
      left_inv := fun b => by
        funext k
        change Function.update (sectorCoordinate (sectorPoint (b 0) (Function.update b 0 0)))
          0 (sectorPoint (b 0) (Function.update b 0 0) 0) k = b k
        by_cases hk : k = 0
        · subst k
          rw [Function.update_self]
          change b 0 + (Function.update b 0 0) 0 = b 0
          rw [Function.update_self, add_zero]
        · rw [Function.update_of_ne hk]
          change (b 0 + (Function.update b 0 0) k) - (b 0 + (Function.update b 0 0) 0) = b k
          rw [Function.update_self, add_zero]
          rw [Function.update_of_ne hk]
          abel
      right_inv := fun i => by
        funext k
        change Function.update (sectorCoordinate i) 0 (i 0) 0 +
          (Function.update (Function.update (sectorCoordinate i) 0 (i 0)) 0 0) k = i k
        rw [Function.update_self]
        by_cases hk : k = 0
        · subst k
          rw [Function.update_self, add_zero]
        · rw [Function.update_of_ne hk, Function.update_of_ne hk]
          change i 0 + (i k - i 0) = i k
          abel }
  have hcoordinate (b : jointIndex n d) : sectorCoordinate (e b) = (Function.update b 0 0) := by
    funext k
    change (b 0 + (Function.update b 0 0) k) - (b 0 + (Function.update b 0 0) 0) = (Function.update b 0 0) k
    rw [Function.update_self, add_zero]
    abel
  have hreindex : (∑ y, if sectorCoordinate y ∈ r then (d : ℝ)⁻¹ else 1) =
      ∑ b : jointIndex n d, if (Function.update b 0 0) ∈ r then (d : ℝ)⁻¹ else 1 := by
    rw [← e.sum_comp (fun y => if sectorCoordinate y ∈ r then (d : ℝ)⁻¹ else 1)]
    apply Finset.sum_congr rfl
    intro b _
    rw [hcoordinate]
  have hc : ((Finset.univ : Finset (jointIndex n d)).card : ℝ) = (d : ℝ) ^ n := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card,
      Nat.cast_pow]
  have hcomplement := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (jointIndex n d))) (fun b => (Function.update b 0 0) ∈ r)
  have hcomplementReal :
      ((Finset.univ.filter (fun b : jointIndex n d => (Function.update b 0 0) ∉ r)).card : ℝ) =
        (d : ℝ) ^ n - d * r.card := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hcomplement
    rw [Nat.cast_add, hcount, Nat.cast_mul, hc] at h
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)
  have hsum : (∑ y, if sectorCoordinate y ∈ r then (d : ℝ)⁻¹ else 1) =
      d * r.card * (d : ℝ)⁻¹ + ((d : ℝ) ^ n - d * r.card) := by
    rw [hreindex, Finset.sum_ite]
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      mul_one, hcount, Nat.cast_mul, hcomplementReal]
  change ((d : ℝ) ^ (2 * n))⁻¹ * ∑ x, ∑ y, _ = _
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hprob x y))]
  rw [hsum, Finset.sum_const, nsmul_eq_mul, hc]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [show 2 * n = n + n by omega, pow_add]
  field_simp [hd0]
  ring

theorem result : claim := by
  intro n d m hn hd hm
  let : NeZero n := neZeroOfTwo n hn
  let : NeZero d := neZeroOfTwo d hd
  obtain ⟨r, hcard, hr⟩ := choose_sectors n d m hn hm
  refine ⟨ghzDensity n d, localEncoding n d, selectedMeasurement r,
    ghz_density n d hn hd, encodings_unitary n d,
    sector_measurement n d hn hd r, ?_, ?_⟩
  · exact hcard ▸ sector_separability_count n d hn hd r hr
  · exact hcard ▸ sector_score n d hn hd r hr

end D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness
