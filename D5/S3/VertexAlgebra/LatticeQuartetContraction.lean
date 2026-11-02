/- GID: D5/S3/VertexAlgebra/LatticeQuartetContraction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeQuartetContraction
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Actual all-frequency tensor quartet contraction by its inverse count. -/

import D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
import D5.S3.Quantum.Fermionic.BcGhostQuartetCount
import D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Rename

set_option autoImplicit false
noncomputable section

namespace D5.S3.VertexAlgebra.LatticeQuartetContraction

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeLightConeCoordinates
open NullFrame MvPolynomial
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open scoped BigOperators TensorProduct

namespace GC
export D5.S3.Quantum.Fermionic.BcGhostQuartetCount
  (U U_pos U_ket localCount count sum_localCount count_zero_iff
   b_positive c_negative b_negative_ge_two c_positive_ge_two
   b_negative_one c_positive_one b_zero occupied capture site_capture ket_expansion)
end GC

abbrev State (D : LatticeData) := Carrier D ⊗[ℂ] Fock

variable {D : LatticeData}

def tp (A : Module.End ℂ (Carrier D)) (G : Module.End ℂ Fock) :
    Module.End ℂ (State D) := TensorProduct.map A G

@[simp] theorem tp_tmul (A : Module.End ℂ (Carrier D)) (G : Module.End ℂ Fock)
    (v : Carrier D) (w : Fock) : tp A G (v ⊗ₜ w) = A v ⊗ₜ G w := rfl

theorem tensor_sub_left (A B : Module.End ℂ (Carrier D)) (G : Module.End ℂ Fock) :
    TensorProduct.map (A-B) G = TensorProduct.map A G - TensorProduct.map B G := by
  ext v w
  simp [TensorProduct.sub_tmul]
theorem tensor_sub_right (A : Module.End ℂ (Carrier D)) (G H : Module.End ℂ Fock) :
    TensorProduct.map A (G-H) = TensorProduct.map A G - TensorProduct.map A H := by
  ext v w
  simp [TensorProduct.tmul_sub]

theorem tp_ac (A B : Module.End ℂ (Carrier D)) (G H : Module.End ℂ Fock) :
    ac (tp A G) (tp B H) =
      tp (A * B - B * A) (G * H) + tp (B * A) (G * H + H * G) := by
  unfold ac tp
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
  simp only [tensor_sub_left, TensorProduct.map_add_right]
  abel

theorem tp_zero_ac (A B : Module.End ℂ (Carrier D)) (G H : Module.End ℂ Fock)
    (hAB : A * B - B * A = 0) (hGH : G * H + H * G = 0) :
    ac (tp A G) (tp B H) = 0 := by
  rw [tp_ac, hAB, hGH]
  simp [tp]

/-- Bilinear extension of the pinned original Heisenberg law. -/
theorem a_heisenberg (u v : E D) (m n : ℤ) :
    a u m * a v n - a v n * a u m =
      (if m+n=0 then (m : ℂ) * g D u v else 0) • (1 : Module.End ℂ (Carrier D)) := by
  classical
  have expand (u v : E D) (m n : ℤ) :
      a u m * a v n = ∑ i, ∑ j,
        (u i * v j) • (neutralMode D i m * neutralMode D j n) := by
    simp only [a, Finset.sum_mul, Finset.mul_sum, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, Finset.smul_sum, smul_smul]
  calc
    _ = ∑ i, ∑ j, (u i * v j) •
        (neutralMode D i m * neutralMode D j n - neutralMode D j n * neutralMode D i m) := by
      rw [expand, expand]
      conv_lhs => rhs; rw [Finset.sum_comm]
      simp only [smul_sub, Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_comm (v j) (u i)]
    _ = _ := by
      simp_rw [neutralMode_heisenberg]
      by_cases h : m+n=0
      · simp only [if_pos h, smul_smul, ← Finset.sum_smul]
        congr 1
        simp only [g, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      · simp [h]

variable (F : NullFrame D)

def dm (n : ℤ) : Module.End ℂ (State D) := tp (a F.eMinus n) (c (-n))
def rr (n : ℤ) : Module.End ℂ (State D) := tp (a F.ePlus (-n)) (b n)

theorem dm_dm (m n : ℤ) : ac (dm F m) (dm F n) = 0 := by
  apply tp_zero_ac
  · simp [a_heisenberg, F.minus_null]
  · exact ghost_c_car (-m) (-n)

theorem rr_rr (m n : ℤ) : ac (rr F m) (rr F n) = 0 := by
  apply tp_zero_ac
  · simp [a_heisenberg, F.plus_null]
  · exact ghost_b_car m n

/-- This identity is on the original tensor carrier at every integer mode. -/
theorem dm_rr (m n : ℤ) :
    ac (dm F m) (rr F n) = if m = n then
      (m : ℂ) • tp 1 (c (-m) * b m) + tp (a F.ePlus (-m) * a F.eMinus m) 1
      else 0 := by
  rw [dm, rr, tp_ac, a_heisenberg]
  have hcar : c (-m) * b n + b n * c (-m) =
      if n-m=0 then (1 : Module.End ℂ Fock) else 0 := by
    simpa only [sub_eq_add_neg, add_comm] using ghost_mixed_car n (-m)
  rw [hcar]
  by_cases h : m = n
  · subst n
    simp [F.minus_plus, tp, TensorProduct.map_smul_left]
  · have hmn : m + -n ≠ 0 := by omega
    have hnm : n-m ≠ 0 := by omega
    simp [h, hmn, hnm, tp]

/-- r labels frequency k=r+1; no zero or signed denominator is used. -/
def dTerm (r : ℕ) : Module.End ℂ (State D) :=
  dm F ((r : ℤ)+1) + dm F (-((r : ℤ)+1))
def rTerm (r : ℕ) : Module.End ℂ (State D) :=
  ((r+1 : ℂ)⁻¹) • (rr F ((r : ℤ)+1) + rr F (-((r : ℤ)+1)))
def numberTerm (r : ℕ) : Module.End ℂ (State D) :=
  ((r+1 : ℂ)⁻¹) • tp
    (a F.ePlus (-((r : ℤ)+1)) * a F.eMinus ((r : ℤ)+1) +
     a F.eMinus (-((r : ℤ)+1)) * a F.ePlus ((r : ℤ)+1)) 1 +
    tp 1 (GC.U (r+1))

theorem original_single_frequency (r : ℕ) :
    ac (dTerm F r) (rTerm F r) = numberTerm F r := by
  let k : ℤ := (r : ℤ)+1
  let z : ℂ := r+1
  have hz : z ≠ 0 := by dsimp [z]; exact_mod_cast Nat.succ_ne_zero r
  have hk : k ≠ -k := by dsimp [k]; omega
  have hcomm := a_heisenberg F.ePlus F.eMinus k (-k)
  have hcomm' : a F.ePlus k * a F.eMinus (-k) =
      a F.eMinus (-k) * a F.ePlus k + z • 1 := by
    have hh : a F.ePlus k * a F.eMinus (-k) -
        a F.eMinus (-k) * a F.ePlus k = z • 1 := by
      simpa [k, z, F.plus_minus] using hcomm
    calc
      _ = a F.eMinus (-k) * a F.ePlus k +
          (a F.ePlus k * a F.eMinus (-k) - a F.eMinus (-k) * a F.ePlus k) := by abel
      _ = _ := by rw [hh]
  have hcar : c k * b (-k) = 1 - b (-k) * c k := by
    have hh := ghost_mixed_car (-k) k
    have hh' : b (-k) * c k + c k * b (-k) = 1 := by simpa using hh
    calc
      _ = (b (-k) * c k + c k * b (-k)) - b (-k) * c k := by abel
      _ = _ := by rw [hh']
  have hU : GC.U (r+1) = c (-k) * b k + b (-k) * c k := by
    simpa [k, Nat.cast_add, Nat.cast_one] using GC.U_pos (r+1) (by omega)
  simp only [dTerm, rTerm, ac_smul_right, ac_add_left, ac_add_right, dm_rr]
  simp only [show (r : ℤ)+1 ≠ -((r : ℤ)+1) by omega,
    show -((r : ℤ)+1) ≠ (r : ℤ)+1 by omega, if_true, if_false, add_zero, zero_add, neg_neg]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
  change z⁻¹ • ((z • tp 1 (c (-k) * b k) +
    tp (a F.ePlus (-k) * a F.eMinus k) 1) +
    ((-z) • tp 1 (c k * b (-k)) + tp (a F.ePlus k * a F.eMinus (-k)) 1)) = _
  rw [hcomm', hcar]
  simp only [tp, TensorProduct.map_add_left, tensor_sub_right,
    TensorProduct.map_smul_left, TensorProduct.map_one]
  rw [numberTerm, hU]
  simp only [tp, TensorProduct.map_add_left, TensorProduct.map_add_right]
  simp only [smul_add, smul_sub, smul_smul, mul_neg, inv_mul_cancel₀ hz, one_smul,
    neg_smul, sub_eq_add_neg]
  abel

theorem distinct_frequencies (r s : ℕ) (hrs : r ≠ s) :
    ac (dTerm F r) (rTerm F s) = 0 := by
  simp only [dTerm, rTerm, ac_smul_right, ac_add_left, ac_add_right, dm_rr]
  have h1 : (r : ℤ)+1 ≠ (s : ℤ)+1 := by omega
  have h2 : (r : ℤ)+1 ≠ -((s : ℤ)+1) := by omega
  have h3 : -((r : ℤ)+1) ≠ (s : ℤ)+1 := by omega
  have h4 : -((r : ℤ)+1) ≠ -((s : ℤ)+1) := by omega
  simp [h1, h2, h3, h4]

theorem dTerm_rTerm (r s : ℕ) : ac (dTerm F r) (rTerm F s) =
    if r = s then numberTerm F r else 0 := by
  by_cases h : r = s
  · subst s; simpa using original_single_frequency F r
  · simpa [h] using distinct_frequencies F r s h

theorem dTerm_dTerm (r s : ℕ) : ac (dTerm F r) (dTerm F s) = 0 := by
  simp only [dTerm, ac_add_left, ac_add_right, dm_dm, add_zero]
theorem rTerm_rTerm (r s : ℕ) : ac (rTerm F r) (rTerm F s) = 0 := by
  simp only [rTerm, ac_smul_left, ac_smul_right, ac_add_left, ac_add_right,
    rr_rr, add_zero, smul_zero]

theorem a_positive_vanish (u : E D) (v : Carrier D) (k : ℕ)
    (hk : vectorFrequencyBound D v < k) : a u (k : ℤ) v = 0 := by
  classical
  simp only [a, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [neutralMode_vanish D i v (k : ℤ) (by exact_mod_cast hk), smul_zero]

theorem positive_ghosts_vanish (w : Fock) (k : ℕ) (hk : GC.capture w ≤ k) :
    b (k : ℤ) w = 0 ∧ c (k : ℤ) w = 0 := by
  classical
  have hk3 : 3 ≤ k := by unfold GC.capture at hk; omega
  have hv (j : ℕ) (hj : ∀ S ∈ w.support, j ∉ S) : annihilate j w = 0 := by
    rw [← GC.ket_expansion w]
    simp only [map_sum, map_smul]
    apply Finset.sum_eq_zero
    intro S hS
    simp [annihilate_ket, hj S hS]
  constructor
  · rw [GC.b_positive]
    apply hv
    intro S hS hj
    have hh := (GC.site_capture w S hS _ hj).trans hk
    omega
  · rw [GC.c_positive_ge_two k (by omega)]
    apply hv
    intro S hS hj
    have hh := (GC.site_capture w S hS _ hj).trans hk
    omega

/-- The four individual summands, not merely their sums, have actual captures. -/
theorem four_modes_tmul_vanish (v : Carrier D) (w : Fock) (r : ℕ)
    (hr : max (vectorFrequencyBound D v + 1) (GC.capture w) ≤ r) :
    dm F ((r : ℤ)+1) (v ⊗ₜ w) = 0 ∧
    dm F (-((r : ℤ)+1)) (v ⊗ₜ w) = 0 ∧
    rr F ((r : ℤ)+1) (v ⊗ₜ w) = 0 ∧
    rr F (-((r : ℤ)+1)) (v ⊗ₜ w) = 0 := by
  have ha (u : E D) : a u ((r : ℤ)+1) v = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      a_positive_vanish u v (r+1) (by omega)
  have hg := positive_ghosts_vanish w (r+1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one] at hg
  simp [dm, rr, ha, hg.1, hg.2]

theorem four_modes_capture (v : State D) : ∃ N : ℕ, ∀ r, N ≤ r →
    dm F ((r : ℤ)+1) v = 0 ∧ dm F (-((r : ℤ)+1)) v = 0 ∧
    rr F ((r : ℤ)+1) v = 0 ∧ rr F (-((r : ℤ)+1)) v = 0 := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, by intros; simp⟩
  | tmul v w => exact ⟨_, fun r hr => four_modes_tmul_vanish F v w r hr⟩
  | add v w hv hw =>
    obtain ⟨Nv, hv⟩ := hv
    obtain ⟨Nw, hw⟩ := hw
    refine ⟨max Nv Nw, ?_⟩
    intro r hr
    obtain ⟨h1,h2,h3,h4⟩ := hv r (by omega)
    obtain ⟨h5,h6,h7,h8⟩ := hw r (by omega)
    simp [map_add, h1,h2,h3,h4,h5,h6,h7,h8]

def modeBound (v : State D) : ℕ := Classical.choose (four_modes_capture F v)

theorem modeBound_spec (v : State D) (r : ℕ) (hr : modeBound F v ≤ r) :
    dm F ((r : ℤ)+1) v = 0 ∧ dm F (-((r : ℤ)+1)) v = 0 ∧
    rr F ((r : ℤ)+1) v = 0 ∧ rr F (-((r : ℤ)+1)) v = 0 :=
  Classical.choose_spec (four_modes_capture F v) r hr

def dFamily : Family (State D) :=
  ⟨dTerm F, modeBound F, by
    intro v r hr
    obtain ⟨h1,h2,h3,h4⟩ := modeBound_spec F v r hr
    simp [dTerm, h1, h2]⟩
def rFamily : Family (State D) :=
  ⟨rTerm F, modeBound F, by
    intro v r hr
    obtain ⟨h1,h2,h3,h4⟩ := modeBound_spec F v r hr
    simp [rTerm, h3, h4]⟩
def numberFamily : Family (State D) :=
  ⟨numberTerm F, modeBound F, by
    intro v r hr
    have hd := (dFamily F).vanish v r hr
    have hh := (rFamily F).vanish v r hr
    have h := LinearMap.congr_fun (original_single_frequency F r) v
    simpa only [ac, LinearMap.add_apply, Module.End.mul_apply, hd, hh,
      map_zero, add_zero] using h.symm⟩

def unscaledD : Module.End ℂ (State D) := (dFamily F).total
def unscaledR : Module.End ℂ (State D) := (rFamily F).total
def M : Module.End ℂ (State D) := (numberFamily F).total
def d0 (p : Charge D) : Module.End ℂ (State D) := F.pPlus p • unscaledD F
def R (p : Charge D) : Module.End ℂ (State D) := (F.pPlus p)⁻¹ • unscaledR F

theorem unscaled_contraction : ac (unscaledD F) (unscaledR F) = M F :=
  Family.total_ac (dFamily F) (rFamily F) (numberFamily F) (dTerm_rTerm F)

theorem unscaledD_square : unscaledD F * unscaledD F = 0 :=
  Family.total_square_zero (dFamily F) (dTerm_dTerm F)
theorem unscaledR_square : unscaledR F * unscaledR F = 0 :=
  Family.total_square_zero (rFamily F) (rTerm_rTerm F)

theorem original_contraction (p : Charge D) (hp : F.pPlus p ≠ 0) :
    d0 F p * R F p + R F p * d0 F p = M F := by
  change ac (F.pPlus p • unscaledD F) ((F.pPlus p)⁻¹ • unscaledR F) = _
  rw [ac_smul_left, ac_smul_right, smul_smul, mul_inv_cancel₀ hp, one_smul]
  exact unscaled_contraction F

theorem d0_square (p : Charge D) : d0 F p * d0 F p = 0 := by
  simp [d0, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, unscaledD_square]
theorem R_square (p : Charge D) : R F p * R F p = 0 := by
  simp [R, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, unscaledR_square]

theorem M_commutes_d0 (p : Charge D) : M F * d0 F p = d0 F p * M F := by
  have h := unscaled_contraction F
  have hd := unscaledD_square F
  simp only [← h, ac, d0]
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  congr 1
  calc
    _ = unscaledD F * unscaledR F * unscaledD F +
      unscaledR F * (unscaledD F * unscaledD F) := by noncomm_ring
    _ = _ := by
      rw [hd]
      simp only [mul_zero, add_zero, mul_add, ← mul_assoc, hd, zero_mul, zero_add]

theorem M_commutes_R (p : Charge D) : M F * R F p = R F p * M F := by
  have h := unscaled_contraction F
  have hr := unscaledR_square F
  simp only [← h, ac, R]
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  congr 1
  calc
    _ = unscaledD F * (unscaledR F * unscaledR F) +
      unscaledR F * unscaledD F * unscaledR F := by noncomm_ring
    _ = _ := by
      rw [hr]
      simp only [mul_zero, zero_add, mul_add, ← mul_assoc, hr, zero_mul, add_zero]

/-- All raw integer summands have finite support, before any regrouping. -/
theorem signed_support (v : State D) :
    (Function.support (fun n : ℤ => if n=0 then 0 else dm F n v)).Finite ∧
    (Function.support (fun n : ℤ => if n=0 then 0 else
      ((n.natAbs : ℂ)⁻¹) • rr F n v)).Finite := by
  classical
  let N := modeBound F v
  let S := (Finset.range N).image (fun r : ℕ => (r : ℤ)+1) ∪
    (Finset.range N).image (fun r : ℕ => -((r : ℤ)+1))
  have hf (f : ℤ → State D) (h0 : f 0=0)
      (hN : ∀ r, N ≤ r → f ((r : ℤ)+1)=0 ∧ f (-((r : ℤ)+1))=0) :
      (Function.support f).Finite := by
    apply S.finite_toSet.subset
    intro z hz
    cases z with
    | ofNat n =>
      cases n with
      | zero => exact False.elim (hz h0)
      | succ r =>
        have hr : r < N := by by_contra h; exact hz (by simpa using (hN r (by omega)).1)
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, by omega⟩)
    | negSucc r =>
      have hr : r < N := by by_contra h; exact hz (by simpa using (hN r (by omega)).2)
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, by omega⟩)
  constructor
  · apply hf _ (by simp)
    intro r hr
    obtain ⟨h1,h2,h3,h4⟩ := modeBound_spec F v r hr
    simp [h1,h2, show (r : ℤ)+1 ≠ 0 by omega, show -((r : ℤ)+1) ≠ 0 by omega]
  · apply hf _ (by simp)
    intro r hr
    obtain ⟨h1,h2,h3,h4⟩ := modeBound_spec F v r hr
    simp [h3,h4, show (r : ℤ)+1 ≠ 0 by omega, show -((r : ℤ)+1) ≠ 0 by omega]

theorem d0_signed_formula (p : Charge D) (v : State D) :
    d0 F p v = F.pPlus p •
      ∑ᶠ n : ℤ, if n=0 then 0 else tp (a F.eMinus n) (c (-n)) v := by
  rw [d0, LinearMap.smul_apply, unscaledD,
    (dFamily F).total_eq_sum v (modeBound F v) le_rfl]
  rw [signed_sum _ (by simp) (modeBound F v) (by
    intro r hr
    obtain ⟨h1,h2,h3,h4⟩ := modeBound_spec F v r hr
    simp [← dm, h1,h2, show (r : ℤ)+1 ≠ 0 by omega, show -((r : ℤ)+1) ≠ 0 by omega])]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp [dFamily, dTerm, dm, show (r : ℤ)+1 ≠ 0 by omega,
    show -((r : ℤ)+1) ≠ 0 by omega]

/-- The denominator is natAbs at BOTH signs. -/
theorem R_signed_formula (p : Charge D) (v : State D) :
    R F p v = (F.pPlus p)⁻¹ • ∑ᶠ n : ℤ, if n=0 then 0 else
      ((n.natAbs : ℂ)⁻¹) • tp (a F.ePlus (-n)) (b n) v := by
  rw [R, LinearMap.smul_apply, unscaledR,
    (rFamily F).total_eq_sum v (modeBound F v) le_rfl]
  rw [signed_sum _ (by simp) (modeBound F v) (by
    intro r hr
    obtain ⟨h1,h2,h3,h4⟩ := modeBound_spec F v r hr
    simp [← rr, h3,h4, show (r : ℤ)+1 ≠ 0 by omega, show -((r : ℤ)+1) ≠ 0 by omega])]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have habs : Int.natAbs ((r : ℤ)+1) = r+1 := by omega
  simp [rFamily, rTerm, rr, habs, Int.natAbs_neg, smul_add,
    show (r : ℤ)+1 ≠ 0 by omega, show -((r : ℤ)+1) ≠ 0 by omega]

abbrev Variables (t : ℕ) := Label t × ℕ
abbrev Exponents (t : ℕ) := Variables t →₀ ℕ
abbrev CoordinateCarrier (D : LatticeData) (t : ℕ) :=
  Charge D →₀ PolynomialCoordinates (Label t)
abbrev StateIndex (D : LatticeData) (t : ℕ) :=
  (Σ _ : Charge D, Exponents t) × Finset ℕ

variable {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)

/-- Constructed tensor equivalence; integral charge and original ghost factor are unchanged. -/
def tensorCoordinates : State D ≃ₗ[ℂ] (CoordinateCarrier D t ⊗[ℂ] Fock) :=
  TensorProduct.congr (F.allChargeEquiv B) (LinearEquiv.refl ℂ Fock)

theorem tensor_operator_transport (u : E D) (n : ℤ) (G : Module.End ℂ Fock)
    (v : State D) :
    tensorCoordinates F B (tp (a u n) G v) =
      TensorProduct.map (coordinateMode (F.completeBasis B) u n) G (tensorCoordinates F B v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    simp only [tp_tmul, tensorCoordinates, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, TensorProduct.map_tmul, F.original_carrier_all_charges]
  | add v w hv hw => simp only [map_add, hv, hw]

def sector (p : Charge D) (Q : PolynomialCoordinates (Label t)) (w : Fock) : State D :=
  Finsupp.single p ((F.coordinateEquiv B).symm Q) ⊗ₜ[ℂ] w

@[simp] theorem tensorCoordinates_sector (p : Charge D)
    (Q : PolynomialCoordinates (Label t)) (w : Fock) :
    tensorCoordinates F B (sector F B p Q w) = Finsupp.single p Q ⊗ₜ[ℂ] w := by
  simp [sector, tensorCoordinates, carrierEquiv_single]

theorem sector_current (p : Charge D) (Q : PolynomialCoordinates (Label t))
    (w : Fock) (u : E D) (n : ℤ) (G : Module.End ℂ Fock) :
    tp (a u n) G (sector F B p Q w) =
      sector F B p
        (F.coordinateEquiv B (polynomialCurrent u p n ((F.coordinateEquiv B).symm Q))) (G w) := by
  simp only [sector, tp_tmul, a_single, AlgEquiv.symm_apply_apply]

theorem sector_add (p : Charge D) (Q T : PolynomialCoordinates (Label t)) (w : Fock) :
    sector F B p (Q+T) w = sector F B p Q w + sector F B p T w := by
  simp [sector, TensorProduct.add_tmul]
theorem sector_smul (p : Charge D) (z : ℂ) (Q : PolynomialCoordinates (Label t)) (w : Fock) :
    sector F B p (z • Q) w = z • sector F B p Q w := by
  simp [sector, TensorProduct.smul_tmul]
theorem sector_smul_right (p : Charge D) (z : ℂ) (Q : PolynomialCoordinates (Label t)) (w : Fock) :
    sector F B p Q (z • w) = z • sector F B p Q w := by
  simp [sector, TensorProduct.tmul_smul]

/-- The displayed x,y derivative and multiplication formulas act on ORIGINAL states. -/
theorem grouped_coordinate_d (p : Charge D) (r : ℕ)
    (Q : PolynomialCoordinates (Label t)) (w : Fock) :
    dTerm F r (sector F B p Q w) =
      (r+1 : ℂ) • sector F B p (pderiv (plus t,r) Q) (c (-((r : ℤ)+1)) w) +
      sector F B p (X (minus t,r) * Q) (c ((r : ℤ)+1) w) := by
  simp only [dTerm, dm, LinearMap.add_apply, sector_current]
  simp only [F.annihilation_minus B, show -((r : ℤ)+1) = -(r : ℤ)-1 by ring,
    F.creation_minus B, AlgEquiv.apply_symm_apply, sector_smul]

theorem grouped_coordinate_R (p : Charge D) (r : ℕ)
    (Q : PolynomialCoordinates (Label t)) (w : Fock) :
    rTerm F r (sector F B p Q w) =
      (r+1 : ℂ)⁻¹ • sector F B p (X (plus t,r) * Q) (b ((r : ℤ)+1) w) +
      sector F B p (pderiv (minus t,r) Q) (b (-((r : ℤ)+1)) w) := by
  have hz : (r+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  simp only [rTerm, rr, LinearMap.smul_apply, LinearMap.add_apply, sector_current]
  simp only [neg_neg, show -((r : ℤ)+1) = -(r : ℤ)-1 by ring,
    F.creation_plus B, F.annihilation_plus B, AlgEquiv.apply_symm_apply, sector_smul,
    smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul]

def coordinateMatterBasis : Module.Basis (Σ _ : Charge D, Exponents t) ℂ
    (CoordinateCarrier D t) :=
  Finsupp.basis (fun _ => MvPolynomial.basisMonomials (Variables t) ℂ)

/-- A genuine basis obtained using the constructed polynomial and tensor equivalences. -/
def actualBasis : Module.Basis (StateIndex D t) ℂ (State D) :=
  ((coordinateMatterBasis (D := D) (t := t)).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis (Finset ℕ) ℂ Fock)).map
      (tensorCoordinates F B).symm

/-- The optional flattened finite-support coordinates are constructed from that actual basis. -/
def finiteCoordinates : State D ≃ₗ[ℂ] (StateIndex D t →₀ ℂ) := (actualBasis F B).repr

@[simp] theorem finiteCoordinates_basis (i : StateIndex D t) :
    finiteCoordinates F B (actualBasis F B i) = Finsupp.single i 1 :=
  (actualBasis F B).repr_self i

@[simp] theorem actualBasis_apply (p : Charge D) (m : Exponents t) (S : Finset ℕ) :
    actualBasis F B (⟨p,m⟩,S) = sector F B p (monomial m 1) (ket S) := by
  simp [actualBasis, coordinateMatterBasis, Finsupp.coe_basis,
    MvPolynomial.coe_basisMonomials, tensorCoordinates, sector, ket,
    carrierEquiv, Finsupp.mapRange.linearEquiv]

theorem basis_expansion (v : State D) :
    (∑ i ∈ ((actualBasis F B).repr v).support,
      (actualBasis F B).repr v i • actualBasis F B i) = v := by
  simpa [Finsupp.linearCombination_apply, Finsupp.sum] using
    (actualBasis F B).linearCombination_repr v

def localDegree (m : Exponents t) (r : ℕ) : ℕ := m (plus t,r) + m (minus t,r)
def frequencies (m : Exponents t) : Finset ℕ := m.support.image Prod.snd
def longitudinalCount (m : Exponents t) : ℕ := ∑ r ∈ frequencies m, localDegree m r
def totalCount (i : StateIndex D t) : ℕ := longitudinalCount i.1.2 + GC.count i.2

theorem localDegree_zero_outside (m : Exponents t) (r : ℕ) (hr : r ∉ frequencies m) :
    localDegree m r = 0 := by
  have h1 : (plus t,r) ∉ m.support := fun h => hr (Finset.mem_image.mpr ⟨_,h,rfl⟩)
  have h2 : (minus t,r) ∉ m.support := fun h => hr (Finset.mem_image.mpr ⟨_,h,rfl⟩)
  simp [localDegree, Finsupp.notMem_support_iff.mp h1, Finsupp.notMem_support_iff.mp h2]

theorem sum_localDegree (m : Exponents t) (N : ℕ)
    (hN : ∀ r ∈ frequencies m, r < N) :
    (∑ r ∈ Finset.range N, localDegree m r) = longitudinalCount m := by
  symm
  apply Finset.sum_subset (fun r hr => Finset.mem_range.mpr (hN r hr))
  intro r hr hnot
  exact localDegree_zero_outside m r hnot

theorem numberTerm_coordinate (p : Charge D) (r : ℕ)
    (Q : PolynomialCoordinates (Label t)) (w : Fock) :
    numberTerm F r (sector F B p Q w) =
      sector F B p (X (plus t,r) * pderiv (plus t,r) Q +
        X (minus t,r) * pderiv (minus t,r) Q) w + sector F B p Q (GC.U (r+1) w) := by
  have hz : (r+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  have ht (A C : Module.End ℂ (Carrier D)) : tp (A*C) (1 : Module.End ℂ Fock) =
      tp A 1 * tp C 1 := by
    simpa [tp] using TensorProduct.map_mul A C (1 : Module.End ℂ Fock) 1
  have hc1 : tp (a F.ePlus (-((r : ℤ)+1)) * a F.eMinus ((r : ℤ)+1)) 1
      (sector F B p Q w) =
      (r+1 : ℂ) • sector F B p (X (plus t,r) * pderiv (plus t,r) Q) w := by
    rw [ht, Module.End.mul_apply, sector_current, F.annihilation_minus B,
      AlgEquiv.apply_symm_apply, sector_smul, map_smul, sector_current,
      show -((r : ℤ)+1) = -(r : ℤ)-1 by ring, F.creation_plus B,
      AlgEquiv.apply_symm_apply]
    rfl
  have hc2 : tp (a F.eMinus (-((r : ℤ)+1)) * a F.ePlus ((r : ℤ)+1)) 1
      (sector F B p Q w) =
      (r+1 : ℂ) • sector F B p (X (minus t,r) * pderiv (minus t,r) Q) w := by
    rw [ht, Module.End.mul_apply, sector_current, F.annihilation_plus B,
      AlgEquiv.apply_symm_apply, sector_smul, map_smul, sector_current,
      show -((r : ℤ)+1) = -(r : ℤ)-1 by ring, F.creation_minus B,
      AlgEquiv.apply_symm_apply]
    rfl
  simp only [numberTerm, tp, TensorProduct.map_add_left, LinearMap.add_apply,
    LinearMap.smul_apply]
  change (r+1 : ℂ)⁻¹ • (_ + _) + _ = _
  rw [hc1, hc2, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hz, one_smul, one_smul]
  simp only [sector_add]
  rfl

theorem numberTerm_basis (r : ℕ) (i : StateIndex D t) :
    numberTerm F r (actualBasis F B i) =
      (localDegree i.1.2 r + GC.localCount (r+1) i.2 : ℕ) • actualBasis F B i := by
  rcases i with ⟨⟨p,m⟩,S⟩
  simp only [actualBasis_apply]
  rw [numberTerm_coordinate, X_mul_pderiv_monomial,
    X_mul_pderiv_monomial, GC.U_ket]
  simp only [← Nat.cast_smul_eq_nsmul ℂ, sector_add, sector_smul,
    sector_smul_right, localDegree, Nat.cast_add, add_smul]
  abel

/-- Derived diagonal spectrum, with transverse exponents absent and site-1 holes present. -/
theorem M_basis (i : StateIndex D t) :
    M F (actualBasis F B i) = (totalCount i : ℂ) • actualBasis F B i := by
  classical
  let v := actualBasis F B i
  let N := max (modeBound F v)
    (max ((frequencies i.1.2).sup id + 1) (i.2.sup id + 3))
  have hb : modeBound F v ≤ N := le_max_left _ _
  have hf : ∀ r ∈ frequencies i.1.2, r < N := by
    intro r hr
    have hh := Finset.le_sup (f := id) hr
    dsimp [N]
    omega
  have hN3 : 3 ≤ N+1 := by dsimp [N]; omega
  have hS : ∀ j ∈ i.2, j+3 ≤ N+1 := by
    intro j hj
    have hh := Finset.le_sup (f := id) hj
    dsimp [N]
    omega
  have hg : (∑ r ∈ Finset.range N, GC.localCount (r+1) i.2) = GC.count i.2 := by
    have h := GC.sum_localCount i.2 (N+1) hN3 hS
    rw [Finset.sum_range_succ'] at h
    have hzero : GC.localCount 0 i.2 = 0 := by simp [GC.localCount]
    simpa only [hzero, zero_add, add_zero] using h
  rw [M, (numberFamily F).total_eq_sum v N hb]
  simp only [numberFamily, numberTerm_basis, ← Nat.cast_smul_eq_nsmul ℂ,
    Nat.cast_add, ← Finset.sum_smul, ← Nat.cast_sum, Finset.sum_add_distrib,
    sum_localDegree i.1.2 N hf, hg]
  rfl

theorem M_eq_number : M F = number (actualBasis F B) totalCount := by
  apply (actualBasis F B).ext
  intro i
  rw [M_basis, number, diagonal_basis]

def P0 : Module.End ℂ (State D) := projectZero (actualBasis F B) totalCount
def invM : Module.End ℂ (State D) := inverseNumber (actualBasis F B) totalCount
def h (p : Charge D) : Module.End ℂ (State D) := R F p * invM F B

theorem spectral_projection_inverse :
    M F * invM F B = 1 - P0 F B ∧ invM F B * M F = 1 - P0 F B ∧
    P0 F B * P0 F B = P0 F B ∧ M F * P0 F B = 0 ∧ invM F B * P0 F B = 0 := by
  simp only [M_eq_number F B]
  exact spectral_identities (actualBasis F B) totalCount

theorem invM_commutes_d0 (p : Charge D) : invM F B * d0 F p = d0 F p * invM F B := by
  apply commutes_function (actualBasis F B) totalCount (d0 F p)
    (by simpa only [M_eq_number F B] using M_commutes_d0 F p)

theorem invM_commutes_R (p : Charge D) : invM F B * R F p = R F p * invM F B := by
  apply commutes_function (actualBasis F B) totalCount (R F p)
    (by simpa only [M_eq_number F B] using M_commutes_R F p)

theorem homotopy_contraction (p : Charge D) (hp : F.pPlus p ≠ 0) :
    d0 F p * h F B p + h F B p * d0 F p = 1 - P0 F B := by
  calc
    _ = (d0 F p * R F p + R F p * d0 F p) * invM F B := by
      simp only [h, add_mul, mul_assoc, invM_commutes_d0 F B p]
    _ = M F * invM F B := by rw [original_contraction F p hp]
    _ = _ := (spectral_projection_inverse F B).1

theorem homotopy_square (p : Charge D) : h F B p * h F B p = 0 := by
  calc
    _ = R F p * (invM F B * R F p) * invM F B := by rw [h]; noncomm_ring
    _ = (R F p * R F p) * (invM F B * invM F B) := by
      rw [invM_commutes_R F B p]; noncomm_ring
    _ = 0 := by rw [R_square, zero_mul]

def NoLongitudinal (m : Exponents t) : Prop := ∀ r, m (plus t,r) = 0 ∧ m (minus t,r) = 0

theorem longitudinalCount_zero_iff (m : Exponents t) :
    longitudinalCount m = 0 ↔ NoLongitudinal m := by
  classical
  constructor
  · intro hm r
    have hd : localDegree m r = 0 := by
      by_cases hr : r ∈ frequencies m
      · have hl := Finset.single_le_sum (fun s (_ : s ∈ frequencies m) =>
          Nat.zero_le (localDegree m s)) hr
        change localDegree m r ≤ longitudinalCount m at hl
        omega
      · exact localDegree_zero_outside m r hr
    exact Nat.add_eq_zero_iff.mp hd
  · intro hm
    apply Finset.sum_eq_zero
    intro r hr
    simp [localDegree, (hm r).1, (hm r).2]

theorem totalCount_zero_iff (i : StateIndex D t) :
    totalCount i = 0 ↔ NoLongitudinal i.1.2 ∧ (i.2 = {1} ∨ i.2 = {1,3}) := by
  simp only [totalCount, Nat.add_eq_zero_iff, longitudinalCount_zero_iff, GC.count_zero_iff]

def transverseVariable (x : Fin t × ℕ) : Variables t := (transverse t x.1,x.2)

theorem transverseVariable_injective : Function.Injective (transverseVariable (t := t)) := by
  intro x y h
  rcases x with ⟨i,r⟩
  rcases y with ⟨j,s⟩
  simpa [transverseVariable, transverse] using h

theorem noLongitudinal_mapDomain (d : (Fin t × ℕ) →₀ ℕ) :
    NoLongitudinal (d.mapDomain transverseVariable) := by
  intro r
  constructor
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨⟨j,s⟩,h⟩
    simp [transverseVariable, transverse, plus] at h
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨⟨j,s⟩,h⟩
    simp [transverseVariable, transverse, minus] at h

theorem noLongitudinal_support (m : Exponents t) (hm : NoLongitudinal m) :
    (m.support : Set (Variables t)) ⊆ Set.range transverseVariable := by
  intro x hx
  rcases x with ⟨l,r⟩
  rcases l with u | (u | j)
  · cases u
    exact False.elim ((Finsupp.mem_support_iff.mp hx) (hm r).1)
  · cases u
    exact False.elim ((Finsupp.mem_support_iff.mp hx) (hm r).2)
  · exact ⟨(j,r),rfl⟩

/-- Surjectivity onto precisely the polynomials with no longitudinal variables is constructed. -/
theorem transverse_monomial_preimage (m : Exponents t) (hm : NoLongitudinal m) :
    ∃ Q : MvPolynomial (Fin t × ℕ) ℂ,
      rename transverseVariable Q = monomial m 1 := by
  refine ⟨monomial (m.comapDomain transverseVariable transverseVariable_injective.injOn) 1, ?_⟩
  rw [rename_monomial, Finsupp.mapDomain_comapDomain transverseVariable
    transverseVariable_injective m (noLongitudinal_support m hm)]

/-- Actual polynomial in the supplied basis of the actual K, inside the original oscillator. -/
def transverseOriginal : MvPolynomial (Fin t × ℕ) ℂ →ₐ[ℂ] Oscillator D :=
  (F.coordinateEquiv B).symm.toAlgHom.comp (rename transverseVariable)

@[simp] theorem transverseOriginal_X (j : Fin t) (r : ℕ) :
    transverseOriginal F B (X (j,r)) = lin r (B j : E D) := by
  simp [transverseOriginal, transverseVariable]

theorem transverseOriginal_eq_aeval :
    transverseOriginal F B = MvPolynomial.aeval (fun x : Fin t × ℕ => lin x.2 (B x.1 : E D)) := by
  ext x
  rcases x with ⟨j,r⟩
  simp

def ghostB0 : Module.End ℂ (State D) := tp 1 (b 0)
def chargeMatter (p : Charge D) : Module.End ℂ (Carrier D) :=
  (Finsupp.lsingle p).comp (Finsupp.lapply p)
def chargeProject (p : Charge D) : Module.End ℂ (State D) := tp (chargeMatter p) 1

theorem ghost_sector (p : Charge D) (Q : PolynomialCoordinates (Label t))
    (w : Fock) (G : Module.End ℂ Fock) :
    tp (1 : Module.End ℂ (Carrier D)) G (sector F B p Q w) = sector F B p Q (G w) := by
  simp [sector]

theorem chargeProject_basis (p : Charge D) (i : StateIndex D t) :
    chargeProject p (actualBasis F B i) =
      (if i.1.1 = p then (1 : ℂ) else 0) • actualBasis F B i := by
  rcases i with ⟨⟨q,m⟩,S⟩
  simp only [actualBasis_apply]
  by_cases h : q = p
  · subst q
    simp [chargeProject, chargeMatter, sector]
  · simp [chargeProject, chargeMatter, sector, h, Ne.symm h]

theorem chargeProject_diagonal (p : Charge D) : chargeProject (D := D) p =
    diagonal (actualBasis F B) (fun i => if i.1.1 = p then 1 else 0) := by
  apply (actualBasis F B).ext
  intro i
  rw [chargeProject_basis, diagonal_basis]

theorem fixed_charge_coefficients (p : Charge D) (v : State D) :
    chargeProject p v = v ↔ ∀ i : StateIndex D t, i.1.1 ≠ p → (actualBasis F B).repr v i = 0 := by
  rw [chargeProject_diagonal F B]
  constructor
  · intro h i hi
    have hh := congrArg (fun w => (actualBasis F B).repr w i) h
    simpa [diagonal_coefficient, hi] using hh.symm
  · intro h
    apply (actualBasis F B).repr.injective
    ext i
    by_cases hi : i.1.1 = p
    · simp [diagonal_coefficient, hi]
    · simp [diagonal_coefficient, hi, h i hi]

/-- The literal original b0 kernel is detected, without imposing a physical mass shell. -/
theorem b0_coefficients (v : State D) : ghostB0 v = 0 ↔
    ∀ i : StateIndex D t, 3 ∈ i.2 → (actualBasis F B).repr v i = 0 := by
  classical
  let J : Module.End ℂ (State D) := tp 1 (create 3 * annihilate 3)
  have hJ : J = diagonal (actualBasis F B) (fun i => if 3 ∈ i.2 then 1 else 0) := by
    apply (actualBasis F B).ext
    rintro ⟨⟨p,m⟩,S⟩
    rw [actualBasis_apply, diagonal_basis, actualBasis_apply]
    change tp 1 (create 3 * annihilate 3) (sector F B p (monomial m 1) (ket S)) = _
    rw [ghost_sector,
      D5.S3.Quantum.Fermionic.BcGhostQuartetCount.create_annihilate_ket]
    by_cases h3 : 3 ∈ S <;> simp [h3, sector]
  have hfac : J = tp 1 (create 3) * ghostB0 := by
    simpa [J, ghostB0, GC.b_zero, tp] using
      TensorProduct.map_mul (1 : Module.End ℂ (Carrier D)) 1 (create 3) (annihilate 3)
  constructor
  · intro hb i hi
    have hz : J v = 0 := by rw [hfac, Module.End.mul_apply, hb, map_zero]
    have hh := congrArg (fun w => (actualBasis F B).repr w i) hz
    rw [hJ, diagonal_coefficient] at hh
    simpa [hi] using hh
  · intro hv
    rw [← basis_expansion F B v]
    simp only [map_sum, map_smul]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases h3 : 3 ∈ i.2
    · rw [hv i h3, zero_smul]
    · rcases i with ⟨⟨p,m⟩,S⟩
      rw [actualBasis_apply]
      simp [ghostB0, ghost_sector, GC.b_zero, annihilate_ket, h3, sector]

def groundMap (p : Charge D) : MvPolynomial (Fin t × ℕ) ℂ →ₗ[ℂ] State D :=
  ((TensorProduct.mk ℂ (Carrier D) Fock).flip
    D5.S3.Quantum.Fermionic.BcGhostQuartetCount.c1vac).comp
      ((Finsupp.lsingle p).comp (transverseOriginal F B).toLinearMap)

theorem groundMap_apply (p : Charge D) (Q : MvPolynomial (Fin t × ℕ) ℂ) :
    groundMap F B p Q = Finsupp.single p (transverseOriginal F B Q) ⊗ₜ[ℂ]
      D5.S3.Quantum.Fermionic.BcGhostQuartetCount.c1vac := rfl

theorem groundMap_sector (p : Charge D) (Q : MvPolynomial (Fin t × ℕ) ℂ) :
    groundMap F B p Q = sector F B p (rename transverseVariable Q) (ket {1}) := by
  rw [groundMap_apply, D5.S3.Quantum.Fermionic.BcGhostQuartetCount.c1vac_eq]
  rfl

theorem groundMap_monomial (p : Charge D) (d : (Fin t × ℕ) →₀ ℕ) :
    groundMap F B p (monomial d 1) = actualBasis F B
      (⟨p,d.mapDomain transverseVariable⟩,{1}) := by
  rw [groundMap_sector, rename_monomial, actualBasis_apply]

theorem groundMap_identities (p : Charge D) :
    (M F).comp (groundMap F B p) = 0 ∧ ghostB0.comp (groundMap F B p) = 0 ∧
    (chargeProject p).comp (groundMap F B p) = groundMap F B p := by
  have hq (d : (Fin t × ℕ) →₀ ℕ) : totalCount (D := D)
      (⟨p,d.mapDomain transverseVariable⟩,{1}) = 0 := by
    apply (totalCount_zero_iff _).mpr
    exact ⟨noLongitudinal_mapDomain d, Or.inl rfl⟩
  repeat' constructor
  all_goals
    apply (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ).ext
    intro d
    change _ (monomial d 1) = _
    simp only [LinearMap.comp_apply, groundMap_monomial]
  · rw [M_basis, hq]; simp
  · rw [actualBasis_apply]
    simp [ghostB0, ghost_sector, GC.b_zero, annihilate_ket, sector]
  · simp [chargeProject_basis]

/-- Full ghost zero count has two states, before b0 is imposed. -/
theorem full_zero_count_coefficients (v : State D) : M F v = 0 ↔
    ∀ i ∈ ((actualBasis F B).repr v).support,
      NoLongitudinal i.1.2 ∧ (i.2 = {1} ∨ i.2 = {1,3}) := by
  rw [M_eq_number F B, kernel_number_iff]
  constructor
  · intro h i hi
    apply (totalCount_zero_iff i).mp
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hi) (h i hn)
  · intro h i hn
    by_contra hc
    exact hn ((totalCount_zero_iff i).mpr (h i (Finsupp.mem_support_iff.mpr hc)))

/-- Exact fixed-integral-charge, literal-kerb0 ground; Q is an arbitrary polynomial
in the actual supplied transverse basis. This is not a claim about the physical
relative BRST complex, which additionally needs totalL0 and the actual remainder. -/
theorem literal_relative_ground (p : Charge D) (v : State D) :
    (M F v = 0 ∧ ghostB0 v = 0 ∧ chargeProject p v = v) ↔
      ∃ Q : MvPolynomial (Fin t × ℕ) ℂ,
        v = Finsupp.single p (transverseOriginal F B Q) ⊗ₜ[ℂ]
          D5.S3.Quantum.Fermionic.BcGhostQuartetCount.c1vac := by
  classical
  constructor
  · rintro ⟨hm,hb,hp⟩
    have hground : v ∈ LinearMap.range (groundMap F B p) := by
      rw [← basis_expansion F B v]
      apply Submodule.sum_mem
      intro i hi
      have hm' := (full_zero_count_coefficients F B v).mp hm i hi
      have hb' := (b0_coefficients F B v).mp hb
      have hp' := (fixed_charge_coefficients F B p v).mp hp
      have hcharge : i.1.1 = p := by
        by_contra hn
        exact (Finsupp.mem_support_iff.mp hi) (hp' i hn)
      have hket : i.2 = {1} := by
        rcases hm'.2 with h | h
        · exact h
        · exact False.elim ((Finsupp.mem_support_iff.mp hi) (hb' i (by simp [h])))
      obtain ⟨Q,hQ⟩ := transverse_monomial_preimage i.1.2 hm'.1
      apply Submodule.smul_mem
      refine ⟨Q, ?_⟩
      rw [groundMap_sector, hQ]
      rcases i with ⟨⟨q,m⟩,S⟩
      dsimp at hcharge hket
      subst q
      subst S
      exact (actualBasis_apply F B p m {1}).symm
    obtain ⟨Q,hQ⟩ := hground
    exact ⟨Q, hQ.symm.trans (groundMap_apply F B p Q)⟩
  · rintro ⟨Q,rfl⟩
    change M F (groundMap F B p Q) = 0 ∧ ghostB0 (groundMap F B p Q) = 0 ∧
      chargeProject p (groundMap F B p Q) = groundMap F B p Q
    exact ⟨LinearMap.congr_fun (groundMap_identities F B p).1 Q,
      LinearMap.congr_fun (groundMap_identities F B p).2.1 Q,
      LinearMap.congr_fun (groundMap_identities F B p).2.2 Q⟩

theorem actual_composition_capture (v : State D) (W : Finset (Module.End ℂ (State D))) :
    ∃ N, modeBound F v ≤ N ∧ ∀ T ∈ W, ∀ r, N ≤ r →
      dm F ((r : ℤ)+1) (T v) = 0 ∧ dm F (-((r : ℤ)+1)) (T v) = 0 ∧
      rr F ((r : ℤ)+1) (T v) = 0 ∧ rr F (-((r : ℤ)+1)) (T v) = 0 := by
  obtain ⟨N,hN,hW⟩ := (dFamily F).finite_outputs_capture v W
  refine ⟨N,hN,?_⟩
  intro T hT r hr
  exact modeBound_spec F (T v) r ((hW T hT).trans hr)

theorem coordinate_derivative_multiplication (x y : Variables t)
    (Q : PolynomialCoordinates (Label t)) :
    pderiv x (X y * Q) - X y * pderiv x Q = if x=y then Q else 0 := by
  classical
  rw [pderiv_mul, pderiv_X]
  by_cases hxy : x=y
  · subst y; simp
  · simp [Pi.single_apply, hxy, Ne.symm hxy]

/-- eta=c(-k), kappa=c(k), B=b(k), beta=b(-k), on the actual original Fock. -/
theorem actual_quartet_CAR (k : ℕ) (hk : 0 < k) :
    c (-(k : ℤ)) * b k + b k * c (-(k : ℤ)) = 1 ∧
    b (-(k : ℤ)) * c k + c k * b (-(k : ℤ)) = 1 ∧
    c (-(k : ℤ)) * b (-(k : ℤ)) + b (-(k : ℤ)) * c (-(k : ℤ)) = 0 ∧
    b k * c k + c k * b k = 0 ∧
    c (-(k : ℤ)) * c k + c k * c (-(k : ℤ)) = 0 ∧
    b k * b (-(k : ℤ)) + b (-(k : ℤ)) * b k = 0 := by
  have h1 := ghost_mixed_car (k : ℤ) (-(k : ℤ))
  have h2 := ghost_mixed_car (-(k : ℤ)) (k : ℤ)
  have h3 := ghost_mixed_car (-(k : ℤ)) (-(k : ℤ))
  have h4 := ghost_mixed_car (k : ℤ) (k : ℤ)
  have hp : (k : ℤ)+(k : ℤ) ≠ 0 := by omega
  have hn : -(k : ℤ)+ -(k : ℤ) ≠ 0 := by omega
  exact ⟨by simpa [add_comm] using h1, by simpa using h2,
    by simpa [add_comm,hn] using h3, by simpa [hp] using h4,
    ghost_c_car _ _, ghost_b_car _ _⟩

theorem b0_dm (n : ℤ) (hn : n ≠ 0) : ac (ghostB0 (D := D)) (dm F n) = 0 := by
  have hc : b 0 * c (-n) + c (-n) * b 0 = 0 := by
    simpa [hn] using ghost_mixed_car 0 (-n)
  rw [ghostB0, dm, tp_ac]
  simp [hc, tp]

theorem b0_rr (n : ℤ) : ac (ghostB0 (D := D)) (rr F n) = 0 := by
  rw [ghostB0, rr, tp_ac]
  simp [ghost_b_car, tp]

theorem b0_unscaledD : ac (ghostB0 (D := D)) (unscaledD F) = 0 := by
  apply Family.total_ac_fixed
  intro r
  simp [dFamily, dTerm, ac_add_right, b0_dm,
    show (r : ℤ)+1 ≠ 0 by omega, show -((r : ℤ)+1) ≠ 0 by omega]

theorem b0_unscaledR : ac (ghostB0 (D := D)) (unscaledR F) = 0 := by
  apply Family.total_ac_fixed
  intro r
  simp [rFamily, rTerm, ac_smul_right, ac_add_right, b0_rr]

theorem b0_d0 (p : Charge D) : ac (ghostB0 (D := D)) (d0 F p) = 0 := by
  rw [d0, ac_smul_right, b0_unscaledD, smul_zero]
theorem b0_R (p : Charge D) : ac (ghostB0 (D := D)) (R F p) = 0 := by
  rw [R, ac_smul_right, b0_unscaledR, smul_zero]

theorem odd_even_commutes {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T A C : Module.End ℂ V) (hA : ac T A = 0) (hC : ac T C = 0) :
    T * ac A C = ac A C * T := by
  have hTA : T*A = -(A*T) := eq_neg_iff_add_eq_zero.mpr hA
  have hTC : T*C = -(C*T) := eq_neg_iff_add_eq_zero.mpr hC
  calc
    _ = (T*A)*C + (T*C)*A := by unfold ac; noncomm_ring
    _ = -(A*T)*C + -(C*T)*A := by rw [hTA,hTC]
    _ = -(A*(T*C)) - C*(T*A) := by noncomm_ring
    _ = _ := by rw [hTC,hTA]; unfold ac; noncomm_ring

theorem M_commutes_b0 : M F * ghostB0 = ghostB0 * M F := by
  simp only [← unscaled_contraction F]
  exact (odd_even_commutes ghostB0 (unscaledD F) (unscaledR F)
    (b0_unscaledD F) (b0_unscaledR F)).symm

theorem invM_commutes_b0 : invM F B * ghostB0 = ghostB0 * invM F B := by
  apply commutes_function (actualBasis F B) totalCount ghostB0
    (by simpa only [M_eq_number F B] using M_commutes_b0 F)
theorem P0_commutes_b0 : P0 F B * ghostB0 = ghostB0 * P0 F B := by
  apply commutes_function (actualBasis F B) totalCount ghostB0
    (by simpa only [M_eq_number F B] using M_commutes_b0 F)

theorem chargeMatter_a (p : Charge D) (u : E D) (n : ℤ) :
    chargeMatter p * a u n = a u n * chargeMatter p := by
  apply Finsupp.lhom_ext
  intro q P
  by_cases hq : q=p
  · subst q
    simp [Module.End.mul_apply, chargeMatter, a_single]
  · simp [Module.End.mul_apply, chargeMatter, a_single, hq, Ne.symm hq]

theorem chargeProject_current (p : Charge D) (u : E D) (n : ℤ) (G : Module.End ℂ Fock) :
    chargeProject p * tp (a u n) G = tp (a u n) G * chargeProject p := by
  simp only [chargeProject, tp, ← TensorProduct.map_mul, one_mul, mul_one, chargeMatter_a]

theorem chargeProject_d0 (p q : Charge D) :
    chargeProject p * d0 F q = d0 F q * chargeProject p := by
  have hu : chargeProject p * unscaledD F = unscaledD F * chargeProject p := by
    apply Family.total_commutes_fixed
    intro r
    simp [dFamily, dTerm, dm, mul_add, add_mul, chargeProject_current]
  simp only [d0, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hu]

theorem chargeProject_R (p q : Charge D) :
    chargeProject p * R F q = R F q * chargeProject p := by
  have hu : chargeProject p * unscaledR F = unscaledR F * chargeProject p := by
    apply Family.total_commutes_fixed
    intro r
    simp [rFamily, rTerm, rr, mul_add, add_mul, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, chargeProject_current]
  simp only [R, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hu]

include B in
theorem M_commutes_chargeProject (p : Charge D) : M F * chargeProject p = chargeProject p * M F := by
  simp only [M_eq_number F B, chargeProject_diagonal F B]
  apply (actualBasis F B).ext
  intro i
  simp only [number, Module.End.mul_apply, diagonal_basis, map_smul, smul_smul]
  rw [mul_comm]

theorem invM_commutes_chargeProject (p : Charge D) :
    invM F B * chargeProject p = chargeProject p * invM F B := by
  apply commutes_function (actualBasis F B) totalCount (chargeProject p)
    (by simpa only [M_eq_number F B] using M_commutes_chargeProject F B p)
theorem P0_commutes_chargeProject (p : Charge D) :
    P0 F B * chargeProject p = chargeProject p * P0 F B := by
  apply commutes_function (actualBasis F B) totalCount (chargeProject p)
    (by simpa only [M_eq_number F B] using M_commutes_chargeProject F B p)

/-- Stability is on the literal original b0 kernel, including h, M and spectral maps. -/
theorem literal_b0_stability (p : Charge D) (v : State D) (hv : ghostB0 v = 0) :
    ghostB0 (d0 F p v) = 0 ∧ ghostB0 (R F p v) = 0 ∧
    ghostB0 (M F v) = 0 ∧ ghostB0 (invM F B v) = 0 ∧
    ghostB0 (P0 F B v) = 0 ∧ ghostB0 (h F B p v) = 0 := by
  have hd := LinearMap.congr_fun (b0_d0 F p) v
  have hr := LinearMap.congr_fun (b0_R F p) v
  have hm := LinearMap.congr_fun (M_commutes_b0 F) v
  have hi := LinearMap.congr_fun (invM_commutes_b0 F B) v
  have hp := LinearMap.congr_fun (P0_commutes_b0 F B) v
  simp only [ac, LinearMap.add_apply, Module.End.mul_apply, hv, map_zero, add_zero] at hd hr
  simp only [Module.End.mul_apply, hv, map_zero] at hm hi hp
  refine ⟨hd,hr,hm.symm,hi.symm,hp.symm,?_⟩
  have hh := LinearMap.congr_fun (b0_R F p) (invM F B v)
  simpa only [h, ac, LinearMap.add_apply, Module.End.mul_apply, hi.symm,
    map_zero, add_zero] using hh

theorem fixed_charge_stability (p q : Charge D) (v : State D) (hv : chargeProject p v = v) :
    chargeProject p (d0 F q v) = d0 F q v ∧ chargeProject p (R F q v) = R F q v ∧
    chargeProject p (M F v) = M F v ∧ chargeProject p (invM F B v) = invM F B v ∧
    chargeProject p (P0 F B v) = P0 F B v ∧ chargeProject p (h F B q v) = h F B q v := by
  have hd := LinearMap.congr_fun (chargeProject_d0 F p q) v
  have hr := LinearMap.congr_fun (chargeProject_R F p q) v
  have hm := LinearMap.congr_fun (M_commutes_chargeProject F B p) v
  have hi := LinearMap.congr_fun (invM_commutes_chargeProject F B p) v
  have hp := LinearMap.congr_fun (P0_commutes_chargeProject F B p) v
  simp only [Module.End.mul_apply, hv] at hd hr hm hi hp
  refine ⟨hd,hr,hm.symm,hi.symm,hp.symm,?_⟩
  have hh := LinearMap.congr_fun (chargeProject_R F p q) (invM F B v)
  simpa only [h, Module.End.mul_apply, hi.symm] using hh

theorem spectral_remaining_identities : P0 F B * M F = 0 ∧
    P0 F B * invM F B = 0 ∧ invM F B * P0 F B = 0 := by
  rw [M_eq_number F B]
  repeat' constructor
  all_goals
    apply (actualBasis F B).ext
    intro i
    by_cases hi : totalCount i=0
    · simp [P0, invM, number, inverseNumber, projectZero, Module.End.mul_apply, hi]
    · simp [P0, invM, number, inverseNumber, projectZero, Module.End.mul_apply, hi]

theorem zero_count_iff_projection (v : State D) : M F v = 0 ↔ P0 F B v = v := by
  constructor
  · intro hv
    have hh := LinearMap.congr_fun (spectral_projection_inverse F B).2.1 v
    change invM F B (M F v) = v-P0 F B v at hh
    rw [hv, map_zero] at hh
    exact (sub_eq_zero.mp hh.symm).symm
  · intro hv
    calc
      M F v = M F (P0 F B v) := congrArg (M F) hv.symm
      _ = 0 := LinearMap.congr_fun (spectral_projection_inverse F B).2.2.2.1 v

theorem pPlus_nonzero_excludes_zero_charge (p : Charge D) (hp : F.pPlus p ≠ 0) : p ≠ 0 := by
  intro hzero
  subst p
  apply hp
  simp [NullFrame.pPlus, chargeVector, g]

theorem invM_basis (i : StateIndex D t) : invM F B (actualBasis F B i) =
    (if totalCount i=0 then (0 : ℂ) else (totalCount i : ℂ)⁻¹) • actualBasis F B i := by
  simp [invM, inverseNumber]
theorem P0_basis (i : StateIndex D t) : P0 F B (actualBasis F B i) =
    (if totalCount i=0 then (1 : ℂ) else 0) • actualBasis F B i := by
  simp [P0, projectZero]

theorem site_one_counts_hole (S : Finset ℕ) :
    (b (-1) * c 1) (ket S) = if 1 ∈ S then 0 else ket S := by
  rw [GC.b_negative_one, GC.c_positive_one]
  exact D5.S3.Quantum.Fermionic.BcGhostQuartetCount.annihilate_create_ket 1 S

/-- The fixed-charge predicate is the image of the original sector inclusion. -/
theorem fixed_charge_original_image (p : Charge D) (v : State D) :
    chargeProject p v = v ↔ ∃ w : Oscillator D ⊗[ℂ] Fock,
      TensorProduct.map (Finsupp.lsingle p : Oscillator D →ₗ[ℂ] Carrier D)
        (1 : Module.End ℂ Fock) w = v := by
  let I := TensorProduct.map (Finsupp.lsingle p : Oscillator D →ₗ[ℂ] Carrier D)
    (1 : Module.End ℂ Fock)
  let E := TensorProduct.map (Finsupp.lapply p : Carrier D →ₗ[ℂ] Oscillator D)
    (1 : Module.End ℂ Fock)
  have hIE : I.comp E = chargeProject p := by
    simp only [I, E, chargeProject, chargeMatter, tp, ← TensorProduct.map_comp,
      LinearMap.comp_id]
  have hI (w : Oscillator D ⊗[ℂ] Fock) : chargeProject p (I w) = I w := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul P g => simp [I, chargeProject, chargeMatter, tp]
    | add x y hx hy => simp only [map_add, hx, hy]
  constructor
  · intro hv
    exact ⟨E v, (LinearMap.congr_fun hIE v).trans hv⟩
  · rintro ⟨w,rfl⟩
    exact hI w

theorem P0_commutes_R (p : Charge D) : P0 F B * R F p = R F p * P0 F B := by
  apply commutes_function (actualBasis F B) totalCount (R F p)
    (by simpa only [M_eq_number F B] using M_commutes_R F p)

theorem homotopy_projection_zero (p : Charge D) :
    h F B p * P0 F B = 0 ∧ P0 F B * h F B p = 0 := by
  constructor
  · rw [h, mul_assoc, (spectral_remaining_identities F B).2.2, mul_zero]
  · rw [h, ← mul_assoc, P0_commutes_R, mul_assoc,
      (spectral_remaining_identities F B).2.1, mul_zero]

end D5.S3.VertexAlgebra.LatticeQuartetContraction
