/- GID: D5/S3/VertexAlgebra/Lattice/LatticeQuartetOperators
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeQuartetOperators
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Locally finite original quartet modes and their actual count anticommutator. -/

import D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
import D5.S3.Quantum.Fermionic.BcGhostQuartetCount
import D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Rename

/-! Quartet operators on the original all-charge matter tensor original bc Fock. -/

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

private theorem tensor_sub_left (A B : Module.End ℂ (Carrier D)) (G : Module.End ℂ Fock) :
    TensorProduct.map (A-B) G = TensorProduct.map A G - TensorProduct.map B G := by
  ext v w
  simp [TensorProduct.sub_tmul]
private theorem tensor_sub_right (A : Module.End ℂ (Carrier D)) (G H : Module.End ℂ Fock) :
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

private theorem tp_zero_ac (A B : Module.End ℂ (Carrier D)) (G H : Module.End ℂ Fock)
    (hAB : A * B - B * A = 0) (hGH : G * H + H * G = 0) :
    ac (tp A G) (tp B H) = 0 := by
  rw [tp_ac, hAB, hGH]
  simp [tp]

/-- Bilinear extension of the pinned original Heisenberg law. -/
private theorem a_heisenberg (u v : E D) (m n : ℤ) :
    a u m * a v n - a v n * a u m =
      (if m+n=0 then (m : ℂ) * g D u v else 0) • (1 : Module.End ℂ (Carrier D)) := by
  classical
  have expand (u v : E D) (m n : ℤ) :
      a u m * a v n = ∑ i, ∑ j,
        (u i * v j) • (neutralMode D i m * neutralMode D j n) := by
    simp only [a, Finset.sum_mul, Finset.mul_sum, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
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

private theorem dm_dm (m n : ℤ) : ac (dm F m) (dm F n) = 0 := by
  apply tp_zero_ac
  · simp [a_heisenberg, F.minus_null]
  · exact ghost_c_car (-m) (-n)

private theorem rr_rr (m n : ℤ) : ac (rr F m) (rr F n) = 0 := by
  apply tp_zero_ac
  · simp [a_heisenberg, F.plus_null]
  · exact ghost_b_car m n

/-- This identity is on the original tensor carrier at every integer mode. -/
private theorem dm_rr (m n : ℤ) :
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

private theorem original_single_frequency (r : ℕ) :
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
  dsimp only [k, z] at hz ⊢
  simp only [smul_add, smul_sub, neg_smul, smul_neg, smul_smul, mul_neg,
    inv_mul_cancel₀ hz, one_smul, sub_eq_add_neg]
  abel

private theorem distinct_frequencies (r s : ℕ) (hrs : r ≠ s) :
    ac (dTerm F r) (rTerm F s) = 0 := by
  simp only [dTerm, rTerm, ac_smul_right, ac_add_left, ac_add_right, dm_rr]
  have h1 : (r : ℤ)+1 ≠ (s : ℤ)+1 := by omega
  have h2 : (r : ℤ)+1 ≠ -((s : ℤ)+1) := by omega
  have h3 : -((r : ℤ)+1) ≠ (s : ℤ)+1 := by omega
  have h4 : -((r : ℤ)+1) ≠ -((s : ℤ)+1) := by omega
  simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, add_zero, zero_add, smul_zero]

private theorem dTerm_rTerm (r s : ℕ) : ac (dTerm F r) (rTerm F s) =
    if r = s then numberTerm F r else 0 := by
  by_cases h : r = s
  · subst s; simpa using original_single_frequency F r
  · simpa [h] using distinct_frequencies F r s h

private theorem dTerm_dTerm (r s : ℕ) : ac (dTerm F r) (dTerm F s) = 0 := by
  simp only [dTerm, ac_add_left, ac_add_right, dm_dm, add_zero]
private theorem rTerm_rTerm (r s : ℕ) : ac (rTerm F r) (rTerm F s) = 0 := by
  simp only [rTerm, ac_smul_left, ac_smul_right, ac_add_left, ac_add_right,
    rr_rr, add_zero, smul_zero]

private theorem a_positive_vanish (u : E D) (v : Carrier D) (k : ℕ)
    (hk : vectorFrequencyBound D v < k) : a u (k : ℤ) v = 0 := by
  classical
  simp only [a, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [neutralMode_vanish D i v (k : ℤ) (by exact_mod_cast hk), smul_zero]

private theorem positive_ghosts_vanish (w : Fock) (k : ℕ) (hk : GC.capture w ≤ k) :
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
private theorem four_modes_tmul_vanish (v : Carrier D) (w : Fock) (r : ℕ)
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

private theorem four_modes_capture (v : State D) : ∃ N : ℕ, ∀ r, N ≤ r →
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
    simp only [map_add, h1,h2,h3,h4,h5,h6,h7,h8, add_zero, and_self]

def modeBound (v : State D) : ℕ := Classical.choose (four_modes_capture F v)

private theorem modeBound_spec (v : State D) (r : ℕ) (hr : modeBound F v ≤ r) :
    dm F ((r : ℤ)+1) v = 0 ∧ dm F (-((r : ℤ)+1)) v = 0 ∧
    rr F ((r : ℤ)+1) v = 0 ∧ rr F (-((r : ℤ)+1)) v = 0 :=
  Classical.choose_spec (four_modes_capture F v) r hr

def dFamily : Family (State D) :=
  ⟨dTerm F, modeBound F, by
    intro v r hr
    obtain ⟨h1,h2,h3,h4⟩ := modeBound_spec F v r hr
    simp only [dTerm, LinearMap.add_apply, h1, h2, add_zero]⟩
def rFamily : Family (State D) :=
  ⟨rTerm F, modeBound F, by
    intro v r hr
    obtain ⟨h1,h2,h3,h4⟩ := modeBound_spec F v r hr
    simp only [rTerm, LinearMap.smul_apply, LinearMap.add_apply, h3, h4, add_zero, smul_zero]⟩
def numberFamily : Family (State D) :=
  ⟨numberTerm F, modeBound F, by
    intro v r hr
    have hd : dTerm F r v = 0 := (dFamily F).vanish v r hr
    have hh : rTerm F r v = 0 := (rFamily F).vanish v r hr
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

private theorem unscaledD_square : unscaledD F * unscaledD F = 0 :=
  Family.total_square_zero (dFamily F) (dTerm_dTerm F)
private theorem unscaledR_square : unscaledR F * unscaledR F = 0 :=
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
        have hr : r < N := by by_contra h; exact hz (by simpa only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] using (hN r (by omega)).1)
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, by simp [Int.ofNat_eq_natCast, Int.negSucc_eq]⟩)
    | negSucc r =>
      have hr : r < N := by by_contra h; exact hz (by simpa only [Int.negSucc_eq, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] using (hN r (by omega)).2)
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, by simp [Int.ofNat_eq_natCast, Int.negSucc_eq]⟩)
  constructor
  · apply hf _ (by simp)
    intro r hr
    obtain ⟨h1,h2,h3,h4⟩ := modeBound_spec F v r hr
    simp only [if_neg (show (r : ℤ)+1 ≠ 0 by omega), if_neg (show -((r : ℤ)+1) ≠ 0 by omega), h1, h2, and_self]
  · apply hf _ (by simp)
    intro r hr
    obtain ⟨h1,h2,h3,h4⟩ := modeBound_spec F v r hr
    simp only [if_neg (show (r : ℤ)+1 ≠ 0 by omega), if_neg (show -((r : ℤ)+1) ≠ 0 by omega), h3, h4, smul_zero, and_self]

theorem d0_signed_formula (p : Charge D) (v : State D) :
    d0 F p v = F.pPlus p •
      ∑ᶠ n : ℤ, if n=0 then 0 else tp (a F.eMinus n) (c (-n)) v := by
  rw [d0, LinearMap.smul_apply, unscaledD,
    (dFamily F).total_eq_sum v (modeBound F v) le_rfl]
  rw [signed_sum _ (by simp) (modeBound F v) (by
    intro r hr
    obtain ⟨h1,h2,h3,h4⟩ := modeBound_spec F v r hr
    change (if (r : ℤ)+1=0 then 0 else dm F ((r : ℤ)+1) v) = 0 ∧ (if -((r : ℤ)+1)=0 then 0 else dm F (-((r : ℤ)+1)) v) = 0
    simp only [if_neg (by omega : (r : ℤ)+1 ≠ 0), if_neg (by omega : -((r : ℤ)+1) ≠ 0), h1, h2, and_self])]
  exact congrArg (fun x : State D => F.pPlus p • x)
    (Finset.sum_congr rfl (fun r _ => by
      simp only [dFamily, dTerm, dm, LinearMap.add_apply,
        if_neg (by omega : (r : ℤ)+1 ≠ 0),
        if_neg (by omega : -((r : ℤ)+1) ≠ 0)]))

/-- The denominator is natAbs at BOTH signs. -/
theorem R_signed_formula (p : Charge D) (v : State D) :
    R F p v = (F.pPlus p)⁻¹ • ∑ᶠ n : ℤ, if n=0 then 0 else
      ((n.natAbs : ℂ)⁻¹) • tp (a F.ePlus (-n)) (b n) v := by
  rw [R, LinearMap.smul_apply, unscaledR,
    (rFamily F).total_eq_sum v (modeBound F v) le_rfl]
  rw [signed_sum _ (by simp) (modeBound F v) (by
    intro r hr
    obtain ⟨h1,h2,h3,h4⟩ := modeBound_spec F v r hr
    change (if (r : ℤ)+1=0 then 0 else _ • rr F ((r : ℤ)+1) v) = 0 ∧ (if -((r : ℤ)+1)=0 then 0 else _ • rr F (-((r : ℤ)+1)) v) = 0
    simp only [if_neg (by omega : (r : ℤ)+1 ≠ 0), if_neg (by omega : -((r : ℤ)+1) ≠ 0), h3, h4, smul_zero, and_self])]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have habs : Int.natAbs ((r : ℤ)+1) = r+1 := by omega
  simp only [rFamily, rTerm, rr, LinearMap.smul_apply, LinearMap.add_apply, habs, Int.natAbs_neg, Nat.cast_add, Nat.cast_one, smul_add, if_neg (by omega : (r : ℤ)+1 ≠ 0), if_neg (by omega : -((r : ℤ)+1) ≠ 0)]

end D5.S3.VertexAlgebra.LatticeQuartetContraction
