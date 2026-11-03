/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode
   mirror-E: none(waiver:algebraic-original-relative-zero-mode)
   anchors: []
   utility: none
   digest: Original finite BRST zero-mode decomposition and literal relative-shell stability. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeMassShell
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCovariance
import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
import D5.S3.Quantum.Fermionic.BcGhostSquare
import D5.S3.Quantum.Fermionic.BcGhostChargeTensor
import Mathlib.LinearAlgebra.Projection

/-! # Original BRST zero modes

Statewise finite decomposition and stability of the unshifted fixed-momentum relative shell.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open D5.S3.VertexAlgebra.LatticeBRST
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostBRST
open private cubic_eq c_swap from D5.S3.Quantum.Fermionic.BcGhostCubic
open private cc_b from D5.S3.Quantum.Fermionic.BcGhostSquare
open private summand_product from D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling

namespace D5.S3.VertexAlgebra.LatticeBRSTRelativeZeroMode
noncomputable section

abbrev State (D : LatticeData) := LatticeMatterGhostCoupling.State D
abbrev L0 (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Module.End ℂ (State D) := LatticeRelativeMassShell.totalL0 D H

private theorem filter_finite {α E : Type*} [Zero E]
    (f : α → E) (hf : Function.HasFiniteSupport f) (P : α → Prop)
    [DecidablePred P] :
    Function.HasFiniteSupport (fun a => if P a then f a else 0) := by
  apply hf.subset
  intro a ha hzero
  exact ha (by simp [hzero])

private theorem finsum_filter_split {α E : Type*} [AddCommMonoid E]
    (f : α → E) (hf : Function.HasFiniteSupport f) (P : α → Prop)
    [DecidablePred P] :
    (∑ᶠ a, f a) =
      (∑ᶠ a, if P a then f a else 0) +
        (∑ᶠ a, if ¬ P a then f a else 0) := by
  rw [← finsum_add_distrib (filter_finite f hf P)
    (filter_finite f hf (fun a => ¬ P a))]
  apply finsum_congr
  intro a
  by_cases h : P a <;> simp [h]

/-- The literal cubic terms with all three possible zero-mode positions removed. -/
def cubicZeroFree : Module.End ℂ Fock where
  toFun v := ∑ᶠ pq : ℤ × ℤ,
    if pq.1 ≠ 0 ∧ pq.2 ≠ 0 ∧ pq.1 + pq.2 ≠ 0 then cubicTerm pq v else 0
  map_add' v w := by
    rw [← finsum_add_distrib
      (filter_finite (fun pq : ℤ × ℤ => cubicTerm pq v)
        (cubicTerm_finite v) _)
      (filter_finite (fun pq : ℤ × ℤ => cubicTerm pq w)
        (cubicTerm_finite w) _)]
    apply finsum_congr
    intro pq
    by_cases h : pq.1 ≠ 0 ∧ pq.2 ≠ 0 ∧ pq.1 + pq.2 ≠ 0 <;>
      simp [h, map_add]
  map_smul' a v := by
    simp only [RingHom.id_apply]
    rw [smul_finsum' a
      (filter_finite (fun pq : ℤ × ℤ => cubicTerm pq v)
        (cubicTerm_finite v) (fun pq => pq.1 ≠ 0 ∧ pq.2 ≠ 0 ∧ pq.1 + pq.2 ≠ 0))]
    apply finsum_congr
    intro pq
    by_cases h : pq.1 ≠ 0 ∧ pq.2 ≠ 0 ∧ pq.1 + pq.2 ≠ 0 <;>
      simp [h]

/-- The actual matter summation with only its m = 0 term deleted. -/
def matterZeroFree (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ (State D) where
  toFun x := ∑ᶠ m : ℤ,
    if m ≠ 0 then summand D H m x else 0
  map_add' x y := by
    rw [← finsum_add_distrib
      (filter_finite (fun m : ℤ => summand D H m x)
        (summand_finite D H x) _)
      (filter_finite (fun m : ℤ => summand D H m y)
        (summand_finite D H y) _)]
    apply finsum_congr
    intro m
    by_cases h : m ≠ 0 <;> simp [h, map_add]
  map_smul' a x := by
    simp only [RingHom.id_apply]
    rw [smul_finsum' a
      (filter_finite (fun m : ℤ => summand D H m x)
        (summand_finite D H x) (fun m => m ≠ 0))]
    apply finsum_congr
    intro m
    by_cases h : m ≠ 0 <;> simp [h]

/-- The original tensor lift of the zero-mode-free cubic, not a replacement charge. -/
def ghostZeroFree (D : LatticeData) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id cubicZeroFree

def zeroModeFreeCharge (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ (State D) :=
  matterZeroFree D H + ghostZeroFree D

/-- Actual b/c CAR at zero, transported to the original tensor carrier. -/
theorem ghost_b_zero_square (D : LatticeData) :
    ghostB D 0 * ghostB D 0 = 0 := by
  have hF : b 0 * b 0 = 0 := by
    have h := BcGhostFock.ghost_b_car 0 0
    have h' : (2 : ℂ) • (b 0 * b 0) = 0 := by
      simpa only [two_smul] using h
    exact (smul_eq_zero.mp h').resolve_left (by norm_num)
  apply TensorProduct.ext'
  intro v w
  simp only [ghostB, Module.End.mul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearMap.zero_apply]
  have hw := LinearMap.congr_fun hF w
  simp only [Module.End.mul_apply, LinearMap.zero_apply] at hw
  rw [hw, TensorProduct.tmul_zero]

theorem ghost_c_zero_square (D : LatticeData) :
    ghostC D 0 * ghostC D 0 = 0 := by
  have hF : c 0 * c 0 = 0 := by
    have h := BcGhostFock.ghost_c_car 0 0
    have h' : (2 : ℂ) • (c 0 * c 0) = 0 := by
      simpa only [two_smul] using h
    exact (smul_eq_zero.mp h').resolve_left (by norm_num)
  apply TensorProduct.ext'
  intro v w
  simp only [ghostC, Module.End.mul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearMap.zero_apply]
  have hw := LinearMap.congr_fun hF w
  simp only [Module.End.mul_apply, LinearMap.zero_apply] at hw
  rw [hw, TensorProduct.tmul_zero]

theorem ghost_zero_mixed (D : LatticeData) :
    ghostB D 0 * ghostC D 0 + ghostC D 0 * ghostB D 0 =
      (1 : Module.End ℂ (State D)) := by
  apply TensorProduct.ext'
  intro v w
  simp only [ghostB, ghostC, LinearMap.add_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  have hw := LinearMap.congr_fun (BcGhostFock.ghost_mixed_car 0 0) w
  have hw' : b 0 (c 0 w) + c 0 (b 0 w) = w := by
    simpa only [LinearMap.add_apply, Module.End.mul_apply, zero_add,
      ite_true, Module.End.one_apply] using hw
  rw [← TensorProduct.tmul_add, hw']
  rfl

/-- The two complementary literal CAR projectors. -/
def bZeroProjector (D : LatticeData) : Module.End ℂ (State D) :=
  ghostB D 0 * ghostC D 0

def cZeroProjector (D : LatticeData) : Module.End ℂ (State D) :=
  ghostC D 0 * ghostB D 0

theorem ghostB_bZeroProjector (D : LatticeData) :
    ghostB D 0 * bZeroProjector D = 0 := by
  unfold bZeroProjector
  rw [← mul_assoc, ghost_b_zero_square, zero_mul]

theorem ghostC_cZeroProjector (D : LatticeData) :
    ghostC D 0 * cZeroProjector D = 0 := by
  unfold cZeroProjector
  rw [← mul_assoc, ghost_c_zero_square, zero_mul]

theorem bZeroProjector_fix_of_ker (D : LatticeData) (x : State D)
    (hx : ghostB D 0 x = 0) : bZeroProjector D x = x := by
  have h := congrArg (fun A : Module.End ℂ (State D) => A x)
    (ghost_zero_mixed D)
  change ghostB D 0 (ghostC D 0 x) = x
  simpa only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
    hx, map_zero, add_zero] using h

theorem cZeroProjector_fix_of_ker (D : LatticeData) (x : State D)
    (hx : ghostC D 0 x = 0) : cZeroProjector D x = x := by
  have h := congrArg (fun A : Module.End ℂ (State D) => A x)
    (ghost_zero_mixed D)
  change ghostC D 0 (ghostB D 0 x) = x
  simpa only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
    hx, map_zero, zero_add] using h

/-- The literal b0-c0 product is a genuine projection onto the b0 kernel. -/
theorem bZeroProjector_isProj (D : LatticeData) :
    LinearMap.IsProj (LinearMap.ker (ghostB D 0)) (bZeroProjector D) where
  map_mem x := LinearMap.congr_fun (ghostB_bZeroProjector D) x
  map_id x hx := bZeroProjector_fix_of_ker D x hx

/-- The literal c0-b0 product is a genuine projection onto the c0 kernel. -/
theorem cZeroProjector_isProj (D : LatticeData) :
    LinearMap.IsProj (LinearMap.ker (ghostC D 0)) (cZeroProjector D) where
  map_mem x := LinearMap.congr_fun (ghostC_cZeroProjector D) x
  map_id x hx := cZeroProjector_fix_of_ker D x hx

/-- The two actual complementary projections, carrying their kernel laws. -/
def zeroModeDecomposition (D : LatticeData) :
    State D ≃ₗ[ℂ] (LinearMap.ker (ghostB D 0) × LinearMap.ker (ghostC D 0)) where
  toFun x := ((bZeroProjector_isProj D).codRestrict x,
    (cZeroProjector_isProj D).codRestrict x)
  invFun y := (y.1 : State D) + (y.2 : State D)
  left_inv x := by
    exact LinearMap.congr_fun (ghost_zero_mixed D) x
  right_inv y := by
    apply Prod.ext <;> apply Subtype.ext
    · change bZeroProjector D ((y.1 : State D) + (y.2 : State D)) = y.1
      rw [map_add, bZeroProjector_fix_of_ker D _ y.1.property]
      change (y.1 : State D) + ghostB D 0 (ghostC D 0 y.2) = y.1
      rw [y.2.property, map_zero, add_zero]
    · change cZeroProjector D ((y.1 : State D) + (y.2 : State D)) = y.2
      rw [map_add, cZeroProjector_fix_of_ker D _ y.2.property]
      change ghostC D 0 (ghostB D 0 y.1) + (y.2 : State D) = y.2
      rw [y.1.property, map_zero, zero_add]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> exact map_add _ x y
  map_smul' a x := by
    apply Prod.ext <;> apply Subtype.ext <;> exact map_smul _ a x

/-- The pure-c Ward operator has no zero-mode commutator with b_0. -/
private theorem rTerm_b_zero (p : ℤ) :
    BcGhostBRST.rTerm 0 p * b 0 - b 0 * BcGhostBRST.rTerm 0 p = 0 := by
  by_cases hp : p = 0
  · subst p
    simp [BcGhostBRST.rTerm]
  · have hcc : (c p * c (-p)) * b 0 - b 0 * (c p * c (-p)) = 0 := by
      simpa [hp] using cc_b p (-p) 0
    simp only [BcGhostBRST.rTerm, zero_sub]
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, hcc, smul_zero]

private theorem R_b_zero :
    BcGhostBRST.R 0 * b 0 - b 0 * BcGhostBRST.R 0 = 0 := by
  apply LinearMap.ext
  intro w
  have hw := BcGhostBRST.rTerm_finite 0 w
  have hbw := BcGhostBRST.rTerm_finite 0 (b 0 w)
  have hmap := hw.fun_comp (map_zero (b 0))
  change (∑ᶠ p : ℤ, BcGhostBRST.rTerm 0 p (b 0 w)) -
      b 0 (∑ᶠ p : ℤ, BcGhostBRST.rTerm 0 p w) = 0
  rw [map_finsum (b 0) hw, ← finsum_sub_distrib hbw hmap]
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply]
    using LinearMap.congr_fun (rTerm_b_zero p) w

private theorem ghostR_b_zero (D : LatticeData) :
    ghostR D 0 * ghostB D 0 - ghostB D 0 * ghostR D 0 = 0 := by
  apply TensorProduct.ext'
  intro v w
  simp only [ghostR, ghostB, LinearMap.sub_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply]
  have hw := LinearMap.congr_fun R_b_zero w
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at hw
  rw [← TensorProduct.tmul_sub, hw, TensorProduct.tmul_zero]

/-- The actual total L_0 commutes with b_0; this uses the m=r=0 Ward law. -/
theorem totalL0_b_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    L0 D H * ghostB D 0 - ghostB D 0 * L0 D H = 0 := by
  have hm : matterMode D H 0 * ghostB D 0 - ghostB D 0 * matterMode D H 0 = 0 := by
    apply TensorProduct.ext'
    intro v w
    simp only [matterMode, ghostB, LinearMap.sub_apply, Module.End.mul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply, sub_self]
  have hg' : ghostVirasoro D 0 * ghostB D 0 -
      ghostB D 0 * ghostVirasoro D 0 = 0 := by
    apply TensorProduct.ext'
    intro v w
    have hw := LinearMap.congr_fun (BcGhostVirasoro.ward_b 0 0) w
    have hw' : BcGhostVirasoro.L 0 (b 0 w) -
        b 0 (BcGhostVirasoro.L 0 w) = 0 := by
      simpa using hw
    simp only [ghostVirasoro, ghostB, LinearMap.sub_apply, Module.End.mul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply]
    rw [← TensorProduct.tmul_sub, hw', TensorProduct.tmul_zero]
  change (matterMode D H 0 + ghostVirasoro D 0) * ghostB D 0 -
      ghostB D 0 * (matterMode D H 0 + ghostVirasoro D 0) = 0
  calc
    _ = (matterMode D H 0 * ghostB D 0 - ghostB D 0 * matterMode D H 0) +
        (ghostVirasoro D 0 * ghostB D 0 - ghostB D 0 * ghostVirasoro D 0) := by
      noncomm_ring
    _ = 0 := by rw [hm, hg', add_zero]

/-- The original charge after subtracting its two literal zero Ward terms. -/
def Qhat (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ (State D) :=
  totalCharge D H - ghostC D 0 * L0 D H - ghostB D 0 * ghostR D 0

/-- Its b_0 anticommutator vanishes, with the signs fixed by the original CAR. -/
theorem Qhat_b_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Qhat D H * ghostB D 0 + ghostB D 0 * Qhat D H = 0 := by
  have hward : totalCharge D H * ghostB D 0 + ghostB D 0 * totalCharge D H =
      L0 D H := total_ward_b D H 0
  have hL := sub_eq_zero.mp (totalL0_b_zero D H)
  have hR := sub_eq_zero.mp (ghostR_b_zero D)
  have hcL : (ghostC D 0 * L0 D H) * ghostB D 0 +
      ghostB D 0 * (ghostC D 0 * L0 D H) = L0 D H := by
    calc
      _ = (ghostC D 0 * ghostB D 0 + ghostB D 0 * ghostC D 0) * L0 D H := by
        rw [mul_assoc (ghostC D 0) (L0 D H), hL]
        noncomm_ring
      _ = L0 D H := by
        rw [add_comm (ghostC D 0 * ghostB D 0), ghost_zero_mixed, one_mul]
  have hbR : (ghostB D 0 * ghostR D 0) * ghostB D 0 +
      ghostB D 0 * (ghostB D 0 * ghostR D 0) = 0 := by
    calc
      _ = (ghostB D 0 * ghostB D 0) * ghostR D 0 +
          (ghostB D 0 * ghostB D 0) * ghostR D 0 := by
        rw [mul_assoc (ghostB D 0) (ghostR D 0), hR]
        noncomm_ring
      _ = 0 := by rw [ghost_b_zero_square]; simp
  unfold Qhat
  calc
    _ = (totalCharge D H * ghostB D 0 + ghostB D 0 * totalCharge D H) -
        ((ghostC D 0 * L0 D H) * ghostB D 0 +
          ghostB D 0 * (ghostC D 0 * L0 D H)) -
        ((ghostB D 0 * ghostR D 0) * ghostB D 0 +
          ghostB D 0 * (ghostB D 0 * ghostR D 0)) := by
      simp only [sub_mul, mul_sub, mul_assoc]
      abel
    _ = 0 := by rw [hward, hcL, hbR, sub_self, sub_zero]

/-- The zero row and column are computed using the supplier's actual cyclic ordering. -/
private theorem cubicTerm_zero_row (q : ℤ) :
    cubicTerm (0,q) + cubicTerm (q,0) =
      c 0 * BcGhostVirasoro.summand 0 q := by
  have hswap : cubic q 0 = -cubic 0 q := by
    simp only [cubic_eq, neg_zero, sub_zero, zero_sub]
    by_cases ht : -q ≤ -2
    · simp only [ht, ite_true]
      rw [mul_assoc, c_swap q 0, mul_neg, ← mul_assoc]
    · simp only [ht, ite_false]
      rw [c_swap q 0, neg_mul]
  have hnormal : c 0 * BcGhostVirasoro.summand 0 q =
      -(q : ℂ) • cubic 0 q := by
    simp only [BcGhostVirasoro.summand, zero_add, mul_smul_comm,
      cubic_eq, neg_zero, zero_sub, BcGhostVirasoro.normal]
    by_cases ht : -q ≤ -2
    · have hb : c 0 * b (-q) = -(b (-q) * c 0) := by
        have h : b (-q) * c 0 + c 0 * b (-q) = 0 := by
          rw [BcGhostFock.ghost_mixed_car, ite_eq_right (by omega)]
        exact eq_neg_of_add_eq_zero_right h
      simp only [ht, ite_true]
      rw [← mul_assoc, hb, neg_mul, smul_neg, neg_smul]
    · simp only [ht, ite_false, mul_neg, smul_neg, neg_smul, mul_assoc]
  rw [hnormal]
  simp only [cubicTerm, zero_sub, sub_zero]
  rw [hswap]
  module

private theorem cubicTerm_zero_diag (p : ℤ) :
    cubicTerm (p,-p) = b 0 * BcGhostBRST.rTerm 0 p := by
  by_cases hp : p = 0
  · subst p
    simp [cubicTerm, BcGhostBRST.rTerm]
  · have hbc : b 0 * c p * c (-p) = c p * c (-p) * b 0 := by
      calc
        _ = (b 0 * c p + c p * b 0) * c (-p) -
            c p * (b 0 * c (-p) + c (-p) * b 0) +
            c p * c (-p) * b 0 := by noncomm_ring
        _ = _ := by
          rw [BcGhostFock.ghost_mixed_car, BcGhostFock.ghost_mixed_car]
          simp [hp]
    have hz : -p - -p = (0 : ℤ) := by omega
    simp only [cubicTerm, cubic_eq, hz, show ¬ (0 : ℤ) ≤ -2 by omega,
      ite_false, BcGhostBRST.rTerm, zero_sub, sub_zero, mul_smul_comm]
    rw [← mul_assoc, hbc]
    congr 1
    push_cast
    ring

/-- Finite row/column reindexing, with the (0,0) overlap proved zero. -/
private theorem cubic_zero_rows (v : Fock) :
    (∑ᶠ pq : ℤ × ℤ, if pq.1 = 0 ∨ pq.2 = 0 then cubicTerm pq v else 0) =
      c 0 (BcGhostVirasoro.L 0 v) := by
  classical
  have hf := cubicTerm_finite v
  have hp : Function.HasFiniteSupport (fun q : ℤ => cubicTerm (0,q) v) := by
    apply (hf.toFinset.image Prod.snd).finite_toSet.subset
    intro q hq
    exact Finset.mem_image.mpr ⟨(0,q), by simpa using hq, rfl⟩
  have hq : Function.HasFiniteSupport (fun p : ℤ => cubicTerm (p,0) v) := by
    apply (hf.toFinset.image Prod.fst).finite_toSet.subset
    intro p hp
    exact Finset.mem_image.mpr ⟨(p,0), by simpa using hp, rfl⟩
  have hrow := filter_finite (fun pq : ℤ × ℤ => cubicTerm pq v) hf
    (fun pq => pq.1 = 0)
  have hcol := filter_finite (fun pq : ℤ × ℤ => cubicTerm pq v) hf
    (fun pq => pq.2 = 0)
  have hrow' : (∑ᶠ pq : ℤ × ℤ,
      if pq.1 = 0 then cubicTerm pq v else 0) =
      ∑ᶠ q : ℤ, cubicTerm (0,q) v := by
    rw [finsum_curry _ hrow]
    rw [finsum_eq_single _ 0 (fun p hp => by simp [hp])]
    simp
  have hcol' : (∑ᶠ pq : ℤ × ℤ,
      if pq.2 = 0 then cubicTerm pq v else 0) =
      ∑ᶠ p : ℤ, cubicTerm (p,0) v := by
    rw [finsum_curry _ hcol]
    apply finsum_congr
    intro p
    rw [finsum_eq_single _ 0 (fun q hq => by simp [hq])]
    simp
  have hoverlap : cubicTerm (0,0) v = 0 := by simp [cubicTerm]
  have hunion : (∑ᶠ pq : ℤ × ℤ,
      if pq.1 = 0 ∨ pq.2 = 0 then cubicTerm pq v else 0) =
      (∑ᶠ pq : ℤ × ℤ, if pq.1 = 0 then cubicTerm pq v else 0) +
        (∑ᶠ pq : ℤ × ℤ, if pq.2 = 0 then cubicTerm pq v else 0) := by
    rw [← finsum_add_distrib hrow hcol]
    apply finsum_congr
    intro pq
    by_cases hp0 : pq.1 = 0 <;> by_cases hq0 : pq.2 = 0
    · have he : pq = (0,0) := Prod.ext hp0 hq0
      simp [he, hoverlap]
    all_goals simp [hp0, hq0]
  rw [hunion, hrow', hcol', ← finsum_add_distrib hp hq]
  change (∑ᶠ q : ℤ, (cubicTerm (0,q) v + cubicTerm (q,0) v)) =
    c 0 (∑ᶠ q : ℤ, BcGhostVirasoro.summand 0 q v)
  rw [map_finsum (c 0) (BcGhostVirasoro.summand_finite 0 v)]
  apply finsum_congr
  intro q
  simpa only [LinearMap.add_apply, Module.End.mul_apply] using
    LinearMap.congr_fun (cubicTerm_zero_row q) v

private theorem cubic_zero_diag (v : Fock) :
    (∑ᶠ pq : ℤ × ℤ,
      if pq.1 + pq.2 = 0 ∧ pq.1 ≠ 0 ∧ pq.2 ≠ 0 then cubicTerm pq v else 0) =
      b 0 (BcGhostBRST.R 0 v) := by
  classical
  have hf := cubicTerm_finite v
  have hg := filter_finite (fun pq : ℤ × ℤ => cubicTerm pq v) hf
    (fun pq => pq.2 = -pq.1)
  have hgraph : (∑ᶠ pq : ℤ × ℤ,
      if pq.2 = -pq.1 then cubicTerm pq v else 0) =
      ∑ᶠ p : ℤ, cubicTerm (p,-p) v := by
    rw [finsum_curry _ hg]
    apply finsum_congr
    intro p
    rw [finsum_eq_single _ (-p) (fun q hq => by simp [hq])]
    simp
  have hremove : (∑ᶠ pq : ℤ × ℤ,
      if pq.2 = -pq.1 then cubicTerm pq v else 0) =
      (∑ᶠ pq : ℤ × ℤ,
        if pq.1 + pq.2 = 0 ∧ pq.1 ≠ 0 ∧ pq.2 ≠ 0 then cubicTerm pq v else 0) := by
    apply finsum_congr
    intro pq
    by_cases he : pq.2 = -pq.1
    · by_cases hp : pq.1 = 0
      · have hq : pq.2 = 0 := by omega
        have hz : pq = (0,0) := Prod.ext hp hq
        simp [hz, cubicTerm]
      · have hq : pq.2 ≠ 0 := by omega
        have hs : pq.1 + pq.2 = 0 := by omega
        simp [he, hp]
    · have hs : pq.1 + pq.2 ≠ 0 := by omega
      simp [he, hs]
  rw [← hremove, hgraph]
  change (∑ᶠ p : ℤ, cubicTerm (p,-p) v) =
    b 0 (∑ᶠ p : ℤ, BcGhostBRST.rTerm 0 p v)
  rw [map_finsum (b 0) (BcGhostBRST.rTerm_finite 0 v)]
  apply finsum_congr
  intro p
  simpa only [Module.End.mul_apply] using
    LinearMap.congr_fun (cubicTerm_zero_diag p) v

/-- The exact original cubic finite-term identity (zero row + zero diagonal + tail). -/
theorem ghost_zero_split (v : Fock) :
    BcGhostBRST.Qg v = c 0 (BcGhostVirasoro.L 0 v) +
      b 0 (BcGhostBRST.R 0 v) + cubicZeroFree v := by
  classical
  let f : ℤ × ℤ → Fock := fun pq => cubicTerm pq v
  let P : ℤ × ℤ → Prop := fun pq => pq.1 = 0 ∨ pq.2 = 0
  let N : ℤ × ℤ → Fock := fun pq => if ¬ P pq then f pq else 0
  have hf : Function.HasFiniteSupport f := cubicTerm_finite v
  have hN : Function.HasFiniteSupport N := filter_finite f hf (fun pq => ¬ P pq)
  have hsplit := finsum_filter_split f hf P
  have htail := finsum_filter_split N hN (fun pq => pq.1 + pq.2 = 0)
  have hdiag : (∑ᶠ pq : ℤ × ℤ, if pq.1 + pq.2 = 0 then N pq else 0) =
      ∑ᶠ pq : ℤ × ℤ,
        if pq.1 + pq.2 = 0 ∧ pq.1 ≠ 0 ∧ pq.2 ≠ 0 then cubicTerm pq v else 0 := by
    apply finsum_congr
    intro pq
    by_cases hp : pq.1 = 0 <;> by_cases hq : pq.2 = 0 <;>
      by_cases hd : pq.1 + pq.2 = 0 <;> simp [N, P, f, hp, hq, hd]
  have hfree : (∑ᶠ pq : ℤ × ℤ, if ¬ (pq.1 + pq.2 = 0) then N pq else 0) =
      cubicZeroFree v := by
    change _ = ∑ᶠ pq : ℤ × ℤ,
      if pq.1 ≠ 0 ∧ pq.2 ≠ 0 ∧ pq.1 + pq.2 ≠ 0 then cubicTerm pq v else 0
    apply finsum_congr
    intro pq
    by_cases hp : pq.1 = 0 <;> by_cases hq : pq.2 = 0 <;>
      by_cases hd : pq.1 + pq.2 = 0 <;> simp [N, P, f, hp, hq, hd]
  change (∑ᶠ pq : ℤ × ℤ, f pq) = _
  rw [hsplit, htail, hdiag, hfree]
  change (∑ᶠ pq : ℤ × ℤ, if pq.1 = 0 ∨ pq.2 = 0 then cubicTerm pq v else 0) +
    ((∑ᶠ pq : ℤ × ℤ,
      if pq.1 + pq.2 = 0 ∧ pq.1 ≠ 0 ∧ pq.2 ≠ 0 then cubicTerm pq v else 0) +
        cubicZeroFree v) = _
  rw [cubic_zero_rows, cubic_zero_diag, add_assoc]

/-- The matter zero-mode term is the actual m=0 summand, with no redefinition. -/
theorem matter_zero_split (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D) :
    T D H x = (matterMode D H 0 * ghostC D 0) x +
      matterZeroFree D H x := by
  classical
  have hf := summand_finite D H x
  change (∑ᶠ m : ℤ, summand D H m x) = _
  rw [finsum_filter_split _ hf (fun m : ℤ => m = 0)]
  have hz : (∑ᶠ m : ℤ, if m = 0 then summand D H m x else 0) =
      summand D H 0 x := by
    rw [finsum_eq_single _ 0 (fun m hm => by simp [hm])]
    simp
  rw [hz]
  simp only [matterZeroFree]
  rw [summand_product]
  rfl

/-- The zero-mode-free sum is exactly the original charge after the Ward terms. -/
theorem original_charge_split (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D) :
    totalCharge D H x = ghostC D 0 (L0 D H x) + ghostB D 0 (ghostR D 0 x) +
      zeroModeFreeCharge D H x := by
  -- The following tensor extensionality step is the literal lift of `ghost_zero_split`.
  have hgl : ghostCharge D x = ghostC D 0 (ghostVirasoro D 0 x) +
      ghostB D 0 (ghostR D 0 x) + ghostZeroFree D x := by
    induction x using TensorProduct.inductionOn with
    | tmul v w =>
        simp only [ghostCharge, ghostC, ghostB, ghostVirasoro, ghostR,
          ghostZeroFree, TensorProduct.map_tmul, LinearMap.id_apply]
        simpa only [TensorProduct.tmul_add] using
          congrArg (fun z : Fock => v ⊗ₜ[ℂ] z) (ghost_zero_split w)
    | add x y hx hy =>
        simp only [map_add, hx, hy]
        abel
  have hm := matter_zero_split D H x
  have hcomm : matterMode D H 0 * ghostC D 0 =
      ghostC D 0 * matterMode D H 0 := by
    apply TensorProduct.ext'
    intro v w
    simp only [matterMode, ghostC, Module.End.mul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply]
  change T D H x + ghostCharge D x = _
  rw [hm, hgl, hcomm]
  change ghostC D 0 (matterMode D H 0 x) + matterZeroFree D H x +
    (ghostC D 0 (ghostVirasoro D 0 x) + ghostB D 0 (ghostR D 0 x) +
      ghostZeroFree D x) = _
  simp only [L0, LatticeRelativeMassShell.totalL0, zeroModeFreeCharge,
    LinearMap.add_apply, map_add]
  abel

/-- The subtracted charge is the explicit statewise finite zero-mode-free sum. -/
theorem Qhat_eq_zeroModeFree (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Qhat D H = zeroModeFreeCharge D H := by
  apply LinearMap.ext
  intro x
  change totalCharge D H x - ghostC D 0 (L0 D H x) -
    ghostB D 0 (ghostR D 0 x) = zeroModeFreeCharge D H x
  rw [original_charge_split D H x]
  abel

/-- Literal equality on the physical relative shell; R_0 is EVEN.
The ordinary commutator is essential: b_0 x = 0 alone cannot simplify b_0 R_0 x. -/
theorem Qhat_eq_original_on_relative_shell (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D)
    (hb : ghostB D 0 x = 0) (hL : L0 D H x = 0) :
    Qhat D H x = totalCharge D H x := by
  have hRb := sub_eq_zero.mp (ghostR_b_zero D)
  have hbx : ghostB D 0 (ghostR D 0 x) = 0 := by
    calc
      _ = ghostR D 0 (ghostB D 0 x) :=
        (LinearMap.congr_fun hRb x).symm
      _ = 0 := by rw [hb, map_zero]
  change totalCharge D H x - ghostC D 0 (L0 D H x) -
    ghostB D 0 (ghostR D 0 x) = totalCharge D H x
  rw [hL, map_zero, hbx, sub_zero, sub_zero]

/-- The actual r=0 covariance has zero anomaly for EVERY rank. -/
private theorem totalCharge_totalL0_comm (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) :
    L0 D H * totalCharge D H - totalCharge D H * L0 D H = 0 := by
  have h : totalCharge D H * L0 D H - L0 D H * totalCharge D H = 0 := by
    simpa only [Int.cast_zero, zero_pow (by decide : 3 ≠ 0), sub_zero,
      mul_zero, zero_smul] using total_covariance D H hHG hGH 0
  exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm

private theorem totalL0_c_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    L0 D H * ghostC D 0 - ghostC D 0 * L0 D H = 0 := by
  have hm : matterMode D H 0 * ghostC D 0 - ghostC D 0 * matterMode D H 0 = 0 := by
    apply TensorProduct.ext'
    intro v w
    simp only [matterMode, ghostC, LinearMap.sub_apply, Module.End.mul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply, sub_self]
  have hg : ghostVirasoro D 0 * ghostC D 0 - ghostC D 0 * ghostVirasoro D 0 = 0 := by
    apply TensorProduct.ext'
    intro v w
    have hw := LinearMap.congr_fun (BcGhostVirasoro.ward_c 0 0) w
    have hw' : BcGhostVirasoro.L 0 (c 0 w) -
        c 0 (BcGhostVirasoro.L 0 w) = 0 := by
      simpa using hw
    simp only [ghostVirasoro, ghostC, LinearMap.sub_apply, Module.End.mul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply]
    rw [← TensorProduct.tmul_sub, hw', TensorProduct.tmul_zero]
  change (matterMode D H 0 + ghostVirasoro D 0) * ghostC D 0 -
    ghostC D 0 * (matterMode D H 0 + ghostVirasoro D 0) = 0
  calc
    _ = (matterMode D H 0 * ghostC D 0 - ghostC D 0 * matterMode D H 0) +
        (ghostVirasoro D 0 * ghostC D 0 - ghostC D 0 * ghostVirasoro D 0) := by
      noncomm_ring
    _ = 0 := by rw [hm, hg, add_zero]

private theorem totalL0_R_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    L0 D H * ghostR D 0 - ghostR D 0 * L0 D H = 0 := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun (BcGhostBRST.R_covariance 0 0) w
  have h' : BcGhostVirasoro.L 0 (BcGhostBRST.R 0 w) -
      BcGhostBRST.R 0 (BcGhostVirasoro.L 0 w) = 0 := by
    simpa using h
  simp only [L0, LatticeRelativeMassShell.totalL0, matterMode, ghostVirasoro,
    ghostR, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply, map_add]
  rw [add_sub_add_left_eq_sub, ← TensorProduct.tmul_sub, h', TensorProduct.tmul_zero]

/-- Qhat's L0 commutator follows from the ACTUAL zero-mode Ward equations. -/
theorem Qhat_totalL0_comm (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) :
    L0 D H * Qhat D H - Qhat D H * L0 D H = 0 := by
  unfold Qhat
  calc
    _ = (L0 D H * totalCharge D H - totalCharge D H * L0 D H) -
        (L0 D H * ghostC D 0 - ghostC D 0 * L0 D H) * L0 D H -
        ((L0 D H * ghostB D 0 - ghostB D 0 * L0 D H) * ghostR D 0 +
          ghostB D 0 * (L0 D H * ghostR D 0 - ghostR D 0 * L0 D H)) := by
      generalize L0 D H = A
      generalize totalCharge D H = Q
      generalize ghostC D 0 = C
      generalize ghostB D 0 = B
      generalize ghostR D 0 = R
      simp only [sub_mul, mul_sub, add_mul, mul_add, mul_assoc]
      abel
    _ = 0 := by
      rw [totalCharge_totalL0_comm D H hHG hGH, totalL0_c_zero,
        totalL0_b_zero, totalL0_R_zero D H]
      simp

theorem Qhat_preserves_b0_kernel (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D)
    (hx : ghostB D 0 x = 0) : ghostB D 0 (Qhat D H x) = 0 := by
  have h := LinearMap.congr_fun (Qhat_b_zero D H) x
  simpa only [LinearMap.add_apply, Module.End.mul_apply, hx, map_zero,
    zero_add, LinearMap.zero_apply] using h

theorem Qhat_preserves_L0_kernel (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) (x : State D)
    (hx : L0 D H x = 0) : L0 D H (Qhat D H x) = 0 := by
  have h := LinearMap.congr_fun (Qhat_totalL0_comm D H hHG hGH) x
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, hx, map_zero,
    sub_zero, LinearMap.zero_apply] using h

/-- The same actual shell is preserved by Qhat because the corrected equality
identifies its action with Q there, including the fixed-momentum component. -/
theorem Qhat_preserves_relativeMassShell (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (a : Charge D) (x : State D)
    (hx : x ∈ LatticeRelativeMassShell.relativeMassShell D H a) :
    Qhat D H x ∈ LatticeRelativeMassShell.relativeMassShell D H a := by
  exact ⟨⟨by
    rw [Qhat_eq_original_on_relative_shell D H x hx.1.2 hx.2]
    exact LatticeRelativeMassShell.totalCharge_mem_fixedMomentum D H a hx.1.1,
    Qhat_preserves_b0_kernel D H x hx.1.2⟩,
    Qhat_preserves_L0_kernel D H hHG hGH x hx.2⟩

/-- The actual Qhat action restricted to the original fixed-momentum relative shell. -/
def relativeQhat (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) (a : Charge D) :
    Module.End ℂ (LatticeRelativeMassShell.relativeMassShell D H a) :=
  (zeroModeFreeCharge D H).restrict (fun x hx => by
    rw [← Qhat_eq_zeroModeFree D H]
    exact Qhat_preserves_relativeMassShell D H hHG hGH a x hx)

end
end D5.S3.VertexAlgebra.LatticeBRSTRelativeZeroMode
