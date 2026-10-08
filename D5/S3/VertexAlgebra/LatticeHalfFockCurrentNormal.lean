/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCurrentNormal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCurrentNormal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual half-integer lattice currents, finite normal sums and Virasoro fields. -/

/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Additional actual half-integer matrix implementation copyright (c) 2026.
Released under Apache 2.0.
Finite support, contraction and induction architecture adapted from
VirasoroProject 5ff4245383b2cdd4eea7a0524bc1274c32041eb4 through the completed
trureturing PolynomialFock sources at bfd9ff0f15397a4fb933f36d701a60d325d84b08.
Actual multicolour half-index operators and their proofs are retained from the
completed half-Fock producer; see notes/NOTICE.md and DeclarationMapping.json.
DN math/9808088v1, section 3.2, pp.12--14; rank/16 on p.19, proof of 3.13(3),
attributed there to FLM. BK math/0402315v1 (4.4), pp.10--13 (4.23)--(4.38).
-/
import D5.S3.VertexAlgebra.LatticeActualAnnihilation
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFock
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration MvPolynomial
open LatticeActualAnnihilation
open scoped BigOperators TensorProduct
noncomputable section

/-- The actual complex Gram matrix; no research Sugawara excerpt import is needed. -/
abbrev gramComplex (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  D.G.map (Int.cast : ℤ → ℂ)

def frequency (j : ℤ) : ℂ := (j : ℂ) + 1/2

def current (D : LatticeData) (i : Fin D.rank) (j : ℤ) :
    Module.End ℂ (Oscillator D) :=
  if j < 0 then LinearMap.mulLeft ℂ (X (i,(-j-1).toNat))
  else frequency j • annihilate D i j.toNat

theorem frequency_opposite (j : ℤ) : frequency (-j-1) = -frequency j := by
  simp only [frequency, Int.cast_sub, Int.cast_neg, Int.cast_one]
  ring

@[simp] theorem current_negative (D : LatticeData) (i : Fin D.rank) (k : ℕ) :
    current D i (-(k : ℤ)-1) = LinearMap.mulLeft ℂ (X (i,k)) := by
  simp [current, show -(k : ℤ)-1 < 0 by omega,
    show -(-(k : ℤ)-1)-1 = (k : ℤ) by omega]

private theorem positive_negative_commutator (D : LatticeData) (i l : Fin D.rank)
    (j k : ℤ) (hj : 0 ≤ j) (hk : k < 0) (p : Oscillator D) :
    current D i j (current D l k p) - current D l k (current D i j p) =
      if j+k+1 = 0 then (frequency j * (D.G i l : ℂ)) • p else 0 := by
  have hidx : j.toNat = (-k-1).toNat ↔ j+k+1 = 0 := by omega
  simp only [current, not_lt.mpr hj, hk, if_false, if_true,
    LinearMap.smul_apply, LinearMap.mulLeft_apply]
  rw [mul_smul_comm, ← smul_sub, annihilate_mul, annihilate_X, add_sub_cancel_right]
  simp only [hidx]
  split_ifs <;> simp [smul_smul]

theorem current_heisenberg_apply (D : LatticeData) (i l : Fin D.rank)
    (j k : ℤ) (p : Oscillator D) :
    current D i j (current D l k p) - current D l k (current D i j p) =
      if j+k+1 = 0 then (frequency j * (D.G i l : ℂ)) • p else 0 := by
  classical
  by_cases hj : j < 0
  · by_cases hk : k < 0
    · simp [current, hj, hk, show j+k+1 ≠ 0 by omega,
        LinearMap.mulLeft_apply, mul_left_comm]
    · have h := positive_negative_commutator D l i k j (by omega) hj p
      by_cases hz : j+k+1 = 0
      · have he : k = -j-1 := by omega
        rw [if_pos (show k+j+1 = 0 by omega), he, frequency_opposite,
          D.symmetric l i, neg_mul, neg_smul] at h
        rw [if_pos hz]
        rw [he]
        linear_combination -h
      · rw [if_neg (show k+j+1 ≠ 0 by omega)] at h
        rw [if_neg hz]
        exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm
  · by_cases hk : k < 0
    · exact positive_negative_commutator D i l j k (by omega) hk p
    · simp only [current, hj, hk, if_false, LinearMap.smul_apply,
        show j+k+1 ≠ 0 by omega]
      rw [map_smul, map_smul]
      run_tac
        let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeSugawaraCurrents 0).append
          `D5.S3.VertexAlgebra.LatticeSugawaraCurrents.weightedPartial_commute
        Lean.Elab.Tactic.evalTactic (← `(tactic| rw [($(Lean.mkIdent supplier))]))
      rw [smul_comm, sub_self]

theorem current_heisenberg (D : LatticeData) (i l : Fin D.rank) (j k : ℤ) :
    current D i j * current D l k - current D l k * current D i j =
      (if j+k+1 = 0 then frequency j * (D.G i l : ℂ) else 0) •
        (1 : Module.End ℂ (Oscillator D)) := by
  apply LinearMap.ext
  intro p
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, ite_smul, zero_smul, DFunLike.ite_apply, LinearMap.zero_apply] using
      current_heisenberg_apply D i l j k p

def bound (D : LatticeData) (p : Oscillator D) : ℕ :=
  p.vars.sup (fun x : Index D => x.2+1)

theorem current_vanish (D : LatticeData) (i : Fin D.rank)
    (p : Oscillator D) (j : ℤ) (hj : (bound D p : ℤ) ≤ j) :
    current D i j p = 0 := by
  classical
  have hjpos : 0 ≤ j := by omega
  have hd (l : Fin D.rank) : pderiv (l,j.toNat) p = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro hm
    have hb := Finset.le_sup (f := fun x : Index D => x.2+1) hm
    change j.toNat+1 ≤ bound D p at hb
    have hc : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hjpos
    omega
  simp [current, not_lt.mpr hjpos, annihilate, LatticeSugawaraCurrents.weightedPartial, hd]

def normalPair (D : LatticeData) (i l : Fin D.rank) (j k : ℤ) :
    Module.End ℂ (Oscillator D) :=
  if j < 0 then current D i j * current D l k
  else current D l k * current D i j

theorem normalPair_support_of_bound (D : LatticeData) (i l : Fin D.rank)
    (m : ℤ) (p : Oscillator D) (R : ℕ)
    (hR : ∀ (a : Fin D.rank) (j : ℤ), (R : ℤ) ≤ j → current D a j p = 0) :
    Function.support (fun j : ℤ => normalPair D i l j (m-j-1) p) ⊆
      Set.Icc (min (m-R) 0) ((R : ℤ)-1) := by
  intro j hj
  by_contra h
  have ho : j < min (m-R) 0 ∨ (R : ℤ) ≤ j := by
    simp only [Set.mem_Icc, not_and_or, not_le] at h
    omega
  rcases ho with hlo | hhi
  · have hjneg : j < 0 := lt_of_lt_of_le hlo (min_le_right _ _)
    have hk : (R : ℤ) ≤ m-j-1 := by
      have := lt_of_lt_of_le hlo (min_le_left _ _)
      omega
    exact hj (by simp [normalPair, hjneg, Module.End.mul_apply, hR l _ hk])
  · have hjpos : ¬ j < 0 := by omega
    exact hj (by simp [normalPair, hjpos, Module.End.mul_apply, hR i _ hhi])

theorem normalPair_support_interval (D : LatticeData) (i l : Fin D.rank)
    (m : ℤ) (p : Oscillator D) :
    Function.support (fun j : ℤ => normalPair D i l j (m-j-1) p) ⊆
      Set.Icc (min (m-bound D p) 0) ((bound D p : ℤ)-1) :=
  normalPair_support_of_bound D i l m p (bound D p)
    (fun a j hj => current_vanish D a p j hj)

theorem normalPair_finite (D : LatticeData) (i l : Fin D.rank)
    (m : ℤ) (p : Oscillator D) :
    Function.HasFiniteSupport (fun j : ℤ => normalPair D i l j (m-j-1) p) :=
  (Set.finite_Icc _ _).subset (normalPair_support_interval D i l m p)

def normalSum (D : LatticeData) (i l : Fin D.rank) (m : ℤ) :
    Module.End ℂ (Oscillator D) where
  toFun p := ∑ᶠ j : ℤ, normalPair D i l j (m-j-1) p
  map_add' p q := by
    simp only [map_add]
    exact finsum_add_distrib (normalPair_finite D i l m p) (normalPair_finite D i l m q)
  map_smul' c p := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (normalPair_finite D i l m p)).symm

theorem normalSum_interval (D : LatticeData) (i l : Fin D.rank) (m : ℤ)
    (p : Oscillator D) (a b : ℤ)
    (ha : a ≤ min (m-bound D p) 0) (hb : (bound D p : ℤ)-1 ≤ b) :
    normalSum D i l m p = ∑ j ∈ Finset.Icc a b, normalPair D i l j (m-j-1) p := by
  change (∑ᶠ j : ℤ, _) = _
  apply finsum_eq_sum_of_support_subset
  intro j hj
  have h := normalPair_support_interval D i l m p hj
  simp only [Set.mem_Icc] at h
  simpa only [Finset.mem_coe, Finset.mem_Icc] using
    (show a ≤ j ∧ j ≤ b by omega)

def rawL (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    Module.End ℂ (Oscillator D) :=
  (2 : ℂ)⁻¹ • ∑ i : Fin D.rank, ∑ l : Fin D.rank, H i l • normalSum D i l m

private theorem rawL_apply (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (m : ℤ) (p : Oscillator D) :
    rawL D H m p = (2 : ℂ)⁻¹ •
      ∑ i : Fin D.rank, ∑ l : Fin D.rank, H i l •
        ∑ᶠ j : ℤ, normalPair D i l j (m-j-1) p := by
  simp [rawL, normalSum, LinearMap.sum_apply]

private theorem normalPair_high_vanish (D : LatticeData) (i l : Fin D.rank)
    (m j : ℤ) (p : Oscillator D) (hm : 2*(bound D p : ℤ) ≤ m) :
    normalPair D i l j (m-j-1) p = 0 := by
  by_cases hj : j < 0
  · have hp := current_vanish D l p (m-j-1) (by omega)
    simp [normalPair, hj, Module.End.mul_apply, hp]
  · by_cases hr : (bound D p : ℤ) ≤ j
    · simp [normalPair, hj, Module.End.mul_apply, current_vanish D i p j hr]
    · have hk : (bound D p : ℤ) ≤ m-j-1 := by omega
      have hc := current_heisenberg_apply D l i (m-j-1) j p
      rw [if_neg (show m-j-1+j+1 ≠ 0 by omega)] at hc
      rw [normalPair, if_neg hj, Module.End.mul_apply, sub_eq_zero.mp hc,
        current_vanish D l p _ hk, map_zero]

theorem rawL_truncation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : Oscillator D) (m : ℤ)
    (hm : 2*(bound D p : ℤ) ≤ m) : rawL D H m p = 0 := by
  rw [rawL_apply]
  simp [normalPair_high_vanish D _ _ m _ p hm]

@[simp] theorem bound_one (D : LatticeData) : bound D (1 : Oscillator D) = 0 := by
  simp [bound]

theorem rawL_ground_nonnegative (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) (hm : 0 ≤ m) :
    rawL D H m (1 : Oscillator D) = 0 :=
  rawL_truncation D H 1 m (by simpa using hm)

theorem rawL_ground_negative (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) (hm : m < 0) :
    rawL D H m (1 : Oscillator D) = (2 : ℂ)⁻¹ •
      ∑ i : Fin D.rank, ∑ l : Fin D.rank, H i l •
        ∑ j ∈ Finset.Icc m (-1), X (i,(-j-1).toNat) * X (l,(j-m).toNat) := by
  simp only [rawL, LinearMap.smul_apply, LinearMap.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  rw [normalSum_interval D i l m 1 m (-1) (by simp; omega) (by simp)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have hjneg : j < 0 := by omega
  have hkneg : m-j-1 < 0 := by omega
  simp [normalPair, hjneg, current, hkneg, Module.End.mul_apply,
    LinearMap.mulLeft_apply, show -(m-j-1)-1 = j-m by omega]

def L (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    Module.End ℂ (Oscillator D) :=
  rawL D H m + (if m = 0 then (D.rank : ℂ)/16 else 0) • 1

theorem L_ground_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    L D H 0 (1 : Oscillator D) = ((D.rank : ℂ)/16) • 1 := by
  simp [L, rawL_ground_nonnegative D H 0 (by omega)]

theorem L_truncation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : Oscillator D) (m : ℤ)
    (hm : 2*(bound D p : ℤ) < m) : L D H m p = 0 := by
  have hmpos : 0 < m := by omega
  simp [L, ne_of_gt hmpos, rawL_truncation D H p m hm.le]

def rightBracket (D : LatticeData) (B : Module.End ℂ (Oscillator D)) :
    Module.End ℂ (Oscillator D) →ₗ[ℂ] Module.End ℂ (Oscillator D) where
  toFun A := A*B-B*A
  map_add' A C := by
    apply LinearMap.ext
    intro p
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, map_add]
    abel
  map_smul' c A := by
    apply LinearMap.ext
    intro p
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      map_smul, smul_sub, RingHom.id_apply]

private theorem product_current_commutator (D : LatticeData) (i l a : Fin D.rank)
    (j k q : ℤ) :
    (current D i j * current D l k) * current D a q -
      current D a q * (current D i j * current D l k) =
      (if k+q+1 = 0 then (frequency k*(D.G l a : ℂ)) • current D i j else 0) +
      (if j+q+1 = 0 then (frequency j*(D.G i a : ℂ)) • current D l k else 0) := by
  calc
    _ = current D i j * (current D l k * current D a q - current D a q * current D l k) +
        (current D i j * current D a q - current D a q * current D i j) * current D l k := by
      apply LinearMap.ext
      intro p
      simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, map_sub, map_add]
      abel
    _ = _ := by
      rw [current_heisenberg, current_heisenberg]
      split_ifs <;> simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

private theorem normalPair_current_commutator (D : LatticeData) (i l a : Fin D.rank)
    (j k q : ℤ) :
    normalPair D i l j k * current D a q - current D a q * normalPair D i l j k =
      (if k+q+1 = 0 then (frequency k*(D.G l a : ℂ)) • current D i j else 0) +
      (if j+q+1 = 0 then (frequency j*(D.G i a : ℂ)) • current D l k else 0) := by
  by_cases hj : j < 0
  · rw [normalPair, if_pos hj]
    exact product_current_commutator D i l a j k q
  · rw [normalPair, if_neg hj]
    simpa only [add_comm] using product_current_commutator D l i a k j q

theorem normalSum_current_commutator (D : LatticeData) (i l a : Fin D.rank)
    (m q : ℤ) :
    normalSum D i l m * current D a q - current D a q * normalSum D i l m =
      -frequency q • ((D.G l a : ℂ) • current D i (m+q) +
        (D.G i a : ℂ) • current D l (m+q)) := by
  classical
  apply LinearMap.ext
  intro p
  have hp := normalPair_finite D i l m p
  have hw := normalPair_finite D i l m (current D a q p)
  have hmap := hp.fun_comp (map_zero (current D a q))
  let x : Oscillator D := (-frequency q*(D.G l a : ℂ)) • current D i (m+q) p
  let y : Oscillator D := (-frequency q*(D.G i a : ℂ)) • current D l (m+q) p
  have hx : Function.HasFiniteSupport (fun j : ℤ => if m-j+q = 0 then x else 0) := by
    apply (Set.finite_singleton (m+q)).subset
    intro j hj
    have he : m-j+q = 0 := by
      by_contra h; exact hj (by simp [h])
    simp only [Set.mem_singleton_iff]; omega
  have hy : Function.HasFiniteSupport (fun j : ℤ => if j+q+1 = 0 then y else 0) := by
    apply (Set.finite_singleton (-q-1)).subset
    intro j hj
    have he : j+q+1 = 0 := by
      by_contra h; exact hj (by simp [h])
    simp only [Set.mem_singleton_iff]; omega
  change (∑ᶠ j : ℤ, normalPair D i l j (m-j-1) (current D a q p)) -
    current D a q (∑ᶠ j : ℤ, normalPair D i l j (m-j-1) p) = _
  rw [map_finsum (current D a q) hp, ← finsum_sub_distrib hw hmap]
  calc
    _ = ∑ᶠ j : ℤ, ((if m-j+q = 0 then x else 0) + (if j+q+1 = 0 then y else 0)) := by
      apply finsum_congr
      intro j
      change (normalPair D i l j (m-j-1) * current D a q -
        current D a q * normalPair D i l j (m-j-1)) p = _
      rw [normalPair_current_commutator]
      simp only [LinearMap.add_apply, DFunLike.ite_apply, LinearMap.smul_apply,
        LinearMap.zero_apply]
      congr 1
      · by_cases hj : m-j+q = 0
        · have hk : m-j-1 = -q-1 := by omega
          have hi : j = m+q := by omega
          simp only [if_pos (show m-j-1+q+1 = 0 by omega), if_pos hj]
          rw [hk, hi, frequency_opposite]
        · simp [show m-j-1+q+1 ≠ 0 by omega, hj]
      · by_cases hj : j+q+1 = 0
        · have hi : j = -q-1 := by omega
          have hk : m-j-1 = m+q := by omega
          simp only [if_pos hj]
          rw [hk, hi, frequency_opposite]
        · simp [hj]
    _ = x+y := by
      rw [finsum_add_distrib hx hy,
        finsum_eq_single _ (m+q) (fun j hj => by simp [show m-j+q ≠ 0 by omega]),
        finsum_eq_single _ (-q-1) (fun j hj => by simp [show j+q+1 ≠ 0 by omega])]
      simp only [if_pos (show m-(m+q)+q = 0 by omega),
        if_pos (show -q-1+q+1 = 0 by omega)]
    _ = _ := by simp [x, y, smul_add, smul_smul]

theorem rawL_current_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Fin D.rank) (m q : ℤ) :
    rawL D H m * current D a q - current D a q * rawL D H m =
      -frequency q • current D a (m+q) := by
  classical
  have left (i : Fin D.rank) : ∑ l, H i l * (D.G l a : ℂ) = if i = a then 1 else 0 := by
    simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply] using
      congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i a) hHG
  have right (l : Fin D.rank) : ∑ i, H i l * (D.G i a : ℂ) = if l = a then 1 else 0 := by
    have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M a l) hGH
    simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply, D.symmetric a,
      mul_comm, eq_comm] using h
  have first : (∑ i : Fin D.rank, ∑ l : Fin D.rank,
      (H i l*(D.G l a : ℂ)) • current D i (m+q)) = current D a (m+q) := by
    simp_rw [← Finset.sum_smul, left]; simp
  have second : (∑ i : Fin D.rank, ∑ l : Fin D.rank,
      (H i l*(D.G i a : ℂ)) • current D l (m+q)) = current D a (m+q) := by
    rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul, right]; simp
  change rightBracket D (current D a q) (rawL D H m) = _
  rw [rawL, map_smul]
  simp_rw [map_sum, map_smul]
  have quadratic (i l : Fin D.rank) : rightBracket D (current D a q) (normalSum D i l m) =
      -frequency q • ((D.G l a : ℂ) • current D i (m+q) +
        (D.G i a : ℂ) • current D l (m+q)) := normalSum_current_commutator D i l a m q
  simp_rw [quadratic]
  have coefficients (i l : Fin D.rank) :
      H i l • (-frequency q • ((D.G l a : ℂ) • current D i (m+q) +
        (D.G i a : ℂ) • current D l (m+q))) =
      -frequency q • ((H i l*(D.G l a : ℂ)) • current D i (m+q) +
        (H i l*(D.G i a : ℂ)) • current D l (m+q)) := by
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  simp_rw [coefficients, ← Finset.smul_sum, Finset.sum_add_distrib]
  rw [first, second, ← two_smul ℂ, smul_smul]
  have hc : (2 : ℂ)⁻¹ * (-frequency q * 2) = -frequency q := by ring
  rw [smul_smul, mul_assoc, hc]

theorem L_current_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Fin D.rank) (m q : ℤ) :
    L D H m * current D a q - current D a q * L D H m =
      -frequency q • current D a (m+q) := by
  rw [L, add_mul, mul_add]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one]
  rw [show rawL D H m * current D a q +
      (if m = 0 then (D.rank : ℂ)/16 else 0) • current D a q -
      (current D a q * rawL D H m + (if m = 0 then (D.rank : ℂ)/16 else 0) • current D a q) =
      rawL D H m * current D a q - current D a q * rawL D H m by abel]
  exact rawL_current_commutator D H hHG hGH a m q

end
end D5.S3.VertexAlgebra.LatticeHalfFock
