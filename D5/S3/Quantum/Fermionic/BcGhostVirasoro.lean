/- GID: D5/S3/Quantum/Fermionic/BcGhostVirasoro
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostVirasoro
   mirror-E: none(waiver:algebraic-ghost-virasoro)
   anchors: []
   utility: none
   digest: Locally finite normal ordered bc modes on the actual occupation Fock space. -/

import D5.S3.Quantum.Fermionic.BcGhostFock
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.NoncommRing

set_option backward.isDefEq.respectTransparency false

/-! Classical algebraic bc ghosts, with weights two and minus one.
The carrier and all odd modes are the original countable occupation operators.
Normal ordering is applied before summing; only statewise finite sums are used.
-/

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostVirasoro

/-- The creator cut is the actual ghost vacuum cut. -/
def normal (p q : ℤ) : Module.End ℂ Fock :=
  if p ≤ -2 then b p * c q else -(c q * b p)

def summand (m q : ℤ) : Module.End ℂ Fock :=
  ((m + q : ℤ) : ℂ) • normal (m-q) q

private theorem normal_ket_tail (m q : ℤ) (S : Finset ℕ)
    (hq : q < -((m.natAbs + S.sup id + 3 : ℕ) : ℤ) ∨
      ((m.natAbs + S.sup id + 3 : ℕ) : ℤ) < q) :
    normal (m-q) q (ket S) = 0 := by
  have hm₁ : -m ≤ (m.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -m))
  have hm₂ : m ≤ (m.natAbs : ℤ) := Int.le_natAbs
  have hbound (j : ℕ) (hj : j ∈ S) : j ≤ S.sup id := Finset.le_sup (f := id) hj
  rcases hq with hq | hq
  · have hp : ¬m-q ≤ -2 := by omega
    have hj : 2 * (m-q+1).toNat + 1 ∉ S := by
      intro hj
      have := hbound _ hj
      omega
    simp [normal, hp, b, annihilate_ket, hj]
  · have hp : m-q ≤ -2 := by omega
    have hc : ¬q ≤ 1 := by omega
    have hj : 2 * (q-2).toNat ∉ S := by
      intro hj
      have := hbound _ hj
      omega
    simp [normal, hp, c, hc, annihilate_ket, hj]

private theorem normal_ket_finite (m : ℤ) (S : Finset ℕ) :
    Function.HasFiniteSupport (fun q : ℤ => normal (m-q) q (ket S)) := by
  classical
  apply (Set.finite_Icc (-((m.natAbs + S.sup id + 3 : ℕ) : ℤ))
    ((m.natAbs + S.sup id + 3 : ℕ) : ℤ)).subset
  intro q hq
  by_contra hn
  have htail : q < -((m.natAbs + S.sup id + 3 : ℕ) : ℤ) ∨
      ((m.natAbs + S.sup id + 3 : ℕ) : ℤ) < q := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hn
    exact hn
  exact hq (normal_ket_tail m q S htail)

private theorem normal_finite (m : ℤ) (v : Fock) :
    Function.HasFiniteSupport (fun q : ℤ => normal (m-q) q v) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp [Function.HasFiniteSupport, Function.support]
  | add f g hf hg =>
    apply (hf.union hg).subset
    intro q hq
    by_contra hn
    have hfq : normal (m-q) q f = 0 := by
      by_contra hz
      exact hn (Or.inl hz)
    have hgq : normal (m-q) q g = 0 := by
      by_contra hz
      exact hn (Or.inr hz)
    exact hq (by simp only [map_add, hfq, hgq, add_zero])
  | single S a =>
    have hs : Finsupp.single S a = a • ket S := by simp [ket]
    rw [hs]
    simp only [map_smul]
    exact (normal_ket_finite m S).fun_comp (smul_zero a)

/-- Every state has finite support in the normal ordered integer summation index. -/
theorem summand_finite (m : ℤ) (v : Fock) :
    Function.HasFiniteSupport (fun q : ℤ => summand m q v) := by
  apply (normal_finite m v).subset
  intro q hq hn
  exact hq (by simp [summand, hn])

/-- The pointwise finite normal ordered sum, acting on every finite-excitation state. -/
def L (m : ℤ) : Module.End ℂ Fock where
  toFun v := ∑ᶠ q : ℤ, summand m q v
  map_add' v w := by
    simp only [map_add]
    exact finsum_add_distrib (summand_finite m v) (summand_finite m w)
  map_smul' a v := by
    simp only [map_smul]
    exact (smul_finsum' a (summand_finite m v)).symm

private theorem normal_eq (p q : ℤ) :
    normal p q = b p * c q -
      (if p ≤ -2 then 0 else if p+q = 0 then 1 else 0) := by
  by_cases hp : p ≤ -2
  · simp [normal, hp]
  · rw [normal, if_neg hp, if_neg hp]
    calc
      -(c q * b p) = b p * c q - (b p * c q + c q * b p) := by abel
      _ = _ := by rw [ghost_mixed_car]

private theorem normal_comm (p q : ℤ) (A : Module.End ℂ Fock) :
    normal p q * A - A * normal p q =
      (b p * c q) * A - A * (b p * c q) := by
  rw [normal_eq]
  split_ifs <;> noncomm_ring

private theorem normal_b (p q r : ℤ) :
    normal p q * b r - b r * normal p q =
      if q+r = 0 then b p else 0 := by
  rw [normal_comm]
  calc
    _ = b p * (b r * c q + c q * b r) -
        (b p * b r + b r * b p) * c q := by noncomm_ring
    _ = _ := by
      rw [ghost_mixed_car, ghost_b_car]
      have he : r+q = 0 ↔ q+r = 0 := by omega
      simp only [he]
      split_ifs <;> simp

private theorem normal_c (p q r : ℤ) :
    normal p q * c r - c r * normal p q =
      if p+r = 0 then -c q else 0 := by
  rw [normal_comm]
  calc
    _ = b p * (c q * c r + c r * c q) -
        (b p * c r + c r * b p) * c q := by noncomm_ring
    _ = _ := by rw [ghost_c_car, ghost_mixed_car]; split_ifs <;> simp

/-- The actual b modes have conformal weight two. -/
theorem ward_b (m r : ℤ) :
    L m * b r - b r * L m = ((m-r : ℤ) : ℂ) • b (m+r) := by
  apply LinearMap.ext
  intro v
  have hv := summand_finite m v
  have hw := summand_finite m (b r v)
  have hmap := hv.fun_comp (map_zero (b r))
  change (∑ᶠ q : ℤ, summand m q (b r v)) -
      b r (∑ᶠ q : ℤ, summand m q v) = _
  rw [map_finsum (b r) hv, ← finsum_sub_distrib hw hmap]
  calc
    _ = ∑ᶠ q : ℤ, if q+r = 0 then ((m-r : ℤ) : ℂ) • b (m+r) v else 0 := by
      apply finsum_congr
      intro q
      have h := LinearMap.congr_fun (normal_b (m-q) q r) v
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      simp only [summand, LinearMap.smul_apply, map_smul, ← smul_sub, h]
      by_cases hq : q+r = 0
      · have he : q = -r := by omega
        subst q
        simp [sub_neg_eq_add, sub_eq_add_neg]
      · simp [hq]
    _ = _ := by
      rw [finsum_eq_single _ (-r) (fun q hq => by
        simp [show q+r ≠ 0 by omega])]
      simp

/-- The actual c modes have conformal weight minus one. -/
theorem ward_c (m r : ℤ) :
    L m * c r - c r * L m = ((-2*m-r : ℤ) : ℂ) • c (m+r) := by
  apply LinearMap.ext
  intro v
  have hv := summand_finite m v
  have hw := summand_finite m (c r v)
  have hmap := hv.fun_comp (map_zero (c r))
  change (∑ᶠ q : ℤ, summand m q (c r v)) -
      c r (∑ᶠ q : ℤ, summand m q v) = _
  rw [map_finsum (c r) hv, ← finsum_sub_distrib hw hmap]
  calc
    _ = ∑ᶠ q : ℤ, if m-q+r = 0 then ((-2*m-r : ℤ) : ℂ) • c (m+r) v else 0 := by
      apply finsum_congr
      intro q
      have h := LinearMap.congr_fun (normal_c (m-q) q r) v
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      simp only [summand, LinearMap.smul_apply, map_smul, ← smul_sub, h]
      by_cases hq : m-q+r = 0
      · have he : q = m+r := by omega
        subst q
        simp only [if_pos hq, LinearMap.neg_apply,
          smul_neg, ← neg_smul]
        congr 1
        push_cast
        ring
      · simp [hq]
    _ = _ := by
      rw [finsum_eq_single _ (m+r) (fun q hq => by
        simp [show m-q+r ≠ 0 by omega])]
      simp

def centralDefect (m n : ℤ) : Module.End ℂ Fock :=
  L m * L n - L n * L m - ((m-n : ℤ) : ℂ) • L (m+n)

private theorem comm_jacobi (A B C : Module.End ℂ Fock) :
    (A*B-B*A)*C-C*(A*B-B*A) =
      (A*(B*C-C*B)-(B*C-C*B)*A) -
      (B*(A*C-C*A)-(A*C-C*A)*B) := by noncomm_ring

private theorem defect_b (m n r : ℤ) :
    centralDefect m n * b r - b r * centralDefect m n = 0 := by
  unfold centralDefect
  rw [show ∀ A B C : Module.End ℂ Fock,
    (A-B)*C-C*(A-B) = (A*C-C*A)-(B*C-C*B) by intros; noncomm_ring]
  rw [comm_jacobi, ward_b n r, ward_b m r]
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [ward_b m (n+r), ward_b n (m+r), ward_b (m+n) r]
  rw [show m+(n+r) = m+n+r by omega, show n+(m+r) = m+n+r by omega]
  simp only [smul_smul, ← sub_smul]
  have he : ((n-r : ℤ) : ℂ) * ((m-(n+r) : ℤ) : ℂ) -
      ((m-r : ℤ) : ℂ) * ((n-(m+r) : ℤ) : ℂ) -
      ((m-n : ℤ) : ℂ) * ((m+n-r : ℤ) : ℂ) = 0 := by push_cast; ring
  rw [he, zero_smul]

private theorem defect_c (m n r : ℤ) :
    centralDefect m n * c r - c r * centralDefect m n = 0 := by
  unfold centralDefect
  rw [show ∀ A B C : Module.End ℂ Fock,
    (A-B)*C-C*(A-B) = (A*C-C*A)-(B*C-C*B) by intros; noncomm_ring]
  rw [comm_jacobi, ward_c n r, ward_c m r]
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [ward_c m (n+r), ward_c n (m+r), ward_c (m+n) r]
  rw [show m+(n+r) = m+n+r by omega, show n+(m+r) = m+n+r by omega]
  simp only [smul_smul, ← sub_smul]
  have he : ((-2*n-r : ℤ) : ℂ) * ((-2*m-(n+r) : ℤ) : ℂ) -
      ((-2*m-r : ℤ) : ℂ) * ((-2*n-(m+r) : ℤ) : ℂ) -
      ((m-n : ℤ) : ℂ) * ((-2*(m+n)-r : ℤ) : ℂ) = 0 := by push_cast; ring
  rw [he, zero_smul]

private theorem defect_scalar (m n : ℤ) :
    ∃ α : ℂ, centralDefect m n = α • (1 : Module.End ℂ Fock) := by
  apply scalar_commutant
  · intro r; exact sub_eq_zero.mp (defect_b m n r)
  · intro r; exact sub_eq_zero.mp (defect_c m n r)

def epsilon : Fock →ₗ[ℂ] ℂ := Finsupp.lapply ∅

private theorem epsilon_vacuum : epsilon vacuum = 1 := by
  simp [epsilon, vacuum, ket]

private theorem epsilon_create (j : ℕ) (v : Fock) : epsilon (create j v) = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]
  | single S a =>
    have hs : Finsupp.single S a = a • ket S := by simp [ket]
    rw [hs, map_smul, map_smul, create_ket]
    by_cases hj : j ∈ S
    · simp [hj]
    · simp [hj, epsilon, ket, Finset.insert_ne_empty]

private theorem epsilon_b (p : ℤ) (hp : p ≤ -2) (v : Fock) :
    epsilon (b p v) = 0 := by simp only [b, if_pos hp]; exact epsilon_create _ v

private theorem normal_vacuum (m q : ℤ) :
    normal (m-q) q vacuum =
      if m+2 ≤ q ∧ q ≤ 1 then b (m-q) (c q vacuum) else 0 := by
  by_cases hp : m-q ≤ -2
  · rw [normal, if_pos hp]
    by_cases hq : q ≤ 1
    · simp [hp, hq, show m+2 ≤ q by omega]
    · simp [hq, ghost_vacuum.2.1 q (by omega : 2 ≤ q)]
  · have hb := ghost_vacuum.1 (m-q) (by omega : -1 ≤ m-q)
    simp [normal, hp, hb, show ¬m+2 ≤ q by omega]

private theorem L_vacuum (m : ℤ) :
    L m vacuum = ∑ q ∈ Finset.Icc (m+2) 1,
      ((m+q : ℤ) : ℂ) • b (m-q) (c q vacuum) := by
  classical
  change (∑ᶠ q : ℤ, summand m q vacuum) = _
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (m+2) 1) (by
    intro q hq
    by_contra hn
    have hn' : ¬(m+2 ≤ q ∧ q ≤ 1) := by simpa using hn
    exact hq (by simp [summand, normal_vacuum, hn']))]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' := Finset.mem_Icc.mp hq
  simp [summand, normal_vacuum, hq']

private theorem epsilon_L_vacuum (m : ℤ) : epsilon (L m vacuum) = 0 := by
  rw [L_vacuum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [map_smul, epsilon_b (m-q) (by have := Finset.mem_Icc.mp hq; omega), smul_zero]

private theorem L_vacuum_nonneg (m : ℤ) (hm : 0 ≤ m) : L m vacuum = 0 := by
  rw [L_vacuum]
  simp [Finset.Icc_eq_empty_of_lt (by omega : (1 : ℤ) < m+2)]

private theorem epsilon_bc_vacuum (s q : ℤ) (hq : q ≤ 1) :
    epsilon (b s (c q vacuum)) = if s+q = 0 then 1 else 0 := by
  by_cases hs : s ≤ -2
  · rw [epsilon_b s hs]
    simp [show s+q ≠ 0 by omega]
  · have hcar := congrArg (fun A : Module.End ℂ Fock => epsilon (A vacuum))
        (ghost_mixed_car s q)
    have hb := ghost_vacuum.1 s (by omega : -1 ≤ s)
    by_cases he : s+q = 0
    · simpa [hb, he, epsilon_vacuum] using hcar
    · simpa [hb, he] using hcar

private theorem epsilon_L_pair (m p q : ℤ) (hp : p ≤ -2) (hq : q ≤ 1) :
    epsilon (L m (b p (c q vacuum))) =
      if m+p+q = 0 then ((m-p : ℤ) : ℂ) else 0 := by
  have hb := LinearMap.congr_fun (ward_b m p) (c q vacuum)
  have hc := LinearMap.congr_fun (ward_c m q) vacuum
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hb hc
  have he : L m (b p (c q vacuum)) =
      b p (c q (L m vacuum)) +
      ((-2*m-q : ℤ) : ℂ) • b p (c (m+q) vacuum) +
      ((m-p : ℤ) : ℂ) • b (m+p) (c q vacuum) := by
    rw [sub_eq_iff_eq_add] at hb hc
    rw [hb, hc, map_add, map_smul]
    abel
  rw [he, map_add, map_add, map_smul, map_smul, epsilon_b p hp,
    epsilon_b p hp, epsilon_bc_vacuum (m+p) q hq]
  split_ifs <;> simp_all

private theorem epsilon_LL (m n : ℤ) :
    epsilon (L m (L n vacuum)) =
      ∑ q ∈ Finset.Icc (n+2) 1,
        if m+n = 0 then ((n+q : ℤ) : ℂ) * ((m-n+q : ℤ) : ℂ) else 0 := by
  classical
  rw [L_vacuum n, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' := Finset.mem_Icc.mp hq
  rw [map_smul, map_smul, epsilon_L_pair m (n-q) q (by omega) hq'.2]
  have he : m+(n-q)+q = m+n := by omega
  rw [he]
  split_ifs <;> simp [smul_eq_mul, show m-(n-q) = m-n+q by omega]

private theorem defect_off_diagonal (m n : ℤ) (hmn : m+n ≠ 0) :
    centralDefect m n = 0 := by
  obtain ⟨α, hα⟩ := defect_scalar m n
  have hv := congrArg (fun A : Module.End ℂ Fock => epsilon (A vacuum)) hα
  have hnm : n+m ≠ 0 := by omega
  simp only [centralDefect, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, map_sub, map_smul, epsilon_LL, if_neg hmn, if_neg hnm,
    Finset.sum_const_zero, epsilon_L_vacuum, smul_zero, sub_self,
    Module.End.one_apply, epsilon_vacuum, smul_eq_mul, mul_one] at hv
  rw [hα, ← hv]
  simp

private theorem contraction_sum (a : ℕ) :
    (∑ r ∈ Finset.range a, (1-(a : ℂ)-r)*(2*(a : ℂ)+1-r)) =
      (-13/6 : ℂ) * ((a : ℂ)^3-a) := by
  have s₁ : ∀ a : ℕ, ∑ r ∈ Finset.range a, (r : ℂ) = (a : ℂ)*((a : ℂ)-1)/2 := by
    intro a
    induction a with
    | zero => simp
    | succ a ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have s₂ : ∀ a : ℕ, ∑ r ∈ Finset.range a, (r : ℂ)^2 =
      (a : ℂ)*((a : ℂ)-1)*(2*(a : ℂ)-1)/6 := by
    intro a
    induction a with
    | zero => simp
    | succ a ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  calc
    _ = ∑ r ∈ Finset.range a,
        ((1+(a : ℂ)-2*(a : ℂ)^2) - ((a : ℂ)+2)*r + (r : ℂ)^2) := by
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, s₁, s₂]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

private theorem contraction_interval (a : ℕ) :
    (∑ q ∈ Finset.Icc (-(a : ℤ)+2) 1,
      ((-(a : ℤ)+q : ℤ) : ℂ) * (((a : ℤ)-(-(a : ℤ))+q : ℤ) : ℂ)) =
      (-13/6 : ℂ) * ((a : ℂ)^3-a) := by
  classical
  rw [← contraction_sum]
  symm
  apply Finset.sum_bij (fun (r : ℕ) _ => (1-(r : ℤ)))
  · intro r hr
    have := Finset.mem_range.mp hr
    simp only [Finset.mem_Icc]
    omega
  · intro r hr s hs hrs
    omega
  · intro q hq
    have hq' := Finset.mem_Icc.mp hq
    refine ⟨(1-q).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]; omega
    · omega
  · intro r hr
    push_cast
    ring

private theorem defect_diagonal_nat (a : ℕ) :
    centralDefect (a : ℤ) (-(a : ℤ)) =
      ((-13/6 : ℂ) * ((a : ℂ)^3-a)) • (1 : Module.End ℂ Fock) := by
  obtain ⟨α, hα⟩ := defect_scalar (a : ℤ) (-(a : ℤ))
  have hv := congrArg (fun A : Module.End ℂ Fock => epsilon (A vacuum)) hα
  simp only [centralDefect, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, map_sub, map_smul, L_vacuum_nonneg (a : ℤ) (by omega),
    map_zero, sub_zero, add_neg_cancel, epsilon_L_vacuum, smul_zero,
    Module.End.one_apply, epsilon_vacuum, smul_eq_mul, mul_one] at hv
  rw [epsilon_LL] at hv
  simp only [add_neg_cancel, if_true] at hv
  rw [contraction_interval] at hv
  rw [hα, ← hv]
  simp

private theorem defect_skew (m n : ℤ) : centralDefect m n = -centralDefect n m := by
  have hc : ((n-m : ℤ) : ℂ) = -((m-n : ℤ) : ℂ) := by push_cast; ring
  simp only [centralDefect, hc, add_comm n m, neg_smul]
  abel

private theorem defect_diagonal (m : ℤ) :
    centralDefect m (-m) =
      ((-13/6 : ℂ) * ((m : ℂ)^3-m)) • (1 : Module.End ℂ Fock) := by
  cases m with
  | ofNat a => simpa using defect_diagonal_nat a
  | negSucc a =>
    have he : Int.negSucc a = -((a+1 : ℕ) : ℤ) := by omega
    rw [he, neg_neg, defect_skew, defect_diagonal_nat]
    simp only [← neg_smul, Int.cast_neg, Int.cast_natCast]
    congr 1
    ring

/-- All integer modes on the original ghost Fock space satisfy Virasoro with c = -26. -/
theorem virasoro (m n : ℤ) :
    L m * L n - L n * L m =
      ((m-n : ℤ) : ℂ) • L (m+n) +
      (if m+n = 0 then (-26/12 : ℂ) * ((m : ℂ)^3-m) else 0) •
        (1 : Module.End ℂ Fock) := by
  have h : centralDefect m n =
      (if m+n = 0 then (-26/12 : ℂ) * ((m : ℂ)^3-m) else 0) •
        (1 : Module.End ℂ Fock) := by
    by_cases hmn : m+n = 0
    · have hn : n = -m := by omega
      subst n
      simpa only [add_neg_cancel, if_true, show (-26/12 : ℂ) = -13/6 by norm_num]
        using defect_diagonal m
    · simp [hmn, defect_off_diagonal m n hmn]
  unfold centralDefect at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

end D5.S3.Quantum.Fermionic.BcGhostVirasoro
