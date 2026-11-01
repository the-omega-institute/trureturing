/- GID: D5/S3/Quantum/Fermionic/BcGhostCubic
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostCubic
   mirror-E: none(waiver:algebraic-ghost-brst)
   anchors: []
   utility: none
   digest: Statewise locally finite normally ordered cubic on the actual bc Fock space. -/

import D5.S3.Quantum.Fermionic.BcGhostVirasoro

set_option backward.isDefEq.respectTransparency false

/-! The classical SL₂ vacuum convention for the cubic bc ghost BRST charge.
The cyclic move of b through two c factors has positive fermionic sign.
Anticommutation of the c factors makes the formula below equal to stable
creator-before-annihilator ordering, without adding contraction terms.
The normal ordered terms are summed only after application to a state.
-/

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostVirasoro (normal L)

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostBRST

/-- Normal ordering of c_p c_q b_{-p-q}, with the actual vacuum cuts. -/
def cubic (p q : ℤ) : Module.End ℂ Fock :=
  if p ≤ 1 then
    if q ≤ 1 then c p*c q*b (-p-q)
    else if -p-q ≤ -2 then -(c p*b (-p-q)*c q) else c p*c q*b (-p-q)
  else if q ≤ 1 then
    if -p-q ≤ -2 then c q*b (-p-q)*c p else -(c q*c p*b (-p-q))
  else if -p-q ≤ -2 then b (-p-q)*c p*c q else c p*c q*b (-p-q)

/-- CAR identifies the stable ordering with a useful cyclic expression.
Every contraction used here is zero in its actual creator/annihilator branch. -/
private theorem cubic_eq (p q : ℤ) : cubic p q =
    if -p-q ≤ -2 then b (-p-q)*c p*c q else c p*c q*b (-p-q) := by
  have hcc := ghost_c_car p q
  by_cases hp : p ≤ 1
  · by_cases hq : q ≤ 1
    · by_cases hk : -p-q ≤ -2
      · have hbp : b (-p-q)*c p+c p*b (-p-q) = 0 := by
          rw [ghost_mixed_car, if_neg (by omega)]
        have hbq : b (-p-q)*c q+c q*b (-p-q) = 0 := by
          rw [ghost_mixed_car, if_neg (by omega)]
        simp only [cubic, hp, hq, hk, if_true]
        calc
          _ = b (-p-q)*c p*c q+c p*(b (-p-q)*c q+c q*b (-p-q)) -
              (b (-p-q)*c p+c p*b (-p-q))*c q := by noncomm_ring
          _ = _ := by rw [hbp, hbq]; simp
      · simp [cubic, hp, hq, hk]
    · by_cases hk : -p-q ≤ -2
      · have hbp : b (-p-q)*c p+c p*b (-p-q) = 0 := by
          rw [ghost_mixed_car, if_neg (by omega)]
        simp only [cubic, hp, hq, hk, if_true, if_false]
        calc
          _ = b (-p-q)*c p*c q-(b (-p-q)*c p+c p*b (-p-q))*c q := by noncomm_ring
          _ = _ := by rw [hbp]; simp
      · simp [cubic, hp, hq, hk]
  · by_cases hq : q ≤ 1
    · by_cases hk : -p-q ≤ -2
      · have hbq : b (-p-q)*c q+c q*b (-p-q) = 0 := by
          rw [ghost_mixed_car, if_neg (by omega)]
        simp only [cubic, hp, hq, hk, if_true, if_false]
        calc
          _ = b (-p-q)*c p*c q-b (-p-q)*(c p*c q+c q*c p) +
              (b (-p-q)*c q+c q*b (-p-q))*c p := by noncomm_ring
          _ = _ := by rw [hcc, hbq]; simp
      · simp only [cubic, hp, hq, hk, if_true, if_false]
        calc
          _ = c p*c q*b (-p-q)-(c p*c q+c q*c p)*b (-p-q) := by noncomm_ring
          _ = _ := by rw [hcc]; simp
    · simp [cubic, hp, hq]

/-- The coefficient includes the one half for the full ordered pair sum. -/
def cubicTerm (pq : ℤ × ℤ) : Module.End ℂ Fock :=
  ((1/2 : ℂ) * ((pq.1-pq.2 : ℤ) : ℂ)) • cubic pq.1 pq.2

private theorem c_swap (p q : ℤ) : c p * c q = -(c q * c p) := by
  exact eq_neg_of_add_eq_zero_left (ghost_c_car p q)

private theorem cubic_p_zero (p q : ℤ) (v : Fock) (hp : 2 ≤ p)
    (hv : c p v = 0) : cubic p q v = 0 := by
  by_cases hk : -p-q ≤ -2
  · have he : b (-p-q) * c p * c q = -(b (-p-q) * c q * c p) := by
      rw [mul_assoc, c_swap p q]
      simp only [mul_neg, ← mul_assoc]
    simp only [cubic_eq, if_pos hk, he, LinearMap.neg_apply, Module.End.mul_apply,
      hv, map_zero, neg_zero]
  · have hbc : b (-p-q) * c p + c p * b (-p-q) = 0 := by
      rw [ghost_mixed_car, if_neg (by omega)]
    have he : c p * c q * b (-p-q) = c q * b (-p-q) * c p := by
      calc
        _ = -(c q * c p) * b (-p-q) := by rw [c_swap]
        _ = c q * b (-p-q) * c p - c q *
            (b (-p-q) * c p + c p * b (-p-q)) := by noncomm_ring
        _ = _ := by rw [hbc]; simp
    simp only [cubic_eq, if_neg hk, he, Module.End.mul_apply, hv, map_zero]

private theorem cubic_swap (p q : ℤ) : cubic p q = -cubic q p := by
  have he : -p-q = -q-p := by omega
  simp only [cubic_eq, ← he]
  split_ifs
  · rw [mul_assoc, c_swap p q]
    simp only [mul_neg, ← mul_assoc]
  · rw [c_swap p q]
    simp only [neg_mul]

private theorem cubic_q_zero (p q : ℤ) (v : Fock) (hq : 2 ≤ q)
    (hv : c q v = 0) : cubic p q v = 0 := by
  rw [cubic_swap, LinearMap.neg_apply, cubic_p_zero q p v hq hv, neg_zero]

private theorem cubic_b_zero (p q : ℤ) (v : Fock) (hk : -1 ≤ -p-q)
    (hv : b (-p-q) v = 0) : cubic p q v = 0 := by
  simp [cubic_eq, show ¬-p-q ≤ -2 by omega, Module.End.mul_apply, hv]

private theorem c_ket_tail (p : ℤ) (S : Finset ℕ)
    (hp : (S.sup id + 3 : ℕ) < p) : c p (ket S) = 0 := by
  have hc : ¬p ≤ 1 := by omega
  have hj : 2 * (p-2).toNat ∉ S := by
    intro hj
    have hs : 2 * (p-2).toNat ≤ S.sup id := Finset.le_sup (f := id) hj
    omega
  simp [c, hc, annihilate_ket, hj]

private theorem b_ket_tail (p : ℤ) (S : Finset ℕ)
    (hp : (S.sup id + 3 : ℕ) < p) : b p (ket S) = 0 := by
  have hb : ¬p ≤ -2 := by omega
  have hj : 2 * (p+1).toNat + 1 ∉ S := by
    intro hj
    have hs : 2 * (p+1).toNat + 1 ≤ S.sup id := Finset.le_sup (f := id) hj
    omega
  simp [b, hb, annihilate_ket, hj]

private theorem cubic_ket_bound (p q : ℤ) (S : Finset ℕ)
    (h : cubic p q (ket S) ≠ 0) :
    let A : ℤ := (S.sup id + 3 : ℕ);
    -2*A ≤ p ∧ p ≤ A ∧ -2*A ≤ q ∧ q ≤ A := by
  dsimp
  have hp : p ≤ (S.sup id + 3 : ℕ) := by
    by_contra hn
    exact h (cubic_p_zero p q (ket S) (by omega) (c_ket_tail p S (by omega)))
  have hq : q ≤ (S.sup id + 3 : ℕ) := by
    by_contra hn
    exact h (cubic_q_zero p q (ket S) (by omega) (c_ket_tail q S (by omega)))
  have hk : -p-q ≤ (S.sup id + 3 : ℕ) := by
    by_contra hn
    exact h (cubic_b_zero p q (ket S) (by omega) (b_ket_tail _ S (by omega)))
  omega

private theorem cubic_ket_finite (S : Finset ℕ) :
    Function.HasFiniteSupport (fun pq : ℤ × ℤ => cubic pq.1 pq.2 (ket S)) := by
  let A : ℤ := (S.sup id + 3 : ℕ)
  apply ((Set.finite_Icc (-2*A) A).prod (Set.finite_Icc (-2*A) A)).subset
  intro pq hpq
  obtain ⟨hp₁, hp₂, hq₁, hq₂⟩ := cubic_ket_bound pq.1 pq.2 S hpq
  exact ⟨⟨hp₁, hp₂⟩, hq₁, hq₂⟩

/-- Local finiteness concerns values on each actual state, not an operator family. -/
theorem cubic_finite (v : Fock) :
    Function.HasFiniteSupport (fun pq : ℤ × ℤ => cubic pq.1 pq.2 v) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp [Function.HasFiniteSupport, Function.support]
  | add f g hf hg =>
    apply (hf.union hg).subset
    intro pq hpq
    by_contra hn
    have hpf : cubic pq.1 pq.2 f = 0 := by
      by_contra hz
      exact hn (Or.inl hz)
    have hpg : cubic pq.1 pq.2 g = 0 := by
      by_contra hz
      exact hn (Or.inr hz)
    exact hpq (by simp only [map_add, hpf, hpg, add_zero])
  | single S a =>
    have hs : Finsupp.single S a = a • ket S := by simp [ket]
    rw [hs]
    simp only [map_smul]
    exact (cubic_ket_finite S).fun_comp (smul_zero a)

/-- The weighted cubic is also statewise locally finite. -/
theorem cubicTerm_finite (v : Fock) :
    Function.HasFiniteSupport (fun pq : ℤ × ℤ => cubicTerm pq v) := by
  apply (cubic_finite v).subset
  intro pq hpq hn
  exact hpq (by simp [cubicTerm, hn])

/-- The full normally ordered cubic charge on the original countable Fock. -/
def Qg : Module.End ℂ Fock where
  toFun v := ∑ᶠ pq : ℤ × ℤ, cubicTerm pq v
  map_add' v w := by
    simp only [map_add]
    exact finsum_add_distrib (cubicTerm_finite v) (cubicTerm_finite w)
  map_smul' a v := by
    simp only [map_smul]
    exact (smul_finsum' a (cubicTerm_finite v)).symm

/-- The single cubic CAR reduction, retaining the supplier's normal ordering. -/
theorem cubic_b (p q r : ℤ) :
    cubic p q * b r + b r * cubic p q =
      (if q+r = 0 then normal (-p-q) p else 0) -
      (if p+r = 0 then normal (-p-q) q else 0) := by
  have hbb := ghost_b_car (-p-q) r
  have hbp := ghost_mixed_car r p
  have hbq := ghost_mixed_car r q
  have hp : r+p = 0 ↔ p+r = 0 := by omega
  have hq : r+q = 0 ↔ q+r = 0 := by omega
  by_cases hk : -p-q ≤ -2
  · simp only [cubic_eq, if_pos hk, normal, if_pos hk]
    calc
      _ = (b (-p-q) * c p) * (b r * c q + c q * b r) -
          b (-p-q) * (b r * c p + c p * b r) * c q +
          (b (-p-q) * b r + b r * b (-p-q)) * c p * c q := by noncomm_ring
      _ = _ := by rw [hbb, hbp, hbq]; simp only [hp, hq]; split_ifs <;> simp <;> abel
  · simp only [cubic_eq, if_neg hk, normal, if_neg hk]
    calc
      _ = (b r * c p + c p * b r) * c q * b (-p-q) -
          c p * (b r * c q + c q * b r) * b (-p-q) +
          c p * c q * (b (-p-q) * b r + b r * b (-p-q)) := by noncomm_ring
      _ = _ := by rw [hbb, hbp, hbq]; simp only [hp, hq]; split_ifs <;> simp <;> abel

/-- The second cubic CAR reduction has no normal-order correction. -/
theorem cubic_c (p q r : ℤ) :
    cubic p q * c r + c r * cubic p q =
      if -p-q+r = 0 then c p * c q else 0 := by
  have hbp := ghost_mixed_car (-p-q) r
  have hpc := ghost_c_car p r
  have hqc := ghost_c_car q r
  by_cases hk : -p-q ≤ -2
  · simp only [cubic_eq, if_pos hk]
    calc
      _ = b (-p-q) * c p * (c q * c r + c r * c q) -
          b (-p-q) * (c p * c r + c r * c p) * c q +
          (b (-p-q) * c r + c r * b (-p-q)) * c p * c q := by noncomm_ring
      _ = _ := by rw [hbp, hpc, hqc]; split_ifs <;> simp
  · simp only [cubic_eq, if_neg hk]
    calc
      _ = c p * c q * (b (-p-q) * c r + c r * b (-p-q)) -
          c p * (c q * c r + c r * c q) * b (-p-q) +
          (c p * c r + c r * c p) * c q * b (-p-q) := by noncomm_ring
      _ = _ := by rw [hbp, hpc, hqc]; split_ifs <;> simp

private theorem cubic_vacuum (p q : ℤ) : cubic p q vacuum = 0 := by
  by_cases hp : 2 ≤ p
  · exact cubic_p_zero p q vacuum hp (ghost_vacuum.2.1 p hp)
  by_cases hq : 2 ≤ q
  · exact cubic_q_zero p q vacuum hq (ghost_vacuum.2.1 q hq)
  by_cases hk : -1 ≤ -p-q
  · exact cubic_b_zero p q vacuum hk (ghost_vacuum.1 _ hk)
  have hp₁ : p = 1 := by omega
  have hq₁ : q = 1 := by omega
  subst p
  subst q
  have hcc : c 1 * c 1 = 0 := by
    have h := ghost_c_car 1 1
    have htwo : (2 : ℂ) • (c 1 * c 1) = 0 := by simpa only [two_smul] using h
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  simp [cubic_eq, mul_assoc, hcc]

/-- The actual SL₂ vacuum is killed by the full cubic, with no intercept term. -/
theorem Qg_vacuum : Qg vacuum = 0 := by
  change (∑ᶠ pq : ℤ × ℤ, cubicTerm pq vacuum) = 0
  apply finsum_eq_zero_of_forall_eq_zero
  intro pq
  simp [cubicTerm, cubic_vacuum]

end D5.S3.Quantum.Fermionic.BcGhostBRST
