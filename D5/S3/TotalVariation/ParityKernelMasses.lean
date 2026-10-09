/- GID: D5/S3/TotalVariation/ParityKernelMasses
   generality: G
   mirror-B: D5/B/S3/TotalVariation/ParityKernelMasses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weak-composition parity fiber counts and conditioned Bernoulli parity normalization. -/

import Mathlib

open scoped BigOperators

namespace D5.S3.TotalVariation.ParityKernelMasses

/-- Stars and bars: the number of weak compositions of `t` into `d` ordered parts. -/
theorem antidiagonal_tuple_card {d : ℕ} (hd : 0 < d) (t : ℕ) :
    (Finset.Nat.antidiagonalTuple d t).card = (t+d-1).choose (d-1) := by
  classical
  let e : ↑(Finset.Nat.antidiagonalTuple d t) ≃ Sym (Fin d) t :=
    (Equiv.subtypeEquivRight (fun r => by
      simp only [Finset.Nat.mem_antidiagonalTuple])).trans
      (Sym.equivNatSumOfFintype (Fin d) t).symm
  rw [Finset.card_eq_of_equiv_fintype e, Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  rw [Nat.add_comm, ← Nat.choose_symm (n := t+d-1) (k := t) (by omega)]
  congr 1
  omega

/-- The weak compositions of `M` into `d` parts with a prescribed complete parity vector:
on the legal support, halving the residual total gives the stars-and-bars count; otherwise
the fiber is empty. -/
theorem parity_fiber_card {d M : ℕ} (hd : 0 < d) (x : Fin d → Bool) :
    let h : (Fin d → Bool) → ℕ := fun x => (Finset.univ.filter fun i => x i = true).card
    ((Finset.Nat.antidiagonalTuple d M).filter
        fun r => ∀ i, r i % 2 = if x i then 1 else 0).card =
      if h x ≤ M ∧ h x % 2 = M % 2 then ((M-h x)/2+d-1).choose (d-1) else 0 := by
  classical
  intro h
  let bit : Bool → ℕ := fun b => if b then 1 else 0
  let C : ℕ → Finset (Fin d → ℕ) := Finset.Nat.antidiagonalTuple d
  have hbit (x : Fin d → Bool) : (∑ i, bit (x i)) = h x := by simp [bit, h]
  have hcard (t : ℕ) : (C t).card = (t+d-1).choose (d-1) := antidiagonal_tuple_card hd t
  have hdecomp (x : Fin d → Bool) (r : Fin d → ℕ)
      (hr : ∀ i, r i % 2 = bit (x i)) :
      (∑ i, r i) = 2 * (∑ i, r i / 2) + h x := by
    rw [← hbit, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hm := Nat.mod_add_div (r i) 2
    rw [hr i] at hm
    omega
  let F : (Fin d → Bool) → Finset (Fin d → ℕ) := fun x =>
    (C M).filter fun r => ∀ i, r i % 2 = bit (x i)
  change (F x).card = if h x ≤ M ∧ h x % 2 = M % 2 then
    ((M-h x)/2+d-1).choose (d-1) else 0
  by_cases hx : h x ≤ M ∧ h x % 2 = M % 2
  · rw [if_pos hx]
    let e : ↑(F x) ≃ ↑(C ((M-h x)/2)) := {
      toFun := fun r => ⟨fun i => r.1 i / 2, by
        have hr := Finset.mem_filter.mp r.2
        have hs := Finset.Nat.mem_antidiagonalTuple.mp hr.1
        have hdec := hdecomp x r.1 hr.2
        change (fun i => r.1 i/2) ∈ Finset.Nat.antidiagonalTuple d ((M-h x)/2)
        rw [Finset.Nat.mem_antidiagonalTuple]
        omega⟩
      invFun := fun t => ⟨fun i => 2*t.1 i + bit (x i), by
        apply Finset.mem_filter.mpr
        constructor
        · change (fun i => 2*t.1 i + bit (x i)) ∈ Finset.Nat.antidiagonalTuple d M
          rw [Finset.Nat.mem_antidiagonalTuple]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hbit]
          have ht := Finset.Nat.mem_antidiagonalTuple.mp t.2
          rw [ht]
          omega
        · intro i
          cases hb : x i <;> simp [bit, hb]⟩
      left_inv := fun r => by
        apply Subtype.ext
        funext i
        change 2*(r.1 i/2) + bit (x i) = r.1 i
        have hi := (Finset.mem_filter.mp r.2).2 i
        have hm := Nat.mod_add_div (r.1 i) 2
        rw [hi] at hm
        omega
      right_inv := fun t => by
        apply Subtype.ext
        funext i
        change (2*t.1 i + bit (x i))/2 = t.1 i
        cases hb : x i <;> simp [bit, hb] <;> omega }
    rw [Finset.card_eq_of_equiv e, hcard]
  · rw [if_neg hx]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hrs := Finset.mem_filter.mp hr
    have hs := Finset.Nat.mem_antidiagonalTuple.mp hrs.1
    have hdec := hdecomp x r hrs.2
    apply hx
    constructor <;> omega

/-- The parity-conditioned Bernoulli reference law: its conditioning event has positive
probability, and the conditioned masses are nonnegative and sum to one. -/
theorem parity_reference_mass {d M : ℕ} (hd : 0 < d) (hM : 0 < M) :
    let h : (Fin d → Bool) → ℕ := fun x => (Finset.univ.filter fun i => x i = true).card
    let ν : ℝ := M/(2*(M : ℝ)+d)
    let pe : ℝ := (1+(-1 : ℝ)^M*((d : ℝ)/(2*(M : ℝ)+d))^d)/2
    let Q : (Fin d → Bool) → ℝ := fun x =>
      if h x % 2 = M % 2 then ν^(h x)*(1-ν)^(d-h x)/pe else 0
    0 < pe ∧ (∀ x, 0 ≤ Q x) ∧ ∑ x, Q x = 1 := by
  classical
  intro h ν pe Q
  let η : ℝ := (d : ℝ)/(2*(M : ℝ)+d)
  let w : Bool → ℝ := fun b => if b then ν else 1-ν
  have hdpos : 0 < d := hd
  have hMpos : 0 < M := hM
  have hden : 0 < 2 * (M : ℝ) + d := by positivity
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hν1 : ν < 1 := by
    dsimp [ν]
    apply (div_lt_one hden).mpr
    linarith [show (0 : ℝ) < 2 * M by positivity]
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η < 1 := by
    dsimp [η]
    apply (div_lt_one hden).mpr
    linarith [show (0 : ℝ) < 2 * M by positivity]
  have hηpow : η^d < 1 := pow_lt_one₀ hη hη1 (by omega)
  have hpe : 0 < pe := by
    rcases neg_one_pow_eq_or ℝ M with hsign | hsign <;>
      dsimp [pe] <;> rw [hsign] <;> nlinarith [pow_nonneg hη d]
  have hw (x : Fin d → Bool) : (∏ i, w (x i)) = ν^(h x) * (1-ν)^(d-h x) := by
    simp only [w]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const]
    have hc : (Finset.univ.filter fun i : Fin d => ¬x i = true).card = d-h x := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      simp [h]
    rw [hc]
  have hchar (x : Fin d → Bool) : (∏ i, (if x i then (-1 : ℝ) else 1)) = (-1 : ℝ)^(h x) := by
    rw [Finset.prod_ite]
    simp [h]
  have htotal : (∑ x : Fin d → Bool, ∏ i, w (x i)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [w]
  have htwist : (∑ x : Fin d → Bool, (-1 : ℝ)^(h x) * ∏ i, w (x i)) = η^d := by
    simp_rw [← hchar, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun (_ : Fin d) (b : Bool) => (if b then (-1 : ℝ) else 1) * w b)]
    have hs : (∑ b : Bool, (if b then (-1 : ℝ) else 1) * w b) = η := by
      simp [w]
      dsimp [ν, η]
      field_simp
      ring
    simp_rw [hs]
    simp
  have hind (x : Fin d → Bool) :
      (if h x % 2 = M % 2 then ∏ i, w (x i) else 0) =
        (∏ i, w (x i)) * (1 + (-1 : ℝ)^M * (-1 : ℝ)^(h x)) / 2 := by
    rw [neg_one_pow_eq_pow_mod_two M, neg_one_pow_eq_pow_mod_two (h x)]
    have hxm := Nat.mod_lt (h x) (by decide : 0 < 2)
    have hMm := Nat.mod_lt M (by decide : 0 < 2)
    interval_cases h x % 2 <;> interval_cases M % 2 <;> norm_num
  have hmass : (∑ x : Fin d → Bool, if h x % 2 = M % 2 then ∏ i, w (x i) else 0) = pe := by
    simp_rw [hind]
    simp_rw [mul_add, mul_one]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    have heq : (∑ x : Fin d → Bool, (∏ i, w (x i)) * ((-1 : ℝ)^M * (-1 : ℝ)^(h x))) =
        (-1 : ℝ)^M * ∑ x : Fin d → Bool, (-1 : ℝ)^(h x) * ∏ i, w (x i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [heq, htotal, htwist]
  have hQ0 : ∀ x, 0 ≤ Q x := by
    intro x
    dsimp [Q]
    split_ifs
    · exact div_nonneg (mul_nonneg (pow_nonneg hν.le _) (pow_nonneg (by linarith) _)) hpe.le
    · exact le_rfl
  have hQ1 : ∑ x, Q x = 1 := by
    change (∑ x : Fin d → Bool, if h x % 2 = M % 2 then ν^(h x) * (1-ν)^(d-h x) / pe else 0) = 1
    simp_rw [← hw]
    calc
      _ = (∑ x : Fin d → Bool, if h x % 2 = M % 2 then ∏ i, w (x i) else 0) / pe := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> simp
      _ = 1 := by rw [hmass, div_self hpe.ne']
  exact ⟨hpe, hQ0, hQ1⟩

end D5.S3.TotalVariation.ParityKernelMasses
