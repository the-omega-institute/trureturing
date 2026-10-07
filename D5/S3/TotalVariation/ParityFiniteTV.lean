/- GID: D5/S3/TotalVariation/ParityFiniteTV
   generality: G
   mirror-B: D5/B/S3/TotalVariation/ParityFiniteTV
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform finite total-variation bound for composition parity and biased parity laws. -/

import Mathlib

open scoped BigOperators
open Set

namespace D5.S3.TotalVariation.ParityFiniteTV

set_option maxHeartbeats 1000000 in
theorem parity_finite_tv {d M : ℕ} (hd : 2 ≤ d) (hM : 3*d ≤ M) :
    let h : (Fin d → Bool) → ℕ := fun x => (Finset.univ.filter fun i => x i = true).card
    let ν : ℝ := M/(2*(M : ℝ)+d)
    let pe : ℝ := (1+(-1 : ℝ)^M*((d : ℝ)/(2*(M : ℝ)+d))^d)/2
    let Q : (Fin d → Bool) → ℝ := fun x =>
      if h x % 2 = M % 2 then ν^(h x)*(1-ν)^(d-h x)/pe else 0
    let R : (Fin d → Bool) → ℝ := fun x =>
      if h x ≤ M ∧ h x % 2 = M % 2 then
        ((M-h x)/2+d-1).choose (d-1)/((M+d-1).choose (d-1) : ℝ) else 0
    (1/2 : ℝ)*(∑ x, |R x-Q x|) ≤
      min 1 (5*(Real.sqrt d/M+(d : ℝ)*(d-1)/(M : ℝ)^2)) := by
  classical
  dsimp only
  let h : (Fin d → Bool) → ℕ := fun x => (Finset.univ.filter fun i => x i = true).card
  let ν : ℝ := M/(2*(M : ℝ)+d)
  let pe : ℝ := (1+(-1 : ℝ)^M*((d : ℝ)/(2*(M : ℝ)+d))^d)/2
  let τ : ℝ := M/(M+d)
  let m : ℝ := d*M/(2*M+d)
  let ell : ℝ → ℝ := fun z =>
    (∑ j : Fin (d-1), Real.log ((M : ℝ)-z+2*((j : ℕ)+1))) - z*Real.log τ
  let Q : (Fin d → Bool) → ℝ := fun x =>
    if h x % 2 = M % 2 then ν^(h x)*(1-ν)^(d-h x)/pe else 0
  let R : (Fin d → Bool) → ℝ := fun x =>
    if h x ≤ M ∧ h x % 2 = M % 2 then
      ((M-h x)/2+d-1).choose (d-1)/((M+d-1).choose (d-1) : ℝ) else 0
  let X : (Fin d → Bool) → ℝ := fun x => ell (h x)-ell m
  let D : ℝ := Real.sqrt (3*d)/(2*((M : ℝ)-d)) +
    3*d*((d : ℝ)-1)/(8*((M : ℝ)-d)^2)
  let c : ℝ := ∑ x, Q x*Real.exp (X x)
  have hnormal : 0 < pe ∧ (∀ x, 0 ≤ Q x) ∧ (∑ x, Q x = 1) ∧
      (∀ x, 0 ≤ R x) ∧ (∑ x, R x = 1) ∧ c > 0 ∧
      ∀ x, R x = Q x * Real.exp (X x) / c := by
    let η : ℝ := (d : ℝ)/(2*(M : ℝ)+d)
    let w : Bool → ℝ := fun b => if b then ν else 1-ν
    let bit : Bool → ℕ := fun b => if b then 1 else 0
    let P : ℝ → ℝ := fun z => ∏ j : Fin (d-1), ((M : ℝ)-z+2*((j : ℕ)+1))
    have hdpos : 0 < d := by omega
    have hMpos : 0 < M := by omega
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
    have hbit (x : Fin d → Bool) : (∑ i, bit (x i)) = h x := by simp [bit, h]
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
    have hR0 : ∀ x, 0 ≤ R x := by
      intro x
      dsimp [R]
      split_ifs <;> positivity
    have hchoose : 0 < (M+d-1).choose (d-1) := Nat.choose_pos (by omega)
    let C : ℕ → Finset (Fin d → ℕ) := Finset.Nat.antidiagonalTuple d
    have hcard (t : ℕ) : (C t).card = (t+d-1).choose (d-1) := by
      let e : ↑(C t) ≃ Sym (Fin d) t :=
        (Equiv.subtypeEquivRight (fun r => by
          simp only [C, Finset.Nat.mem_antidiagonalTuple])).trans
          (Sym.equivNatSumOfFintype (Fin d) t).symm
      rw [Finset.card_eq_of_equiv_fintype e, Sym.card_sym_eq_choose]
      simp only [Fintype.card_fin]
      rw [Nat.add_comm, ← Nat.choose_symm (n := t+d-1) (k := t) (by omega)]
      congr 1
      omega
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
    have hfiber (x : Fin d → Bool) :
        (F x).card = if h x ≤ M ∧ h x % 2 = M % 2 then
          ((M-h x)/2+d-1).choose (d-1) else 0 := by
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
    let par : (Fin d → ℕ) → (Fin d → Bool) := fun r i => r i % 2 == 1
    have hsum : (∑ x : Fin d → Bool, (F x).card) = (C M).card := by
      have h := Finset.card_eq_sum_card_fiberwise
        (f := par) (s := C M) (t := Finset.univ) (fun r _ => Finset.mem_univ (par r))
      rw [h]
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      ext r
      simp only [F, Finset.mem_filter]
      constructor
      · rintro ⟨hmem, hr⟩
        refine ⟨hmem, ?_⟩
        funext i
        specialize hr i
        cases hb : x i <;> simp [par, bit, hb] at hr ⊢ <;> omega
      · rintro ⟨hmem, hr⟩
        refine ⟨hmem, ?_⟩
        intro i
        have hi := congr_fun hr i
        have hm := Nat.mod_lt (r i) (by decide : 0 < 2)
        cases hb : x i <;> simp [par, bit, hb] at hi ⊢ <;> omega
    have hden : (0 : ℝ) < (M+d-1).choose (d-1) := by exact_mod_cast hchoose
    have hR1 : ∑ x, R x = 1 := by
      change (∑ x : Fin d → Bool, if h x ≤ M ∧ h x % 2 = M % 2 then
          (((M-h x)/2+d-1).choose (d-1) : ℝ) / ((M+d-1).choose (d-1) : ℝ) else 0) = 1
      calc
        _ = (∑ x : Fin d → Bool, ((F x).card : ℝ)) /
            ((M+d-1).choose (d-1) : ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro x _
          rw [hfiber]
          split_ifs <;> simp
        _ = 1 := by
          rw [← Nat.cast_sum, hsum, hcard, div_self hden.ne']
    have hτ : 0 < τ := by dsimp [τ]; positivity
    have hfactor_pos (z : ℝ) (hz : z ≤ d) (j : Fin (d - 1)) :
        0 < (M : ℝ) - z + 2 * ((j : ℕ) + 1) := by
      have hj : (j : ℕ) + 1 ≤ d := by omega
      have hdR : (d : ℝ) ≤ M := by exact_mod_cast (by omega : d ≤ M)
      have hzR : z ≤ (d : ℝ) := hz
      have hjR : (0 : ℝ) ≤ (j : ℕ) := by positivity
      push_cast
      nlinarith
    have hexp_ell_nat (n : ℕ) (hn : n ≤ d) :
        Real.exp (ell (n : ℝ)) = P (n : ℝ) / τ ^ n := by
      have hp : ∀ j : Fin (d - 1), 0 < (M : ℝ) - (n : ℝ) + 2 * ((j : ℕ) + 1) := by
        intro j
        apply hfactor_pos
        exact_mod_cast hn
      dsimp [ell, P]
      rw [Real.exp_sub, Real.exp_sum]
      have hlogexp : ∀ j : Fin (d - 1),
          Real.exp (Real.log ((M : ℝ) - (n : ℝ) + 2 * ((j : ℕ) + 1))) =
            (M : ℝ) - (n : ℝ) + 2 * ((j : ℕ) + 1) := by
        intro j
        exact Real.exp_log (hp j)
      simp_rw [hlogexp]
      rw [Real.exp_nat_mul, Real.exp_log hτ]
    have hchoose_product (n : ℕ) :
        ((n + d - 1).choose (d - 1) : ℝ) =
          (Finset.univ.prod (fun j : Fin (d - 1) => ((n : ℝ) + (j : ℕ) + 1))) /
            (Nat.factorial (d - 1) : ℝ) := by
      have ha := Nat.ascFactorial_eq_factorial_mul_choose' (n + 1) (d - 1)
      rw [Nat.ascFactorial_eq_prod_range] at ha
      have hprod :
          (Finset.univ.prod (fun j : Fin (d - 1) => ((n : ℝ) + (j : ℕ) + 1))) =
            (Finset.range (d - 1)).prod (fun i => (n : ℝ) + i + 1) := by
        exact Fin.prod_univ_eq_prod_range (fun i => (n : ℝ) + i + 1) (d - 1)
      rw [hprod]
      norm_num at ha
      have haR :
          (Finset.range (d - 1)).prod (fun i => (n : ℝ) + i + 1) =
            (Nat.factorial (d - 1) : ℝ) * ((n + d - 1).choose (d - 1) : ℝ) := by
        have ha' :
            (Finset.range (d - 1)).prod (fun i => n + i + 1) =
              (d - 1).factorial * (n + d - 1).choose (d - 1) := by
          have hnd : n + (d - 1) = n + d - 1 := by omega
          rw [hnd] at ha
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ha
        exact_mod_cast ha'
      rw [haR]
      field_simp
    let a : ℝ := (M + d) / (2 * (M : ℝ) + d)
    let B : ℝ := a ^ d / pe
    let A : ℝ := ((M + d - 1).choose (d - 1) : ℝ)
    have ha : 0 < a := by dsimp [a]; positivity
    have hνrel : ν = τ * a := by
      dsimp [ν, τ, a]
      field_simp
    have h1νrel : 1 - ν = a := by
      dsimp [ν, a]
      field_simp
      ring
    have hB : 0 < B := by dsimp [B]; positivity
    have hA : 0 < A := by dsimp [A]; exact hden
    have hxd (x : Fin d → Bool) : h x ≤ d := by
      dsimp [h]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
    have hQweight (x : Fin d → Bool) (hx : h x % 2 = M % 2) :
        Q x = B * τ ^ (h x) := by
      have hsum : h x + (d - h x) = d := Nat.add_sub_of_le (hxd x)
      dsimp [Q, B]
      rw [if_pos hx, h1νrel, hνrel, mul_pow]
      have hpow : a ^ h x * a ^ (d - h x) = a ^ d := by
        rw [← pow_add, hsum]
      rw [show (τ ^ h x * a ^ h x * a ^ (d - h x)) / pe =
          (τ ^ h x * (a ^ h x * a ^ (d - h x))) / pe by ring, hpow]
      ring
    have hhalf (x : Fin d → Bool) (hxM : h x ≤ M)
        (hxpar : h x % 2 = M % 2) : M - h x = 2 * ((M - h x) / 2) := by
      have hm := Nat.mod_add_div (M - h x) 2
      have hmod : (M - h x) % 2 = 0 := by omega
      omega
    have hPchoose (x : Fin d → Bool) (hxM : h x ≤ M)
        (hxpar : h x % 2 = M % 2) :
        P (h x) = (2 : ℝ) ^ (d - 1) *
          (Nat.factorial (d - 1) : ℝ) *
            (((M - h x) / 2 + d - 1).choose (d - 1) : ℝ) := by
      have hu := hchoose_product ((M - h x) / 2)
      dsimp [P]
      calc
        _ = Finset.univ.prod (fun j : Fin (d - 1) =>
            (2 : ℝ) * (((M - h x) / 2 : ℕ) + (j : ℕ) + 1)) := by
          apply Finset.prod_congr rfl
          intro j hj
          have hh := hhalf x hxM hxpar
          push_cast
          rw [show (M : ℝ) - (h x : ℝ) = 2 * (((M - h x) / 2 : ℕ) : ℝ) by
            exact_mod_cast hh]
          ring
        _ = (Finset.univ.prod (fun _ : Fin (d - 1) => (2 : ℝ))) *
            (Finset.univ.prod (fun j : Fin (d - 1) =>
              (((M - h x) / 2 : ℕ) : ℝ) + (j : ℕ) + 1)) := by
          rw [Finset.prod_mul_distrib]
        _ = (2 : ℝ) ^ (d - 1) *
            (Finset.univ.prod (fun j : Fin (d - 1) =>
              (((M - h x) / 2 : ℕ) : ℝ) + (j : ℕ) + 1)) := by
          simp
        _ = (2 : ℝ) ^ (d - 1) *
            (Nat.factorial (d - 1) : ℝ) *
              (((M - h x) / 2 + d - 1).choose (d - 1) : ℝ) := by
          rw [hu]
          have hfpos : (0 : ℝ) < (Nat.factorial (d - 1) : ℝ) := by positivity
          field_simp [hfpos.ne']
    have hRform (x : Fin d → Bool) (hxM : h x ≤ M)
        (hxpar : h x % 2 = M % 2) :
        R x = P (h x) /
          (A * (2 : ℝ) ^ (d - 1) * (Nat.factorial (d - 1) : ℝ)) := by
      dsimp [R]
      rw [if_pos ⟨hxM, hxpar⟩, hPchoose x hxM hxpar]
      dsimp [A]
      field_simp [hden.ne']
    have hVform (x : Fin d → Bool) (hxpar : h x % 2 = M % 2) :
        Q x * Real.exp (ell (h x) - ell m) =
          (B / Real.exp (ell m)) * P (h x) := by
      have hxe := hexp_ell_nat (h x) (hxd x)
      rw [hQweight x hxpar, Real.exp_sub, hxe]
      have htaux : (τ ^ h x : ℝ) ≠ 0 := pow_ne_zero _ hτ.ne'
      field_simp [htaux, (Real.exp_pos (ell m)).ne']
    let κ : ℝ := Real.exp (ell m) /
      (B * A * (2 : ℝ) ^ (d - 1) * (Nat.factorial (d - 1) : ℝ))
    have hκ : 0 < κ := by
      dsimp [κ]
      positivity
    have hprop (x : Fin d → Bool) :
        R x = κ * (Q x * Real.exp (ell (h x) - ell m)) := by
      by_cases hxpar : h x % 2 = M % 2
      · have hxM : h x ≤ M := by
          have hxd' := hxd x
          omega
        rw [hRform x hxM hxpar, hVform x hxpar]
        dsimp [κ]
        field_simp [hA.ne', hB.ne', (Real.exp_pos (ell m)).ne']
      · dsimp [R, Q]
        simp [hxpar]
    have hsumprop : (∑ x, R x) = κ * c := by
      calc
        (∑ x, R x) = ∑ x, κ * (Q x * Real.exp (ell (h x) - ell m)) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hprop x
        _ = κ * c := by
          dsimp [c]
          rw [Finset.mul_sum]
    have hkc : κ * c = 1 := by nlinarith [hR1, hsumprop]
    have hc : 0 < c := by nlinarith [hκ, hkc]
    have hk : κ = 1 / c := (eq_div_iff hc.ne').2 hkc
    refine ⟨hpe, hQ0, hQ1, hR0, hR1, ?_, ?_⟩
    · exact hc
    · intro x
      change R x = Q x * Real.exp (ell (h x) - ell m) / c
      rw [hprop x, hk]
      ring
  change 0 < pe ∧ (∀ x, 0 ≤ Q x) ∧ (∑ x, Q x = 1) ∧
    (∀ x, 0 ≤ R x) ∧ (∑ x, R x = 1) ∧ c > 0 ∧
    ∀ x, R x = Q x * Real.exp (X x) / c at hnormal
  obtain ⟨hpe, hQ, hQ1, hR, hR1, hc, hdensity⟩ := hnormal
  have hanalytic : ∀ y ∈ Set.Icc (0 : ℝ) d,
      |ell y-ell m| ≤ (1/((M : ℝ)-d))*|y-m| +
        (((d : ℝ)-1)/((M : ℝ)-d)^2)/2*(y-m)^2 ∧ ell y-ell m ≤ 1/2 := by
    let slope : ℝ → ℝ := fun z =>
      -(∑ j : Fin (d - 1), 1 / ((M : ℝ) - z + 2 * ((j : ℕ) + 1))) - Real.log τ
    let curvature : ℝ → ℝ := fun z =>
      -(∑ j : Fin (d - 1), 1 / ((M : ℝ) - z + 2 * ((j : ℕ) + 1)) ^ 2)
    let A0 : ℝ := 1 / ((M : ℝ) - d)
    let B0 : ℝ := ((d : ℝ) - 1) / ((M : ℝ) - d)^2
    have hcenter : 0 ≤ slope m ∧ slope m ≤ A0 := by
      dsimp only [slope]
      let A : ℝ := (M : ℝ) - m
      let f : ℝ → ℝ := fun y => 1 / (A + 2 * y)
      have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have hMR : 3 * (d : ℝ) ≤ M := by exact_mod_cast hM
      have hMpos : (0 : ℝ) < M := by linarith
      have hden : (0 : ℝ) < 2 * M + d := by linarith
      have hbase : (0 : ℝ) < M - d := by linarith
      have hm : m < d := by
        dsimp [m]
        apply (div_lt_iff₀ hden).2
        nlinarith
      have hA : 0 < A := by dsimp [A]; linarith
      have hAeq : A = 2 * (M : ℝ)^2 / (2 * M + d) := by
        dsimp [A, m]
        field_simp
        ring
      have hend : A + 2 * d = 2 * ((M : ℝ) + d)^2 / (2 * M + d) := by
        dsimp [A, m]
        field_simp
        ring
      have hratio : (A + 2 * d) / A = (((M : ℝ) + d) / M)^2 := by
        rw [hend, hAeq]
        field_simp
      have hlog : Real.log ((A + 2 * d) / A) = -2 * Real.log τ := by
        rw [hratio, Real.log_pow, Real.log_div (by linarith : (M : ℝ) + d ≠ 0) hMpos.ne']
        dsimp [τ]
        rw [Real.log_div hMpos.ne' (by linarith : (M : ℝ) + d ≠ 0)]
        ring
      have hint : (∫ y in (0 : ℝ)..d, f y) = -Real.log τ := by
        dsimp only [f]
        simp only [one_div]
        rw [intervalIntegral.integral_comp_add_mul (fun y : ℝ => y⁻¹)
          (by norm_num : (2 : ℝ) ≠ 0) A]
        simp only [mul_zero, add_zero, smul_eq_mul]
        rw [integral_inv_of_pos hA (by linarith : 0 < A + 2 * d), hlog]
        norm_num
        ring
      have hanti : AntitoneOn f (Set.Icc (0 : ℝ) d) := by
        intro x hx y hy hxy
        dsimp [f]
        exact one_div_le_one_div_of_le (by linarith [hx.1] : 0 < A + 2 * x)
          (by linarith : A + 2 * x ≤ A + 2 * y)
      have hanti' : AntitoneOn f (Set.Icc (0 : ℝ) (0 + d)) := by simpa using hanti
      have hlo := hanti'.integral_le_sum (x₀ := (0 : ℝ)) (a := d)
      have hhi := hanti'.sum_le_integral (x₀ := (0 : ℝ)) (a := d)
      simp only [zero_add] at hlo hhi
      rw [hint] at hlo hhi
      have hds : d - 1 + 1 = d := by omega
      have hsum : (∑ j : Fin (d - 1), 1 / ((M : ℝ) - m + 2 * ((j : ℕ) + 1))) =
          ∑ i ∈ Finset.range (d - 1), f (((i + 1 : ℕ) : ℝ)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (Fin.sum_univ_eq_sum_range (fun i : ℕ => f ((i : ℝ) + 1)) (d - 1))
      have hlow : (∑ i ∈ Finset.range d, f (i : ℝ)) =
          (∑ i ∈ Finset.range (d - 1), f (((i + 1 : ℕ) : ℝ))) + f 0 := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega]
        simpa only [Nat.cast_zero] using Finset.sum_range_succ' (fun i : ℕ => f (i : ℝ)) (d - 1)
      have hhigh : (∑ i ∈ Finset.range d, f (((i + 1 : ℕ) : ℝ))) =
          (∑ i ∈ Finset.range (d - 1), f (((i + 1 : ℕ) : ℝ))) + f (d : ℝ) := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega]
        rw [Finset.sum_range_succ, hds]
      rw [hlow] at hlo
      rw [hhigh] at hhi
      have hfd : 0 ≤ f (d : ℝ) := by
        dsimp [f]
        have : 0 < A + 2 * (d : ℝ) := by linarith
        positivity
      have hf0 : f 0 ≤ 1 / ((M : ℝ) - d) := by
        dsimp [f]
        simp only [mul_zero, add_zero]
        apply one_div_le_one_div_of_le hbase
        dsimp [A]
        linarith
      rw [hsum]
      constructor <;> linarith
    have hcalculusRaw : ∀ z ∈ Set.Icc (0 : ℝ) d,
        HasDerivAt ell (slope z) z ∧ HasDerivAt slope (curvature z) z ∧
          -((d : ℝ)-1)/((M : ℝ)-d)^2 ≤ curvature z ∧ curvature z ≤ 0 := by
      have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have hMR : 3 * (d : ℝ) ≤ M := by exact_mod_cast hM
      have hbase : 0 < (M : ℝ) - d := by linarith
      intro z hz
      have harg (j : Fin (d - 1)) :
          0 < (M : ℝ) - z + 2 * ((j : ℕ) + 1) := by
        have hj : (0 : ℝ) ≤ (j : ℕ) := by positivity
        linarith [hz.2]
      have hD (j : Fin (d - 1)) :
          HasDerivAt (fun x : ℝ => (M : ℝ) - x + 2 * ((j : ℕ) + 1)) (-1) z := by
        simpa using ((hasDerivAt_id z).const_sub (M : ℝ)).add_const
          (2 * (((j : ℕ) : ℝ) + 1))
      have hlog (j : Fin (d - 1)) :
          HasDerivAt (fun x : ℝ => Real.log ((M : ℝ) - x + 2 * ((j : ℕ) + 1)))
            (-(1 / ((M : ℝ) - z + 2 * ((j : ℕ) + 1)))) z := by
        simpa only [neg_div, one_div] using (hD j).log (harg j).ne'
      have hinv (j : Fin (d - 1)) :
          HasDerivAt (fun x : ℝ => 1 / ((M : ℝ) - x + 2 * ((j : ℕ) + 1)))
            (1 / ((M : ℝ) - z + 2 * ((j : ℕ) + 1)) ^ 2) z := by
        simpa only [neg_neg, one_div] using (hD j).fun_inv (harg j).ne'
      have hfirst : HasDerivAt ell (slope z) z := by
        have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hlog j)
        simpa only [ell, slope, Finset.sum_neg_distrib, one_mul, id_eq] using
          hs.fun_sub ((hasDerivAt_id z).mul_const (Real.log τ))
      have hsecond : HasDerivAt slope (curvature z) z := by
        exact (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hinv j)).fun_neg.sub_const
          (Real.log τ)
      have hsum0 : 0 ≤ ∑ j : Fin (d - 1),
          1 / ((M : ℝ) - z + 2 * ((j : ℕ) + 1)) ^ 2 := by
        exact Finset.sum_nonneg (fun j _ => by positivity)
      have hsumle : (∑ j : Fin (d - 1),
          1 / ((M : ℝ) - z + 2 * ((j : ℕ) + 1)) ^ 2) ≤
            ((d : ℝ) - 1) / ((M : ℝ) - d)^2 := by
        calc
          _ ≤ ∑ _j : Fin (d - 1), 1 / ((M : ℝ) - d)^2 := by
            apply Finset.sum_le_sum
            intro j _
            have hj : (0 : ℝ) ≤ (j : ℕ) := by positivity
            have hgap : (M : ℝ) - d ≤ (M : ℝ) - z + 2 * ((j : ℕ) + 1) := by
              push_cast
              linarith [hz.2]
            exact one_div_le_one_div_of_le (sq_pos_of_pos hbase)
              (sq_le_sq₀ hbase.le (harg j).le |>.2 hgap)
          _ = _ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [Nat.cast_sub (by omega : 1 ≤ d)]
            push_cast
            ring
      refine ⟨hfirst, hsecond, ?_, ?_⟩
      · change -((d : ℝ) - 1) / ((M : ℝ) - d)^2 ≤
          -(∑ j : Fin (d - 1), 1 / ((M : ℝ) - z + 2 * ((j : ℕ) + 1)) ^ 2)
        simpa only [neg_div] using neg_le_neg hsumle
      · exact neg_nonpos.mpr hsum0
    have hcalculus : ∀ z ∈ Set.Icc (0 : ℝ) d,
        HasDerivAt ell (slope z) z ∧ HasDerivAt slope (curvature z) z ∧
          -B0 ≤ curvature z ∧ curvature z ≤ 0 := by
      simpa only [B0, neg_div] using hcalculusRaw
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hMR : 3 * (d : ℝ) ≤ M := by exact_mod_cast hM
    have hbase : 0 < (M : ℝ) - d := by linarith
    have hden : 0 < 2 * (M : ℝ) + d := by linarith
    have hM0 : (0 : ℝ) < M := by linarith
    have hd0 : (0 : ℝ) < d := by linarith
    have hm0 : 0 < m := by dsimp [m]; positivity
    have hmd : m < d := by
      dsimp [m]
      apply (div_lt_iff₀ hden).2
      nlinarith
    have hmI : m ∈ Set.Icc (0 : ℝ) d := ⟨hm0.le, hmd.le⟩
    have hmInt : m ∈ interior (Set.Icc (0 : ℝ) d) := by
      rw [interior_Icc]
      exact ⟨hm0, hmd⟩
    let F : ℝ → ℝ → ℝ := fun K z =>
      ell z - ell m - slope m * (z-m) + K/2*(z-m)^2
    have hFd (K : ℝ) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) d) :
        HasDerivAt (F K) (slope z - slope m + K*(z-m)) z := by
      convert! (((hcalculus z hz).1.sub_const (ell m)).fun_sub
        (((hasDerivAt_id z).sub_const m).const_mul (slope m))).fun_add
        ((((hasDerivAt_id z).sub_const m).pow 2).const_mul (K/2)) using 1 <;>
        dsimp [F] <;> ring
    have hFdd (K : ℝ) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) d) :
        HasDerivAt (fun y => slope y - slope m + K*(y-m)) (curvature z + K) z := by
      convert! ((hcalculus z hz).2.1.sub_const (slope m)).fun_add
        (((hasDerivAt_id z).sub_const m).const_mul K) using 1 <;> ring
    have hFc : ConvexOn ℝ (Set.Icc (0 : ℝ) d) (F B0) := by
      apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
        (fun z hz => (hFd B0 z hz).continuousAt.continuousWithinAt)
        (fun z hz => (hFd B0 z (interior_subset hz)).hasDerivWithinAt)
        (fun z hz => (hFdd B0 z (interior_subset hz)).hasDerivWithinAt)
      intro z hz
      linarith [(hcalculus z (interior_subset hz)).2.2.1]
    have hGc : ConvexOn ℝ (Set.Icc (0 : ℝ) d) (fun z => -(F 0 z)) := by
      apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
        (fun z hz => (hFd 0 z hz).fun_neg.continuousAt.continuousWithinAt)
        (fun z hz => (hFd 0 z (interior_subset hz)).fun_neg.hasDerivWithinAt)
        (fun z hz => (hFdd 0 z (interior_subset hz)).fun_neg.hasDerivWithinAt)
      intro z hz
      have hc := (hcalculus z (interior_subset hz)).2.2.2
      linarith
    have hFmin : IsMinOn (F B0) (Set.Icc (0 : ℝ) d) m := by
      apply hFc.isMinOn_of_rightDeriv_eq_zero hmInt
      simpa only [sub_self, mul_zero, add_zero] using
        (hFd B0 m hmI).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi m)
    have hGmin : IsMinOn (fun z => -(F 0 z)) (Set.Icc (0 : ℝ) d) m := by
      apply hGc.isMinOn_of_rightDeriv_eq_zero hmInt
      simpa only [sub_self, mul_zero, add_zero, neg_zero] using
        (hFd 0 m hmI).fun_neg.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi m)
    intro h hh
    have hlo := hFmin hh
    have hhi := hGmin hh
    dsimp [F] at hlo hhi
    have htan : ell h - ell m ≤ slope m * (h-m) := by linarith
    have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
    have hB0 : 0 ≤ B0 := by
      exact div_nonneg (by linarith : 0 ≤ (d : ℝ)-1) (sq_nonneg _)
    have habs : |slope m * (h-m)| ≤ A0 * |h-m| := by
      rw [abs_mul, abs_of_nonneg hcenter.1]
      exact mul_le_mul_of_nonneg_right hcenter.2 (abs_nonneg _)
    have htanabs : slope m * (h-m) ≤ A0 * |h-m| :=
      (le_abs_self _).trans habs
    have hnegtanabs : -(slope m * (h-m)) ≤ A0 * |h-m| :=
      (neg_le_abs _).trans habs
    have hrem0 : 0 ≤ B0/2*(h-m)^2 := by positivity
    constructor
    · apply abs_le.mpr
      constructor <;> linarith
    · have hdelta : h-m ≤ (d : ℝ) := by linarith [hh.2]
      have hslope : slope m * (h-m) ≤ A0*(d : ℝ) := by
        calc
          _ ≤ slope m * (d : ℝ) := mul_le_mul_of_nonneg_left hdelta hcenter.1
          _ ≤ A0*(d : ℝ) := mul_le_mul_of_nonneg_right hcenter.2 (by positivity)
      have hAhalf : A0*(d : ℝ) ≤ 1/2 := by
        dsimp [A0]
        rw [one_div_mul_eq_div]
        apply (div_le_iff₀ hbase).2
        linarith
      exact htan.trans (hslope.trans hAhalf)
  have hmoments : 1/3 ≤ pe ∧ (∑ x, Q x*((h x : ℝ)-m)^2) ≤ 3*d/4 ∧
      (∑ x, Q x*|(h x : ℝ)-m|) ≤ Real.sqrt (3*d)/2 := by
    let η : ℝ := (d : ℝ)/(2*(M : ℝ)+d)
    have hdpos : 0 < d := by omega
    have hMpos : 0 < M := by omega
    have hden : 0 < 2*(M : ℝ)+d := by positivity
    have hν : 0 < ν := by dsimp [ν]; positivity
    have hν1 : ν < 1 := by
      dsimp [ν]
      apply (div_lt_one hden).mpr
      linarith [show (0 : ℝ) < 2*M by positivity]
    have hη : 0 ≤ η := by dsimp [η]; positivity
    have hη1 : η < 1 := by
      dsimp [η]
      apply (div_lt_one hden).mpr
      linarith [show (0 : ℝ) < 2*M by positivity]
    let w : Bool → ℝ := fun b => if b then ν else 1-ν
    have hw (x : Fin d → Bool) : (∏ i, w (x i)) = ν^(h x)*(1-ν)^(d-h x) := by
      simp only [w]
      rw [Finset.prod_ite]
      simp only [Finset.prod_const]
      have hc : (Finset.univ.filter fun i : Fin d => ¬x i = true).card = d-h x := by
        rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
        simp [h]
      rw [hc]
    have hQ0 := hQ
    have hsecond : (∑ x : Fin d → Bool, ((h x : ℝ)-d*ν)^2*∏ i, w (x i)) =
        d*ν*(1-ν) := by
      let z : Bool → ℝ := fun b => (if b then 1 else 0) - ν
      have hw : (∑ b : Bool, w b) = 1 := by simp [w]
      have hz : (∑ b : Bool, z b * w b) = 0 := by simp [z, w]; ring
      have hz2 : (∑ b : Bool, z b^2 * w b) = ν * (1 - ν) := by simp [z, w]; ring
      have hcenter (x : Fin d → Bool) : (h x : ℝ) - d * ν = ∑ i, z (x i) := by
        have hc : (∑ i : Fin d, (if x i then 1 else 0 : ℕ)) = h x := by simp [h]
        have hcr : (∑ i : Fin d, (if x i then (1 : ℝ) else 0)) = (h x : ℝ) := by
          exact_mod_cast hc
        dsimp only [z]
        rw [Finset.sum_sub_distrib, hcr]
        simp
      have hdiag (i : Fin d) :
          (∑ x : Fin d → Bool, z (x i)^2 * ∏ k, w (x k)) = ν * (1 - ν) := by
        have hp (x : Fin d → Bool) :
            z (x i)^2 * ∏ k, w (x k) =
              ∏ k, (if k = i then z (x k)^2 else 1) * w (x k) := by
          rw [Finset.prod_mul_distrib]
          simp
        simp_rw [hp]
        rw [← Fintype.prod_sum (fun (k : Fin d) (b : Bool) => (if k = i then z b^2 else 1) * w b)]
        have hs (k : Fin d) :
            (∑ b : Bool, (if k = i then z b^2 else 1) * w b) =
              if k = i then ν * (1 - ν) else 1 := by
          by_cases hk : k = i
          · simpa only [if_pos hk] using hz2
          · simpa only [if_neg hk, one_mul] using hw
        simp_rw [hs]
        simp
      have hcross (i j : Fin d) (hij : i ≠ j) :
          (∑ x : Fin d → Bool, z (x i) * z (x j) * ∏ k, w (x k)) = 0 := by
        have hp (x : Fin d → Bool) :
            z (x i) * z (x j) * ∏ k, w (x k) =
              ∏ k, ((if k = i then z (x k) else 1) *
                (if k = j then z (x k) else 1)) * w (x k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
          simp
        simp_rw [hp]
        rw [← Fintype.prod_sum (fun (k : Fin d) (b : Bool) => ((if k = i then z b else 1) * (if k = j then z b else 1)) * w b)]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simpa only [if_pos rfl, if_true, if_neg hij, mul_one] using hz
      have hpair (i j : Fin d) :
          (∑ x : Fin d → Bool, z (x i) * z (x j) * ∏ k, w (x k)) =
            if i = j then ν * (1 - ν) else 0 := by
        by_cases hij : i = j
        · subst j
          simpa only [if_pos rfl, if_true, ← sq] using hdiag i
        · simpa [hij] using hcross i j hij
      calc
        _ = ∑ x : Fin d → Bool, (∑ i, ∑ j, z (x i) * z (x j)) * ∏ k, w (x k) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hcenter, sq, Fintype.sum_mul_sum]
        _ = ∑ i : Fin d, ∑ j : Fin d, ∑ x : Fin d → Bool,
            z (x i) * z (x j) * ∏ k, w (x k) := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = ∑ i : Fin d, ∑ j : Fin d, if i = j then ν * (1 - ν) else 0 := by
          simp_rw [hpair]
        _ = _ := by simp; ring
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hMR : 3 * (d : ℝ) ≤ M := by exact_mod_cast hM
    have hηsmall : η ≤ 1/7 := by
      dsimp [η]
      apply (div_le_iff₀ hden).2
      linarith
    have hηpower : η^d ≤ 1/7 :=
      (pow_le_of_le_one hη hη1.le (by omega : d ≠ 0)).trans hηsmall
    have hpelower : 1/3 ≤ pe := by
      rcases neg_one_pow_eq_or ℝ M with hs | hs <;>
        dsimp [pe] <;> rw [hs] <;> nlinarith [pow_nonneg hη d]
    have hcenter : m = d * ν := by dsimp [m, ν]; ring
    change (∑ x : Fin d → Bool, ((h x : ℝ) - d*ν)^2 * ∏ i, w (x i)) =
      d * ν * (1-ν) at hsecond
    have hsecondle : (∑ x : Fin d → Bool, Q x * ((h x : ℝ)-m)^2) ≤ 3*d/4 := by
      calc
        _ = (∑ x : Fin d → Bool,
            if h x % 2 = M % 2 then ((h x : ℝ)-m)^2 * ∏ i, w (x i) else 0)/pe := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro x _
          dsimp [Q]
          rw [← hw]
          split_ifs <;> ring
        _ ≤ (∑ x : Fin d → Bool, ((h x : ℝ)-m)^2 * ∏ i, w (x i))/pe := by
          apply div_le_div_of_nonneg_right _ hpe.le
          apply Finset.sum_le_sum
          intro x _
          split_ifs
          · exact le_rfl
          · apply mul_nonneg (sq_nonneg _)
            apply Finset.prod_nonneg
            intro i _
            dsimp [w]
            split_ifs <;> linarith
        _ = (d*ν*(1-ν))/pe := by rw [hcenter, hsecond]
        _ ≤ 3*d/4 := by
          apply (div_le_iff₀ hpe).2
          have hv : d*ν*(1-ν) ≤ (d : ℝ)/4 := by
            nlinarith [mul_nonneg (show (0 : ℝ) ≤ d by positivity) (sq_nonneg (ν-1/2))]
          nlinarith
    have hfirstle : (∑ x : Fin d → Bool, Q x * |(h x : ℝ)-m|) ≤
        Real.sqrt (3*d)/2 := by
      have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin d → Bool))
        (f := fun x => Q x) (g := fun x => Q x * ((h x : ℝ)-m)^2)
        hQ0 (fun x => mul_nonneg (hQ0 x) (sq_nonneg _))
      have hsqrt (x : Fin d → Bool) :
          Real.sqrt (Q x) * Real.sqrt (Q x * ((h x : ℝ)-m)^2) =
            Q x * |(h x : ℝ)-m| := by
        rw [Real.sqrt_mul (hQ0 x), Real.sqrt_sq_eq_abs, ← mul_assoc,
          Real.mul_self_sqrt (hQ0 x)]
      simp_rw [hsqrt] at hcs
      rw [hQ1, Real.sqrt_one, one_mul] at hcs
      calc
        _ ≤ Real.sqrt (∑ x : Fin d → Bool, Q x * ((h x : ℝ)-m)^2) := hcs
        _ ≤ Real.sqrt (3*d/4) := Real.sqrt_le_sqrt hsecondle
        _ = _ := by rw [Real.sqrt_div (by positivity), show Real.sqrt (4 : ℝ) = 2 by norm_num]
    exact ⟨hpelower, hsecondle, hfirstle⟩
  have hconstants : 0 ≤ D ∧ D < 1/2 ∧
      Real.exp 1*D ≤ 5*(Real.sqrt d/M+(d : ℝ)*(d-1)/(M : ℝ)^2) := by
    let C : ℝ := (M : ℝ)-d
    let S : ℝ := Real.sqrt (3*d)
    let D : ℝ := S/(2*C) + 3*d*((d : ℝ)-1)/(8*C^2)
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hMR : 3*(d : ℝ) ≤ M := by exact_mod_cast hM
    have hd0 : (0 : ℝ) < d := by linarith
    have hM0 : (0 : ℝ) < M := by linarith
    have hC0 : 0 < C := by dsimp [C]; linarith
    have hC2 : 2*(d : ℝ) ≤ C := by dsimp [C]; linarith
    have hCM : 2*(M : ℝ)/3 ≤ C := by dsimp [C]; linarith
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    have hC2sq : (2*(d : ℝ))^2 ≤ C^2 :=
      (sq_le_sq₀ (by positivity) hC0.le).2 hC2
    have hfirst : S/(2*C) < 3/8 := by
      have hs : S < 3*C/4 := by
        apply (Real.sqrt_lt (by positivity : (0 : ℝ) ≤ 3*d)
          (by positivity : 0 ≤ 3*C/4)).2
        have hd2 : 2*(d : ℝ) ≤ (d : ℝ)^2 := by
          nlinarith [mul_nonneg hd0.le (show 0 ≤ (d : ℝ)-2 by linarith)]
        nlinarith
      apply (div_lt_iff₀ (by positivity : 0 < 2*C)).2
      linarith
    have hsecond : 3*d*((d : ℝ)-1)/(8*C^2) < 3/32 := by
      apply (div_lt_iff₀ (by positivity : 0 < 8*C^2)).2
      nlinarith
    have hdminus : 0 ≤ (d : ℝ)-1 := by linarith
    have hD0 : 0 ≤ D := by
      dsimp [D]
      exact add_nonneg (div_nonneg hS0 (by positivity))
        (div_nonneg (by positivity : 0 ≤ 3*(d : ℝ)*((d : ℝ)-1)) (by positivity))
    have hDhalf : D < 1/2 := by dsimp [D]; linarith
    have hInv : 1/C ≤ (3/2)/M := by
      apply (div_le_div_iff₀ hC0 hM0).2
      linarith
    have hInv2 : 1/C^2 ≤ (9/4)/(M : ℝ)^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hC0) (sq_pos_of_pos hM0)).2
      have hs : (2*(M : ℝ)/3)^2 ≤ C^2 :=
        (sq_le_sq₀ (by positivity) hC0.le).2 hCM
      nlinarith
    have hS : S = Real.sqrt 3 * Real.sqrt d := Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) _
    have hfirstCmp : S/(2*C) ≤ (3*Real.sqrt 3/4)*(Real.sqrt d/M) := by
      calc
        _ = (S/2)*(1/C) := by ring
        _ ≤ (S/2)*((3/2)/M) := mul_le_mul_of_nonneg_left hInv (by positivity)
        _ = _ := by rw [hS]; ring
    have hsecondCmp : 3*d*((d : ℝ)-1)/(8*C^2) ≤
        (27/32)*((d : ℝ)*(d-1)/(M : ℝ)^2) := by
      have hnum : 0 ≤ 3*(d : ℝ)*((d : ℝ)-1)/8 := by positivity
      calc
        _ = (3*d*((d : ℝ)-1)/8)*(1/C^2) := by ring
        _ ≤ (3*d*((d : ℝ)-1)/8)*((9/4)/(M : ℝ)^2) :=
          mul_le_mul_of_nonneg_left hInv2 hnum
        _ = _ := by ring
    have hDCmp : D ≤ (3*Real.sqrt 3/4)*(Real.sqrt d/M) +
        (27/32)*((d : ℝ)*(d-1)/(M : ℝ)^2) := add_le_add hfirstCmp hsecondCmp
    have hp : 0 ≤ Real.sqrt d/(M : ℝ) := by positivity
    have hq : 0 ≤ (d : ℝ)*(d-1)/(M : ℝ)^2 := by positivity
    have hs3 : Real.sqrt (3 : ℝ) ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
    have ha : 3*(3*Real.sqrt (3 : ℝ)/4) ≤ 5 := by linarith
    have hb : (3 : ℝ)*(27/32) ≤ 5 := by norm_num
    have hfinal : Real.exp 1 * D ≤
        5*(Real.sqrt d/M + (d : ℝ)*(d-1)/(M : ℝ)^2) := by
      calc
        _ ≤ 3*D := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hD0
        _ ≤ 3*((3*Real.sqrt 3/4)*(Real.sqrt d/M) +
            (27/32)*((d : ℝ)*(d-1)/(M : ℝ)^2)) :=
          mul_le_mul_of_nonneg_left hDCmp (by norm_num)
        _ = (3*(3*Real.sqrt 3/4))*(Real.sqrt d/M) +
            (3*(27/32))*((d : ℝ)*(d-1)/(M : ℝ)^2) := by ring
        _ ≤ 5*(Real.sqrt d/M) + 5*((d : ℝ)*(d-1)/(M : ℝ)^2) :=
          add_le_add (mul_le_mul_of_nonneg_right ha hp) (mul_le_mul_of_nonneg_right hb hq)
        _ = _ := by ring
    exact ⟨hD0, hDhalf, hfinal⟩
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hMR : 3*(d : ℝ) ≤ M := by exact_mod_cast hM
  have hbase : 0 < (M : ℝ)-d := by linarith
  have hcount (x : Fin d → Bool) : h x ≤ d := by
    exact (Finset.card_filter_le _ _).trans_eq (by simp)
  have hX (x : Fin d → Bool) : X x ≤ 1/2 :=
    (hanalytic (h x) ⟨by positivity, by exact_mod_cast hcount x⟩).2
  have hD0 : 0 ≤ D := hconstants.1
  have hD : D < 1/2 := hconstants.2.1
  have hEX : ∑ x, Q x * |X x| ≤ D := by
    have hA0 : 0 ≤ 1/((M : ℝ)-d) := by positivity
    have hB0 : 0 ≤ ((d : ℝ)-1)/((M : ℝ)-d)^2/2 := by
      apply div_nonneg _ (by norm_num)
      exact div_nonneg (by linarith) (sq_nonneg _)
    calc
      _ ≤ ∑ x, Q x * (1/((M : ℝ)-d)*|(h x : ℝ)-m| +
          (((d : ℝ)-1)/((M : ℝ)-d)^2)/2*((h x : ℝ)-m)^2) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left
          (hanalytic (h x) ⟨by positivity, by exact_mod_cast hcount x⟩).1 (hQ x)
      _ = (1/((M : ℝ)-d))*(∑ x, Q x*|(h x : ℝ)-m|) +
          ((((d : ℝ)-1)/((M : ℝ)-d)^2)/2)*(∑ x, Q x*((h x : ℝ)-m)^2) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ (1/((M : ℝ)-d))*(Real.sqrt (3*d)/2) +
          ((((d : ℝ)-1)/((M : ℝ)-d)^2)/2)*(3*d/4) :=
        add_le_add (mul_le_mul_of_nonneg_left hmoments.2.2 hA0)
          (mul_le_mul_of_nonneg_left hmoments.2.1 hB0)
      _ = D := by dsimp [D]; field_simp [hbase.ne'] <;> ring
  have hnormalized : (1/2 : ℝ)*∑ x, |Q x*Real.exp (X x)/c-Q x| ≤ Real.exp 1*D := by
    classical
    let c : ℝ := ∑ x, Q x * Real.exp (X x)
    let E : ℝ := ∑ x, Q x * |Real.exp (X x) - 1|
    have hmean : -D ≤ ∑ x, Q x * X x := by
      have hs : -(∑ x, Q x * |X x|) ≤ ∑ x, Q x * X x := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro x _
        have hi : -|X x| ≤ X x := by linarith [neg_le_abs (X x)]
        nlinarith [mul_le_mul_of_nonneg_left hi (hQ x)]
      linarith
    have hJ : Real.exp (∑ x, Q x * X x) ≤ c := by
      simpa only [smul_eq_mul, c] using
        (convexOn_exp.map_sum_le (t := Finset.univ) (w := Q) (p := X)
          (fun x _ => hQ x) hQ1 (fun x _ => Set.mem_univ (X x)))
    have hclower : Real.exp (-D) ≤ c := (Real.exp_le_exp.mpr hmean).trans hJ
    have hc : 0 < c := (Real.exp_pos (-D)).trans_le hclower
    have hexp (x : ℝ) (hx : x ≤ 1/2) :
        |Real.exp x - 1| ≤ Real.exp (1/2) * |x| := by
      by_cases hx0 : 0 ≤ x
      · have he := norm_image_sub_le_of_norm_deriv_le_segment'
          (a := (0 : ℝ)) (b := x) (f := Real.exp) (f' := Real.exp)
          (C := Real.exp (1/2))
          (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt)
          (fun z hz => by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
            exact Real.exp_le_exp.mpr (hz.2.le.trans hx)) x ⟨hx0, le_rfl⟩
        simpa only [Real.norm_eq_abs, Real.exp_zero, sub_zero, abs_of_nonneg hx0] using he
      · have hxn : x < 0 := lt_of_not_ge hx0
        have he := norm_image_sub_le_of_norm_deriv_le_segment'
          (a := x) (b := (0 : ℝ)) (f := Real.exp) (f' := Real.exp)
          (C := Real.exp (1/2))
          (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt)
          (fun z hz => by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
            exact Real.exp_le_exp.mpr (by linarith [hz.2])) 0 ⟨hxn.le, le_rfl⟩
        simpa only [Real.norm_eq_abs, Real.exp_zero, zero_sub, abs_sub_comm,
          abs_of_neg hxn] using he
    have hE0 : 0 ≤ E := Finset.sum_nonneg (fun x _ => mul_nonneg (hQ x) (abs_nonneg _))
    have hE : E ≤ Real.exp (1/2) * D := by
      calc
        E ≤ ∑ x, Q x * (Real.exp (1/2) * |X x|) :=
          Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hexp (X x) (hX x)) (hQ x))
        _ = Real.exp (1/2) * ∑ x, Q x * |X x| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hEX (Real.exp_pos _).le
    have hc1 : |c-1| ≤ E := by
      calc
        |c-1| = |∑ x, Q x * (Real.exp (X x) - 1)| := by
          congr 1
          simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
          rw [hQ1]
        _ ≤ ∑ x, |Q x * (Real.exp (X x) - 1)| := Finset.abs_sum_le_sum_abs _ _
        _ = E := by
          apply Finset.sum_congr rfl
          intro x _
          rw [abs_mul, abs_of_nonneg (hQ x)]
    have hnum : (∑ x, Q x * |Real.exp (X x) - c|) ≤ E + |c-1| := by
      calc
        _ ≤ ∑ x, Q x * (|Real.exp (X x)-1| + |1-c|) :=
          Finset.sum_le_sum (fun x _ =>
            mul_le_mul_of_nonneg_left (abs_sub_le (Real.exp (X x)) 1 c) (hQ x))
        _ = E + |c-1| := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hQ1, one_mul]
          rw [abs_sub_comm 1 c]
    have hTV : (1/2 : ℝ) * ∑ x, |Q x * Real.exp (X x) / c - Q x| =
        (1/(2*c)) * ∑ x, Q x * |Real.exp (X x) - c| := by
      have hi (x : Fin d → Bool) : |Q x * Real.exp (X x) / c - Q x| =
          (1/c) * (Q x * |Real.exp (X x)-c|) := by
        have heq : Q x * Real.exp (X x) / c - Q x = (Q x/c)*(Real.exp (X x)-c) := by
          field_simp [hc.ne']
        rw [heq, abs_mul, abs_of_nonneg (div_nonneg (hQ x) hc.le)]
        ring
      simp_rw [hi]
      rw [← Finset.mul_sum]
      ring
    have hinv : 1/c ≤ Real.exp D := by
      calc
        _ ≤ 1/Real.exp (-D) := one_div_le_one_div_of_le (Real.exp_pos _) hclower
        _ = _ := by simp only [Real.exp_neg, one_div, inv_inv]
    rw [hTV]
    calc
      _ ≤ (1/(2*c))*(E+|c-1|) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
      _ ≤ (1/(2*c))*(2*E) := by gcongr; linarith
      _ = (1/c)*E := by ring
      _ ≤ Real.exp D * (Real.exp (1/2)*D) :=
        mul_le_mul hinv hE hE0 (Real.exp_pos _).le
      _ = Real.exp (D+1/2)*D := by rw [← mul_assoc, ← Real.exp_add]
      _ ≤ Real.exp 1 * D :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hD0
  have hquant : (1/2 : ℝ)*∑ x, |R x-Q x| ≤
      5*(Real.sqrt d/M+(d : ℝ)*(d-1)/(M : ℝ)^2) := by
    simp_rw [hdensity]
    exact hnormalized.trans hconstants.2.2
  have hone : (1/2 : ℝ)*∑ x, |R x-Q x| ≤ 1 := by
    have hsum : (∑ x, |R x-Q x|) ≤ 2 := by
      calc
        _ ≤ ∑ x, (R x+Q x) := by
          apply Finset.sum_le_sum
          intro x _
          calc
            |R x-Q x| ≤ |R x|+|Q x| := abs_sub _ _
            _ = _ := by rw [abs_of_nonneg (hR x), abs_of_nonneg (hQ x)]
        _ = 2 := by rw [Finset.sum_add_distrib, hR1, hQ1]; norm_num
    linarith
  exact le_min hone hquant

#print axioms parity_finite_tv

end D5.S3.TotalVariation.ParityFiniteTV
