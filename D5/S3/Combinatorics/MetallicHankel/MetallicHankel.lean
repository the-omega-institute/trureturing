/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankel
   mirror-E: none(waiver:external-metallic-hankel-conjecture)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Integral metallic tails give the first extra Hankel shift's period and bounds. -/

import Mathlib.Algebra.Ring.GeomSum
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelTransitions
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelPeriod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankel

open PowerSeries Finset MetallicHankelDefs MetallicHankelData
open MetallicHankelTransitions MetallicHankelTransfer MetallicHankelPeriod

set_option maxHeartbeats 2000000 in
/-- Conjecture E(1) of Han and Pedon, uniformly for every `n ≥ 2`. -/
theorem result : MetallicHankelDefs.claim := by
  classical
  intro n hn
  obtain ⟨length_eq, valid_cycle, chain, weight, word, denominator⟩ := cycle_data n hn
  let L := (cycle n).length
  let P := 2 * n * (n + 1)
  have Lpos : 0 < L := by dsimp [L]; rw [length_eq]; omega
  let state : ℕ → TailState := Nat.rec .v₂ (fun _ a => nextState n a)
  have state_zero : state 0 = .v₂ := rfl
  have state_step (p : ℕ) : state (p + 1) = nextState n (state p) := rfl
  have state_segment : ∀ p, p ≤ L → state p = (cycle n ++ [TailState.v₂]).getD p .v₂ := by
    intro p
    induction p with
    | zero => simp [state, cycle]
    | succ p ih =>
      intro hp
      have hlt : p < (cycle n ++ [TailState.v₂]).length := by simp [L] at *; omega
      have hlt' : p + 1 < (cycle n ++ [TailState.v₂]).length := by simp [L] at *; omega
      have hc := chain.getElem p hlt'
      rw [List.getElem_eq_getD TailState.v₂, List.getElem_eq_getD TailState.v₂] at hc
      rw [state_step, ih (by omega)]
      exact hc
  have state_end : state L = .v₂ := by
    rw [state_segment L (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by exact le_rfl)]
    simp [L]
  have state_period : ∀ p, state (p + L) = state p := by
    intro p
    induction p with
    | zero => simpa [state_zero] using state_end
    | succ p ih =>
      rw [show p + 1 + L = (p + L) + 1 by omega, state_step, state_step, ih]
  have state_at (i : ℕ) (hi : i < L) : state i = (cycle n)[i]'hi := by
    rw [state_segment i (by omega), ← List.getElem_eq_getD TailState.v₂]
    · exact List.getElem_append_left hi
    · simp only [List.length_append, List.length_singleton]
      exact Nat.lt_add_right 1 hi
  have state_mod : ∀ p, state p = state (p % L) := by
    intro p
    induction p using Nat.strong_induction_on with
    | h p ih =>
      by_cases hp : p < L
      · rw [Nat.mod_eq_of_lt hp]
      · have hl : L ≤ p := by omega
        rw [← Nat.sub_add_cancel hl, state_period]
        rw [ih (p - L) (by omega), Nat.sub_add_cancel hl, ← Nat.mod_eq_sub_mod hl]
  have valid (p : ℕ) : validState n (state p) := by
    rw [state_mod, state_at _ (Nat.mod_lt p Lpos)]
    exact valid_cycle _ (List.getElem_mem _)
  let k (p : ℕ) := (fractionData n (state p)).1
  let b (p : ℕ) := (fractionData n (state p)).2.1
  let v (p : ℕ) : ℤ := if p = 0 then 1 else b p
  let D (p : ℕ) := (fractionData n (state p)).2.2
  let s (p : ℕ) := ∑ i ∈ range p, (k i + 1)
  let h (p : ℕ) : ℤ := -∏ i ∈ range (p + 1), b i
  let numerator (p : ℕ) := C (v (p + 1)) * X ^ (k p + k (p + 1) + 2)
  let qpair : ℕ → PowerSeries ℤ × PowerSeries ℤ :=
    Nat.rec (1, D 0) (fun p z => (z.2, D (p + 1) * z.2 - numerator p * z.1))
  let npair : ℕ → PowerSeries ℤ × PowerSeries ℤ :=
    Nat.rec (0, C (v 0) * X ^ k 0)
      (fun p z => (z.2, D (p + 1) * z.2 - numerator p * z.1))
  let Q (p : ℕ) := (qpair p).1
  let N (p : ℕ) := (npair p).1
  have s_zero : s 0 = 0 := by simp [s]
  have s_step (p : ℕ) : s (p + 1) = s p + k p + 1 := by
    change (∑ i ∈ range (p + 1), (k i + 1)) = _
    rw [sum_range_succ]
    exact Nat.add_assoc _ _ _ |>.symm
  have h_zero : h 0 = v 0 := by simp [h, v, b, state, fractionData]
  have h_step (p : ℕ) : h (p + 1) = h p * v (p + 1) := by
    simp [h, v, prod_range_succ, neg_mul]
  have q_zero : Q 0 = 1 := rfl
  have q_one : Q 1 = D 0 := rfl
  have n_zero : N 0 = 0 := rfl
  have n_one : N 1 = C (v 0) * X ^ k 0 := rfl
  have q_step (p : ℕ) : Q (p + 2) = D (p + 1) * Q (p + 1) - numerator p * Q p := rfl
  have n_step (p : ℕ) : N (p + 2) = D (p + 1) * N (p + 1) - numerator p * N p := rfl
  obtain ⟨F, equation, degrees, error⟩ := metallic_approximation n hn state state_zero
    state_step k s v h D Q N (fun _ => ⟨rfl, rfl, rfl⟩) s_zero s_step h_zero h_step
    q_zero q_one n_zero n_one q_step n_step
  let I := invOfUnit (1 - X : PowerSeries ℤ) 1
  let S : PowerSeries ℤ := ∑ i ∈ range n, X ^ i
  let Φ := S + X ^ (n + 1) * F 0
  have hI : (1 - X : PowerSeries ℤ) * I = 1 := by simp [I]
  have hS : S * (1 - X) = 1 - X ^ n := geom_sum_mul_neg X n
  have hs : S = (1 - X ^ n) * I := by
    calc
      S = S * ((1 - X) * I) := by rw [hI, mul_one]
      _ = (S * (1 - X)) * I := by ring
      _ = (1 - X ^ n) * I := by rw [hS]
  have hn0 : n ≠ 0 := by omega
  have sconstant : constantCoeff S = 1 := by simp [hs, I, hn0]
  have hb : linearCoeff n = (1 + X ^ n) * (1 - X) - X * S := rfl
  have hsquare : X * S ^ 2 + linearCoeff n * S - 1 = -X ^ (2 * n) := by
    rw [hb]
    calc
      X * S ^ 2 + ((1 + X ^ n) * (1 - X) - X * S) * S - 1 =
          (1 + X ^ n) * (S * (1 - X)) - 1 := by ring
      _ = -X ^ (2 * n) := by rw [hS, two_mul, pow_add]; ring
  have metallic : IsMetallic n Φ := by
    refine ⟨by simp [Φ, sconstant], ?_⟩
    have he : X ^ (n + 2) * F 0 ^ 2 +
        (X * S + (1 + X ^ n) * (1 - X)) * F 0 - X ^ (n - 1) = 0 := by
      rw [hs]
      exact sub_eq_zero.mpr (by simpa only [quadraticData, I, mul_assoc] using equation)
    have hp : n + 1 + (n - 1) = 2 * n := by omega
    have htail : X * Φ ^ 2 + linearCoeff n * Φ - 1 =
        X ^ (n + 1) *
          (X ^ (n + 2) * F 0 ^ 2 + (X * S + (1 + X ^ n) * (1 - X)) * F 0 -
            X ^ (n - 1)) := by
      dsimp [Φ]
      rw [hb] at hsquare ⊢
      rw [← sub_eq_zero] at hsquare
      rw [pow_add, show n + 2 = (n + 1) + 1 by omega, pow_add, pow_one]
      have hpn : (X : PowerSeries ℤ) ^ (n + 1) * X ^ (n - 1) = X ^ (2 * n) := by
        rw [← pow_add, hp]
      linear_combination hsquare + hpn
    exact sub_eq_zero.mp (by rw [htail, he, mul_zero])
  have shifted (r : ℕ) : coeff (n + 1 + r) Φ = coeff r (F 0) := by
    dsimp [Φ]
    rw [map_add, coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel_left]
    have hz : coeff (n + 1 + r) S = 0 := by
      dsimp [S]
      rw [map_sum]
      apply sum_eq_zero
      intro i hi
      rw [coeff_X_pow, if_neg]
      simp only [mem_range] at hi
      omega
    rw [hz, zero_add]
  have unique (Ψ : PowerSeries ℤ) (hΨ : IsMetallic n Ψ) : Ψ = Φ := by
    have hu : IsUnit (linearCoeff n + X * (Ψ + Φ)) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp [linearCoeff, hn0]
    apply hu.mul_left_injective
    linear_combination hΨ.2 - metallic.2
  have k_period (p : ℕ) : k (p + L) = k p := by simp [k, L, state_period]
  have b_period (p : ℕ) : b (p + L) = b p := by simp [b, L, state_period]
  have sum_rotate (f : ℕ → ℕ) (hf : ∀ p, f (p + L) = f p) (p : ℕ) :
      (∑ i ∈ range L, f (p + i)) = ∑ i ∈ range L, f i := by
    obtain ⟨m, hm⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    induction p with
    | zero => simp
    | succ p ih =>
      have hlast : f (p + 1 + m) = f p := by
        rw [show p + 1 + m = p + L by omega, hf]
      calc
        _ = (∑ i ∈ range m, f (p + 1 + i)) + f p := by
          rw [hm, sum_range_succ, hlast]
        _ = (∑ i ∈ range m, f (p + (i + 1))) + f p := by
          congr 1
          apply sum_congr rfl
          intro i hi
          congr 1
          omega
        _ = ∑ i ∈ range L, f (p + i) := by
          rw [hm, sum_range_succ']
          simp
        _ = _ := ih
  have prod_rotate (f : ℕ → ℤ) (hf : ∀ p, f (p + L) = f p) (p : ℕ) :
      (∏ i ∈ range L, f (p + i)) = ∏ i ∈ range L, f i := by
    obtain ⟨m, hm⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    induction p with
    | zero => simp
    | succ p ih =>
      have hlast : f (p + 1 + m) = f p := by
        rw [show p + 1 + m = p + L by omega, hf]
      calc
        _ = (∏ i ∈ range m, f (p + 1 + i)) * f p := by
          rw [hm, prod_range_succ, hlast]
        _ = (∏ i ∈ range m, f (p + (i + 1))) * f p := by
          congr 1
          apply prod_congr rfl
          intro i hi
          congr 1
          omega
        _ = ∏ i ∈ range L, f (p + i) := by
          rw [hm, prod_range_succ']
          simp
        _ = _ := ih
  have weight0 : (∑ i ∈ range L, (k i + 1)) = P := by
    have hlist : List.ofFn (fun i : Fin L => k i + 1) =
        (cycle n).map (fun a => (fractionData n a).1 + 1) := by
      rw [← List.ofFn_getElem (xs := cycle n), List.map_ofFn]
      congr 1
      funext i
      dsimp [k]
      rw [state_at i i.isLt]
    rw [← Fin.sum_univ_eq_sum_range, ← List.sum_ofFn, hlist]
    exact weight
  have bprod0 : (∏ i ∈ range L, b i) = 1 := by
    have hlist : List.ofFn (fun i : Fin L => b i) =
        (cycle n).map (fun a => (fractionData n a).2.1) := by
      rw [← List.ofFn_getElem (xs := cycle n), List.map_ofFn]
      congr 1
      funext i
      dsimp [b]
      rw [state_at i i.isLt]
    rw [← Fin.prod_univ_eq_prod_range, ← List.prod_ofFn, hlist]
    exact (cycle_sign n hn).1
  have s_period (p : ℕ) : s (p + L) = s p + P := by
    simp only [s, sum_range_add]
    rw [sum_rotate (fun i => k i + 1) (by intro i; rw [k_period]), weight0]
  have h_period (p : ℕ) : h (p + L) = h p := by
    dsimp [h]
    rw [show p + L + 1 = (p + 1) + L by omega, prod_range_add,
      prod_rotate b b_period, bprod0, mul_one]
  have bsquare (p : ℕ) : b p ^ 2 = 1 := by
    dsimp [b]
    cases state p <;> norm_num [fractionData]
  have h_square (p : ℕ) : h p ^ 2 = 1 := by
    induction p with
    | zero =>
      simpa [h] using bsquare 0
    | succ p ih =>
      dsimp [h] at ih ⊢
      rw [prod_range_succ, ← neg_mul, mul_pow, ih, bsquare (p + 1), one_mul]
  have hsign (p : ℕ) : h p ∈ ({-1, 1} : Finset ℤ) := by
    have hh : (h p + 1) * (h p - 1) = 0 := by nlinarith [h_square p]
    simp only [mem_insert, mem_singleton]
    rcases mul_eq_zero.mp hh with he | he
    · left; omega
    · right; omega
  let r (p : ℕ) : ℤ :=
    (-1) ^ (k p * (k p + 1) / 2) * h p ^ (k p + 1)
  have r_period (p : ℕ) : r (p + L) = r p := by
    simp only [r, k_period, h_period]
  have rprod0 : (∏ i ∈ range L, r i) = (-1) ^ n := by
    have index (i : ℕ) (hi : i < L) : state i = (cycle n).getD i .v₂ := by
      rw [List.getD_eq_getElem (cycle n) .v₂ hi]
      exact state_at i hi
    have compare (i : ℕ) (hi : i < L) :
        r i =
          let a := (cycle n).getD i .v₂
          let ki := (fractionData n a).1
          let hp := -(∏ j ∈ range (i + 1),
            (fractionData n ((cycle n).getD j .v₂)).2.1)
          (-1 : ℤ) ^ (ki * (ki + 1) / 2) * hp ^ (ki + 1) := by
      have kh : k i = (fractionData n ((cycle n).getD i .v₂)).1 := by
        dsimp [k]
        rw [index i hi]
      have hh : h i = -(∏ j ∈ range (i + 1),
          (fractionData n ((cycle n).getD j .v₂)).2.1) := by
        dsimp [h]
        congr 1
        apply prod_congr rfl
        intro j hj
        dsimp [b]
        rw [index j (by simp only [mem_range] at hj; omega)]
      simp only [r, kh, hh]
    calc
      _ = _ := prod_congr rfl (fun i hi => compare i (mem_range.mp hi))
      _ = _ := (cycle_sign n hn).2
  have multiplier (p : ℕ) : (∏ i ∈ range L,
      (-1 : ℤ) ^ (k (p + i) * (k (p + i) + 1) / 2) *
        h (p + i) ^ (k (p + i) + 1)) = (-1) ^ n :=
    (prod_rotate r r_period p).trans rprod0
  let c (p r : ℕ) : ℤ := coeff (s p - r) (Q p)
  have moments (p : ℕ) : c p (s p) = 1 ∧
      (∀ t, t < s p + k p →
        ∑ r ∈ range (s p + 1), c p r * coeff (n + 1 + r + t) Φ = 0) ∧
      (∑ r ∈ range (s p + 1),
        c p r * coeff (n + 1 + r + (s p + k p)) Φ) = h p := by
    obtain ⟨R, he, hr⟩ := error p
    have convolution (t : ℕ) :
        (∑ r ∈ range (s p + 1), c p r * coeff (n + 1 + r + t) Φ) =
          coeff (s p + t) (Q p * F 0) := by
      simp only [show ∀ r, n + 1 + r + t = n + 1 + (r + t) by intro r; omega,
        shifted, c]
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have truncate :
          (∑ i ∈ range (s p + t + 1), coeff i (Q p) * coeff (s p + t - i) (F 0)) =
            ∑ i ∈ range (s p + 1), coeff i (Q p) * coeff (s p + t - i) (F 0) := by
        symm
        apply Finset.sum_subset (range_mono (by omega))
        intro i hi hnot
        have hi' : s p < i := by simp only [mem_range] at hnot; omega
        simp [(degrees p).2.1 i hi']
      rw [truncate, ← sum_range_reflect
        (fun i => coeff i (Q p) * coeff (s p + t - i) (F 0)) (s p + 1)]
      apply sum_congr rfl
      intro r hr
      have hr' : r ≤ s p := by simp only [mem_range] at hr; omega
      rw [show s p + 1 - 1 - r = s p - r by omega,
        show s p + t - (s p - r) = r + t by omega]
    refine ⟨by simpa [c] using (degrees p).1, ?_, ?_⟩
    · intro t ht
      rw [convolution]
      have ht' := congrArg (coeff (s p + t)) he
      rw [map_sub, (degrees p).2.2 _ (by omega), sub_zero, coeff_X_pow_mul',
        if_neg (by omega)] at ht'
      exact ht'
    · rw [convolution]
      have ht' := congrArg (coeff (s p + (s p + k p))) he
      rw [map_sub, (degrees p).2.2 _ (by omega), sub_zero, coeff_X_pow_mul',
        if_pos (by omega), show s p + (s p + k p) - (2 * s p + k p) = 0 by omega,
        coeff_zero_eq_constantCoeff, hr] at ht'
      exact ht'
  let t (p : ℕ) : ℤ := coeff (s p) (Q p)
  let d (p : ℕ) : ℤ := coeff (k p + 1) (D p)
  have top (U V : PowerSeries ℤ) (a b : ℕ)
      (hU : ∀ i, a < i → coeff i U = 0)
      (hV : ∀ i, b < i → coeff i V = 0) :
      coeff (a+b) (U*V) = coeff a U * coeff b V := by
    rw [coeff_mul]
    apply sum_eq_single (a,b)
    · intro x hx hne
      have he := mem_antidiagonal.mp hx
      by_cases hd : a < x.1
      · simp [hU x.1 hd]
      · have hfst : x.1 ≠ a := by
          intro eq
          apply hne
          have hsec : x.2 = b := by omega
          exact Prod.ext eq hsec
        simp [hV x.2 (by omega)]
    · simp
  have t0 : t 0 = 1 := by simp [t, q_zero, s_zero]
  have t1 : t 1 = d 0 := by
    simp only [t, q_one, s_step, s_zero, zero_add, d]
  have t_step (p : ℕ) : t (p+2) = d (p+1)*t (p+1)-v (p+1)*t p := by
    have hs1 := s_step p
    have hs2 : s (p+2) = s (p+1)+k (p+1)+1 := by
      simpa only [Nat.add_assoc] using s_step (p+1)
    have htop : coeff (s (p+2)) (D (p+1)*Q (p+1)) = d (p+1)*t (p+1) := by
      have he : s (p+2) = (k (p+1)+1)+s (p+1) := by omega
      rw [he]
      exact top _ _ _ _ (denominator _ (valid (p+1))).2 (degrees (p+1)).2.1
    have hlow : coeff (s (p+2)) (numerator p*Q p) = v (p+1)*t p := by
      have he : s (p+2) = (k p+k (p+1)+2)+s p := by omega
      dsimp only [numerator]
      rw [mul_assoc, coeff_C_mul, he,
        Nat.add_comm (k p+k (p+1)+2) (s p), coeff_X_pow_mul]
    dsimp only [t]
    rw [q_step, map_sub, htop, hlow]
  have wordlen : (topWord n).length = L := by
    rw [← word, List.length_map]
  have lookup (p : ℕ) : (topWord n)[p % (topWord n).length]! = (d p,b p) := by
    rw [wordlen, ← word]
    have hi : p % L < (cycle n).length := Nat.mod_lt p Lpos
    rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
    rw [← state_at _ hi, ← state_mod]
  let pair (p : ℕ) : ℤ×ℤ := (t p,if p=0 then 0 else t (p-1))
  have pair0 : pair 0 = (1,0) := by simp [pair,t0]
  have pair_step (p : ℕ) : pair (p+1) =
      let a := (topWord n)[p % (topWord n).length]!
      (a.1*(pair p).1-a.2*(pair p).2,(pair p).1) := by
    rw [lookup]
    dsimp only
    cases p with
    | zero => simp [pair,t1,t0]
    | succ p =>
      have ht := t_step p
      simp only [v,show p+1≠0 by omega,if_neg,if_false,Nat.add_sub_cancel] at ht
      simpa only [pair,show p+1≠0 by omega,show p+1+1≠0 by omega,
        if_neg,if_false,Nat.add_sub_cancel,Nat.add_assoc,
        show p+(1+1)-1=p+1 by omega] using congrArg (fun x => (x,t (p+1))) ht
  have hb := block_transfer n hn pair pair0 pair_step
  have c_period (p : ℕ) : c (p + L) 0 = c p 0 := by
    have he := congrArg Prod.fst (hb p).1
    simpa only [pair, wordlen, c, Nat.sub_zero, t] using he
  have cvalues (p : ℕ) : c p 0 ∈ ({-1, 0, 1, 2} : Finset ℤ) := by
    simpa only [pair, c, Nat.sub_zero, t] using (hb p).2.1
  have peven : Even P := by
    refine ⟨n * (n + 1), ?_⟩
    dsimp [P]
    ring
  have conclusion := propagate Φ (n + 1) n L P s k c h s_zero s_step
    s_period k_period h_period c_period peven hsign cvalues
    (fun p => (moments p).1)
    (fun p t ht => (moments p).2.1 t (by rw [s_step] at ht; omega))
    (fun p => by simpa only [s_step, Nat.add_sub_cancel] using (moments p).2.2)
    multiplier
  refine ⟨⟨Φ, metallic⟩, ?_⟩
  intro Ψ hΨ
  rw [unique Ψ hΨ]
  simpa only [P, show n + 1 + 1 = n + 2 by omega] using conclusion

end D5.S3.Combinatorics.MetallicHankel.MetallicHankel
