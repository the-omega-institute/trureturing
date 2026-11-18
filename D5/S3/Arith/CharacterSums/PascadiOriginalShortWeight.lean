/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalShortWeight
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalShortWeight
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Short actual prime-square lattices have the smaller weighted incidence cost. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalWeightAverage
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem short_weight_dyadic_sum {T : ℝ} {N : ℕ}
    (hN : (2 : ℝ)^N ≤ T) :
    (∑ k ∈ Finset.range (N+1), (2 : ℝ)^k) ≤ 2*T := by
  have hid (n : ℕ) : (∑ k ∈ Finset.range (n+1), (2 : ℝ)^k) = 2^(n+1)-1 := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [hid, pow_succ]
  linarith

/-- If every actual prime-square lattice has a shortest vector of length at
most H/p, the unit-parameter weight has cost A/p+A²/p⁴ rather than A. -/
theorem actual_short_physical_weight_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y H : ℝ),
      0 < X → 0 < Y → X ≤ Y → Y < (p : ℝ)^3 → X*Y < 2*(p : ℝ)^4 →
      0 < H → H^2 = X*Y → (p : ℝ) ≤ H →
      ∀ (s : Finset Coordinate) (U : Coordinate → Coordinate),
      (∀ wt ∈ s, wt ∈ literalBox X Y) →
      (∀ wt ∈ s, IsUnit (wt.2 : ZMod (p^2)) ∧ IsUnit (wt.1 : ZMod (p^2))) →
      (∀ wt ∈ s, ∃ B : ReducedMiddleBasis (p^2) wt.2 wt.1 X Y, U wt = B.R) →
      (∀ wt ∈ s, weightedSq X Y (U wt) ≤ X*Y/(p : ℝ)^2) →
      (∑ wt ∈ s, (1+H/((p : ℝ)*Real.sqrt (weightedSq X Y (U wt))))) ≤
        C*(p : ℝ)^ε*(X*Y/p+(X*Y)^2/(p : ℝ)^4) := by
  let L : ℝ := 2+1/(ε*Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 1 ≤ L := by
    have hh : 0 ≤ 1/(ε*Real.log 2) := by positivity
    dsimp [L]
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  refine ⟨2048*L, by positivity, ?_⟩
  intro p hp X Y H hX hY hXY hYcut hAcut hH hHsq hHp s U hbox hunit hbasis hshort
  classical
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  let T := H/(p : ℝ)
  let Q := fun wt => weightedSq X Y (U wt)
  let W := fun wt => 1+H/((p : ℝ)*Real.sqrt (Q wt))
  have hT : 0 < T := by dsimp [T]; positivity
  have hT1 : 1 ≤ T := (le_div_iff₀ hpR).mpr (by simpa only [one_mul] using hHp)
  have hTsq : T^2 = X*Y/(p : ℝ)^2 := by dsimp [T]; rw [div_pow, hHsq]
  have hTcut : T < 2*p := by
    have hs : T^2 < 2*(p : ℝ)^2 := by
      rw [hTsq]
      apply (div_lt_iff₀ (sq_pos_of_pos hpR)).mpr
      nlinarith [hAcut]
    nlinarith [sq_nonneg (T-2*p)]
  obtain ⟨N, hNlow, hNhigh⟩ := exists_nat_pow_near hT1 (by norm_num : (1 : ℝ) < 2)
  let P := fun k wt => ((2 : ℝ)^k)^2 ≤ Q wt ∧ Q wt < 4*((2 : ℝ)^k)^2
  have hW (wt : Coordinate) : 0 ≤ W wt := by dsimp [W]; positivity
  have hlower (wt : Coordinate) (hw : wt ∈ s) : 1 ≤ Real.sqrt (Q wt) := by
    obtain ⟨B, hB⟩ := hbasis wt hw
    have hu := short_middle_vector_unit_coordinates hp hX hY hXY hYcut hAcut
      (hunit wt hw).1 (hunit wt hw).2 (U wt)
      (by rw [hB]; exact B.memR)
      (by rw [hB]; exact B.first_ne_zero (pow_pos hp.pos _)) (hshort wt hw)
    have ha (z : ℤ) (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
      exact_mod_cast Int.one_le_abs hz
    have hprod : 1 ≤ |((U wt).1 : ℝ)| * |((U wt).2 : ℝ)| :=
      one_le_mul_of_one_le_of_one_le (ha _ hu.1) (ha _ hu.2.1)
    apply Real.le_sqrt_of_sq_le
    have hh := two_abs_product_le_weightedSq hX hY (U wt)
    dsimp [Q]
    nlinarith
  have hcover (wt : Coordinate) (hw : wt ∈ s) :
      W wt ≤ ∑ k ∈ Finset.range (N+1), if P k wt then W wt else 0 := by
    obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near (hlower wt hw)
      (by norm_num : (1 : ℝ) < 2)
    have hlen : Real.sqrt (Q wt) ≤ T := (Real.sqrt_le_iff).mpr
      ⟨hT.le, by rw [hTsq]; exact hshort wt hw⟩
    have hk : k < N+1 := by
      have hh : (2 : ℝ)^k < 2^(N+1) := hklo.trans_lt (hlen.trans_lt hNhigh)
      exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hh
    have hPk : P k wt := by
      have hsq := Real.sq_sqrt (weightedSq_nonneg hX hY (U wt))
      have hlo := (sq_le_sq₀ (by positivity : 0 ≤ (2 : ℝ)^k)
        (Real.sqrt_nonneg (Q wt))).mpr hklo
      have hhi := (sq_lt_sq₀ (Real.sqrt_nonneg (Q wt))
        (by positivity : 0 ≤ (2 : ℝ)^(k+1))).mpr hkhi
      have hpow_succ : (2 : ℝ)^(k+1) = 2^k*2 := pow_succ _ _
      rw [hpow_succ] at hhi
      exact ⟨by dsimp [Q] at *; nlinarith, by dsimp [Q] at *; nlinarith⟩
    have hh := Finset.single_le_sum (f := fun j => if P j wt then W wt else 0)
      (fun _ _ => by split <;> positivity) (Finset.mem_range.mpr hk)
    simpa only [if_pos hPk] using hh
  have hs (k : ℕ) (hk : k ∈ Finset.range (N+1)) :
      (∑ wt ∈ s.filter (P k), W wt) ≤
        512*T*((2 : ℝ)^k+H+(X*Y/(p : ℝ)^2)*(2 : ℝ)^k) := by
    apply actual_shortest_vector_scale_weight hp hX hY hXY hYcut hAcut hH hHsq
      (by positivity : 0 < (2 : ℝ)^k)
      ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).trans hNlow)
      (s.filter (P k))
      (fun wt hw => hbox wt (Finset.mem_filter.mp hw).1)
      (fun wt hw => hunit wt (Finset.mem_filter.mp hw).1) U
      (fun wt hw => hbasis wt (Finset.mem_filter.mp hw).1)
      (fun _ hw => (Finset.mem_filter.mp hw).2.1)
      (fun _ hw => (Finset.mem_filter.mp hw).2.2.le)
      (fun wt hw => hshort wt (Finset.mem_filter.mp hw).1)
  have hsplit : (∑ wt ∈ s, W wt) ≤
      ∑ k ∈ Finset.range (N+1), ∑ wt ∈ s.filter (P k), W wt := by
    calc
      _ ≤ ∑ wt ∈ s, ∑ k ∈ Finset.range (N+1),
          if P k wt then W wt else 0 := Finset.sum_le_sum hcover
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.sum_filter]
  have hgeom := short_weight_dyadic_sum hNlow
  have hsum : (∑ wt ∈ s, W wt) ≤
      512*T*(2*T+((N+1 : ℕ) : ℝ)*H+(X*Y/(p : ℝ)^2)*(2*T)) := by
    apply hsplit.trans
    calc
      _ ≤ ∑ k ∈ Finset.range (N+1),
          512*T*((2 : ℝ)^k+H+(X*Y/(p : ℝ)^2)*(2 : ℝ)^k) := Finset.sum_le_sum hs
      _ = 512*T*((∑ k ∈ Finset.range (N+1), (2 : ℝ)^k)+
          ((N+1 : ℕ) : ℝ)*H+(X*Y/(p : ℝ)^2)*
          (∑ k ∈ Finset.range (N+1), (2 : ℝ)^k)) := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by gcongr
  have hNlog : ((N+1 : ℕ) : ℝ) ≤ 2+Real.log p/Real.log 2 := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < 2^N)
      (hNlow.trans hTcut.le)
    rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpR.ne'] at hh
    have hd := (le_div_iff₀ hlog2).mpr hh
    have he : (Real.log 2+Real.log p)/Real.log 2 = 1+Real.log p/Real.log 2 := by
      rw [add_div, div_self hlog2.ne']
    rw [he] at hd
    push_cast
    linarith
  have hpow : 1 ≤ (p : ℝ)^ε := Real.one_le_rpow hp1 hε.le
  have hN : ((N+1 : ℕ) : ℝ) ≤ L*(p : ℝ)^ε := by
    have hh := Real.log_le_rpow_div hpR.le hε
    have hd := div_le_div_of_nonneg_right hh hlog2.le
    have he : (p : ℝ)^ε/ε/Real.log 2 = (1/(ε*Real.log 2))*(p : ℝ)^ε := by
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    rw [he] at hd
    dsimp [L]
    nlinarith
  have halg : 512*T*(2*T+((N+1 : ℕ) : ℝ)*H+(X*Y/(p : ℝ)^2)*(2*T)) =
      1024*(X*Y)/(p : ℝ)^2+512*(X*Y/p)*((N+1 : ℕ) : ℝ)+
        1024*(X*Y)^2/(p : ℝ)^4 := by
    dsimp [T]
    calc
      _ = 1024*H^2/(p : ℝ)^2+512*(H^2/p)*((N+1 : ℕ) : ℝ)+
          1024*(H^2*(X*Y))/(p : ℝ)^4 := by field_simp; ring
      _ = _ := by rw [hHsq]; ring
  rw [halg] at hsum
  have hLP : 1 ≤ L*(p : ℝ)^ε := one_le_mul_of_one_le_of_one_le hL hpow
  have hsmall : X*Y/(p : ℝ)^2 ≤ X*Y/p :=
    div_le_div_of_nonneg_left (by positivity) hpR (by nlinarith)
  have hfirst := mul_le_mul_of_nonneg_left
    (hsmall.trans (le_mul_of_one_le_right (by positivity) hLP))
    (by norm_num : (0 : ℝ) ≤ 1024)
  have hsecond := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ 512*(X*Y/p))
  have hthird := le_mul_of_one_le_right
    (show 0 ≤ 1024*(X*Y)^2/(p : ℝ)^4 by positivity) hLP
  have hslack : 0 ≤ (512*(X*Y/p)+1024*((X*Y)^2/(p : ℝ)^4))*(L*(p : ℝ)^ε) := by
    positivity
  change (∑ wt ∈ s, W wt) ≤ _
  simp only [mul_div_assoc] at hsum hfirst hsecond hthird hslack ⊢
  nlinarith only [hsum, hfirst, hsecond, hthird, hslack]

end
end D5.S3.Arith.CharacterSums.Original
