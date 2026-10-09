/- GID: D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every larger atom in an optimal real law terminates at its least dyadic strict rounding depth. -/

import D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange
import D5.S1.Digit.RadixFloorDigit

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding

open D5.S3.Arith.FibonacciAtomic
open D5.S3.Arith.FibonacciAtomic.DyadicSupportLines
open D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope

/-- A coordinate is dyadic with the displayed least terminating depth. -/
def DyadicTerminalAbove (x t : ℝ) : Prop :=
  ∃ D : ℕ, 1 ≤ D ∧
    (∃ z : ℤ, (2 : ℝ) ^ D * x = z) ∧
    (∀ d : ℕ, d < D → ¬∃ z : ℤ, (2 : ℝ) ^ d * x = z) ∧
    x = (((⌊(2 : ℝ) ^ D * t⌋ : ℤ) + 1 : ℤ) : ℝ) / (2 : ℝ) ^ D

/-- Exact Lean target corresponding to the source's strict-rounding conclusion. -/
def StrictRoundingTarget (m : ℕ) (p : Fin m → ℝ) (k : Fin m) : Prop :=
  ∀ i : Fin m, p k < p i → DyadicTerminalAbove (p i) (p k)

/-- The full public proposition, with the frozen optimizer hypotheses explicit. -/

private lemma alpha_lt (n m : ℕ) (hn : 1 ≤ n) (h : n < m) : alpha n < alpha m := by
  have step (r : ℕ) : alpha (r + 1) < alpha (r + 2) := by
    by_cases hr : r = 0
    · subst r
      norm_num [OptimalLawStrictSlope.result.1, OptimalLawStrictSlope.result.2.1]
    · have H := OptimalLawStrictSlope.result.2.2 (r + 2) (by omega)
      simpa using H
  have H : StrictMono (fun r : ℕ => alpha (r + 1)) :=
    strictMono_nat_of_lt_succ (fun r => by simpa [Nat.add_assoc] using step r)
  have H' := H (show n - 1 < m - 1 by omega)
  simpa [Nat.sub_add_cancel hn, Nat.sub_add_cancel (show 1 ≤ m by omega)] using H'

private lemma receiver_law (m : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty) :
    ∃ (q : Fin m → ℝ) (u : ℝ), 0 < u ∧
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i) = 1 ∧
      (∀ i ∈ S, u ≤ q i) ∧ (∀ i, i ∉ S → q i = 0) ∧
      cost q = alpha S.card * u ∧ (S.card : ℝ) * u ≤ 1 := by
  classical
  have hn : 1 ≤ S.card := Finset.card_pos.mpr hS
  have base : ∃ (v : Fin S.card → ℝ) (k : Fin S.card),
      (∀ a, 0 < v a) ∧ (∑ a, v a) = 1 ∧ (∀ a, v k ≤ v a) ∧
      cost v = alpha S.card * v k := by
    by_cases h : S.card = 1
    · let v : Fin S.card → ℝ := fun _ => 1
      let k : Fin S.card := ⟨0, by omega⟩
      refine ⟨v, k, by simp [v], by simp [v, h], by simp [v], ?_⟩
      have hc : cost v = 0 := by
        unfold cost
        rw [show (fun d : ℕ => DyadicSupportLines.residual v d / (2 : ℝ) ^ d) = fun _ => 0 from ?_]
        · simp
        funext d
        have hf : ⌊(2 : ℝ) ^ d⌋ = (2 : ℤ) ^ d := by
          exact_mod_cast Int.floor_intCast ((2 : ℤ) ^ d)
        simp [DyadicSupportLines.residual, v, hf, h]
      rw [hc, h, OptimalLawStrictSlope.result.1, zero_mul]
    · obtain ⟨v, k, hv, hs, hk, he⟩ := attained S.card (by omega)
      exact ⟨v, k, hv, hs, hk, by
        have H := (div_eq_iff (hv k).ne').mp he
        simpa [mul_comm] using H⟩
  obtain ⟨v, k, hv, hs, hk, he⟩ := base
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  let q : Fin m → ℝ := fun i => if hi : i ∈ S then v (e ⟨i, hi⟩) else 0
  have transport (g : ℝ → ℝ) (g0 : g 0 = 0) :
      (∑ i : Fin m, g (q i)) = ∑ a : Fin S.card, g (v a) := by
    calc
      _ = ∑ i ∈ S, g (q i) := (Finset.sum_subset S.subset_univ
        (fun i _ hi => by simp [q, hi, g0])).symm
      _ = ∑ a : S, g (v (e a)) := by
        rw [← Finset.sum_coe_sort]
        apply Finset.sum_congr rfl
        intro a _
        simp [q, a.property]
      _ = _ := Equiv.sum_comp e (fun a => g (v a))
  have qs : ∑ i, q i = 1 := (transport (fun x => x) rfl).trans hs
  have qc : cost q = cost v := by
    unfold cost
    apply tsum_congr
    intro d
    congr 1
    unfold DyadicSupportLines.residual
    simp only [Int.cast_sum]
    rw [transport (fun x => (⌊(2 : ℝ) ^ d * x⌋ : ℝ)) (by simp)]
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hk i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hs] at bound
  refine ⟨q, v k, hv k, ?_, qs, ?_, ?_, qc.trans he, bound⟩
  · intro i
    dsimp [q]
    split_ifs with hi
    · exact (hv _).le
    · exact le_rfl
  · intro i hi
    simpa [q, hi] using hk (e ⟨i, hi⟩)
  · intro i hi
    simp [q, hi]

lemma bit_bounds (x : ℝ) (d : ℕ) :
    2 * ⌊(2 : ℝ) ^ d * x⌋ ≤ ⌊(2 : ℝ) ^ (d + 1) * x⌋ ∧
    ⌊(2 : ℝ) ^ (d + 1) * x⌋ ≤ 2 * ⌊(2 : ℝ) ^ d * x⌋ + 1 := by
  have low := Int.floor_le ((2 : ℝ) ^ d * x)
  have high := Int.lt_floor_add_one ((2 : ℝ) ^ d * x)
  constructor
  · apply Int.le_floor.mpr
    push_cast
    rw [pow_succ]
    nlinarith
  · have H : ⌊(2 : ℝ) ^ (d + 1) * x⌋ < 2 * ⌊(2 : ℝ) ^ d * x⌋ + 2 := by
      apply Int.floor_lt.mpr
      push_cast
      rw [pow_succ]
      nlinarith
    omega

private lemma non_dyadic_deep_leaf (x : ℝ)
    (hx : ¬∃ D : ℕ, ∃ z : ℤ, (2 : ℝ) ^ D * x = z) (N : ℕ) :
    ∃ D : ℕ, N < D ∧
      ⌊(2 : ℝ) ^ D * x⌋ = 2 * ⌊(2 : ℝ) ^ (D - 1) * x⌋ + 1 := by
  by_contra h
  have zero_bit (d : ℕ) (hd : N ≤ d) :
      ⌊(2 : ℝ) ^ (d + 1) * x⌋ = 2 * ⌊(2 : ℝ) ^ d * x⌋ := by
    have H := bit_bounds x d
    have ne : ⌊(2 : ℝ) ^ (d + 1) * x⌋ ≠ 2 * ⌊(2 : ℝ) ^ d * x⌋ + 1 := by
      intro he
      apply h
      exact ⟨d + 1, by omega, by simpa using he⟩
    omega
  have floors (n : ℕ) : ⌊(2 : ℝ) ^ (N + n) * x⌋ =
      (2 : ℤ) ^ n * ⌊(2 : ℝ) ^ N * x⌋ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show N + (n + 1) = (N + n) + 1 by omega, zero_bit _ (by omega), ih]
      ring
  have upper (n : ℕ) : (2 : ℝ) ^ N * x ≤
      (⌊(2 : ℝ) ^ N * x⌋ : ℝ) + (1 / 2 : ℝ) ^ n := by
    have H := Int.lt_floor_add_one ((2 : ℝ) ^ (N + n) * x)
    rw [floors] at H
    push_cast at H
    rw [pow_add] at H
    have hc : (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by rw [div_pow, one_pow]
    rw [hc]
    have H' : (2 : ℝ) ^ N * x - (⌊(2 : ℝ) ^ N * x⌋ : ℝ) ≤ 1 / 2 ^ n := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr
      nlinarith only [H]
    linarith only [H']
  have limit : Filter.Tendsto
      (fun n : ℕ => (⌊(2 : ℝ) ^ N * x⌋ : ℝ) + (1 / 2 : ℝ) ^ n)
      Filter.atTop (nhds (⌊(2 : ℝ) ^ N * x⌋ : ℝ)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  have equal := le_antisymm (ge_of_tendsto limit (Filter.Eventually.of_forall upper))
    (Int.floor_le ((2 : ℝ) ^ N * x))
  exact hx ⟨N, ⌊(2 : ℝ) ^ N * x⌋, equal⟩


private lemma larger_terminal (m : ℕ) (hm : 2 ≤ m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (hk : ∀ i, p k ≤ p i) (ho : cost p / p k = alpha m)
    (j : Fin m) (hj : p k < p j) :
    ∃ D : ℕ, ∃ z : ℤ, (2 : ℝ) ^ D * p j = z := by
  classical
  by_contra nonterminal
  let S := Finset.univ.filter (fun i : Fin m => p i = p k)
  have Sk : k ∈ S := by simp [S]
  have Sj : j ∉ S := by simp [S, ne_of_gt hj]
  have Sc : S.card < m := by
    have sub : S ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.filter_subset _ _, by intro eq; exact Sj (eq ▸ Finset.mem_univ j)⟩
    simpa using Finset.card_lt_card sub
  obtain ⟨q, u, up, qpos, qsum, qlow, qzero, qcost, ub⟩ := receiver_law m S ⟨k, Sk⟩
  have profit : cost q < alpha m * u := by
    rw [qcost]
    exact mul_lt_mul_of_pos_right (alpha_lt S.card m (Finset.card_pos.mpr ⟨k, Sk⟩) Sc) up
  have opt : cost p = alpha m * p k := by
    have H := (div_eq_iff (hp k).ne').mp ho
    simpa [mul_comm] using H
  have small : ∀ᶠ D : ℕ in Filter.atTop, ∀ i : Fin m, i ∉ S →
      p k + (1 / (2 : ℝ) ^ D) * (1 + u) < p i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ∈ S
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hi))
    · have gap : p k < p i := lt_of_le_of_ne (hk i) (by
        intro H
        apply hi
        simp [S, H.symm])
      have limit : Filter.Tendsto (fun D : ℕ => p k + (1 / (2 : ℝ) ^ D) * (1 + u))
          Filter.atTop (nhds (p k)) := by
        have H := (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 + u)
        simpa [div_pow, one_pow] using tendsto_const_nhds.add H
      filter_upwards [limit.eventually (Iio_mem_nhds gap)] with D h _
      exact h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp small
  obtain ⟨D, hD, bit⟩ := non_dyadic_deep_leaf (p j) nonterminal N
  apply D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange.profitable_leaf_impossible m D hm p q j (by omega)
    (fun i => (hp i).le) hs qpos qsum (qzero j Sj) S (p k) u (hp k) up
    (fun i hi => ⟨hk i, qlow i hi⟩) ?_ ?_ opt profit bit
  · intro i hi hij
    have H := hN D (by omega) i hi
    have nn : 0 ≤ 1 / (2 : ℝ) ^ D := by positivity
    nlinarith only [H, nn]
  · exact (hN D (by omega) j Sj).le


noncomputable def round (t : ℝ) (D : ℕ) : ℝ :=
  ((⌊(2 : ℝ) ^ D * t⌋ : ℝ) + 1) / (2 : ℝ) ^ D

def OnGrid (x : ℝ) (D : ℕ) : Prop := ∃ z : ℤ, (2 : ℝ) ^ D * x = z

lemma grid_up (x : ℝ) (D E : ℕ) (h : D ≤ E) (hx : OnGrid x D) : OnGrid x E := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨(2 : ℤ) ^ (E - D) * z, ?_⟩
  have he : E = (E - D) + D := by omega
  conv_lhs => rw [he, pow_add, mul_assoc, hz]
  push_cast
  rfl

private lemma round_grid (t : ℝ) (D : ℕ) : OnGrid (round t D) D := by
  refine ⟨⌊(2 : ℝ) ^ D * t⌋ + 1, ?_⟩
  dsimp [round]
  push_cast
  field_simp

private lemma round_gt (t : ℝ) (D : ℕ) : t < round t D := by
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ D)).mpr
  simpa [mul_comm] using Int.lt_floor_add_one ((2 : ℝ) ^ D * t)

private lemma round_le_grid (t x : ℝ) (D : ℕ) (h : t < x) (hx : OnGrid x D) :
    round t D ≤ x := by
  obtain ⟨z, hz⟩ := hx
  have hI : ⌊(2 : ℝ) ^ D * t⌋ < z := by
    apply Int.floor_lt.mpr
    rw [← hz]
    exact mul_lt_mul_of_pos_left h (by positivity)
  have hR : (⌊(2 : ℝ) ^ D * t⌋ : ℝ) + 1 ≤ (z : ℝ) := by
    exact_mod_cast (show ⌊(2 : ℝ) ^ D * t⌋ + 1 ≤ z by omega)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ D)).mpr
  simpa [mul_comm, ← hz] using hR

private lemma round_antitone (t : ℝ) (D E : ℕ) (h : D ≤ E) : round t E ≤ round t D :=
  round_le_grid t (round t D) E (round_gt t D) (grid_up _ D E h (round_grid t D))

lemma least_grid_bit (x : ℝ) (D : ℕ) (hD : 1 ≤ D) (hx : OnGrid x D)
    (hmin : ∀ d < D, ¬OnGrid x d) :
    ⌊(2 : ℝ) ^ D * x⌋ = 2 * ⌊(2 : ℝ) ^ (D - 1) * x⌋ + 1 := by
  have bounds := bit_bounds x (D - 1)
  have E : (D - 1) + 1 = D := by omega
  rw [E] at bounds
  by_contra H
  have eqn : ⌊(2 : ℝ) ^ D * x⌋ = 2 * ⌊(2 : ℝ) ^ (D - 1) * x⌋ := by omega
  obtain ⟨z, hz⟩ := hx
  have floorz : ⌊(2 : ℝ) ^ D * x⌋ = z := by rw [hz, Int.floor_intCast]
  have he : (2 : ℝ) ^ D * x = 2 * (⌊(2 : ℝ) ^ (D - 1) * x⌋ : ℝ) := by
    rw [hz, ← floorz, eqn]
    push_cast
    rfl
  apply hmin (D - 1) (by omega)
  refine ⟨⌊(2 : ℝ) ^ (D - 1) * x⌋, ?_⟩
  have powe : (2 : ℝ) ^ D = (2 : ℝ) ^ (D - 1) * 2 := by
    calc
      _ = (2 : ℝ) ^ ((D - 1) + 1) := by congr 1; omega
      _ = _ := pow_succ _ _
  rw [powe] at he
  nlinarith only [he]

private lemma exception_donor (t x : ℝ) (D : ℕ) (h : t < x)
    (hx : OnGrid x D) (hne : x ≠ round t D) :
    round t D + 1 / (2 : ℝ) ^ D ≤ x := by
  obtain ⟨z, hz⟩ := hx
  have H := round_le_grid t x D h ⟨z, hz⟩
  have ne : z ≠ ⌊(2 : ℝ) ^ D * t⌋ + 1 := by
    intro eqn
    apply hne
    apply (eq_div_iff (by positivity : (2 : ℝ) ^ D ≠ 0)).mpr
    dsimp [round] at *
    have eqr : (z : ℝ) = (⌊(2 : ℝ) ^ D * t⌋ : ℝ) + 1 := by exact_mod_cast eqn
    simpa only [mul_comm] using hz.trans eqr
  have hi : ⌊(2 : ℝ) ^ D * t⌋ + 1 ≤ z := by
    have HH := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ D)).mp H
    change (⌊(2 : ℝ) ^ D * t⌋ : ℝ) + 1 ≤ x * 2 ^ D at HH
    rw [mul_comm x, hz] at HH
    exact_mod_cast HH
  have hi' : ⌊(2 : ℝ) ^ D * t⌋ + 2 ≤ z := by omega
  have HR : (⌊(2 : ℝ) ^ D * t⌋ : ℝ) + 2 ≤ (z : ℝ) := by exact_mod_cast hi'
  dsimp [round]
  rw [← add_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ D)).mpr
  rw [mul_comm x, hz]
  linarith only [HR]

private lemma fractional_margin (m D : ℕ) (p : Fin m → ℝ) (t : ℝ)
    (hs : ∑ i, p i = 1) (S : Finset (Fin m)) (hS : S.Nonempty)
    (hlow : ∀ i ∈ S, t ≤ p i) (hhigh : ∀ i ∈ S, p i < round t D)
    (hout : ∀ i, i ∉ S → OnGrid (p i) D) (u : ℝ)
    (hu : (S.card : ℝ) * u ≤ 1) :
    t + (1 / (2 : ℝ) ^ D) * u ≤ round t D := by
  classical
  let k : ℤ := ⌊(2 : ℝ) ^ D * t⌋
  let R : ℤ := (2 : ℤ) ^ D - ∑ i, ⌊(2 : ℝ) ^ D * p i⌋
  have floorS (i : Fin m) (hi : i ∈ S) : ⌊(2 : ℝ) ^ D * p i⌋ = k := by
    apply Int.floor_eq_iff.mpr
    have lo := mul_le_mul_of_nonneg_left (hlow i hi) (by positivity : (0 : ℝ) ≤ 2 ^ D)
    have high := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ D)).mp (hhigh i hi)
    constructor
    · exact (Int.floor_le _).trans lo
    · simpa [k, mul_comm] using high
  have tail_sum : (R : ℝ) = ∑ i ∈ S, ((2 : ℝ) ^ D * p i - k) := by
    have allsum : (R : ℝ) = ∑ i, ((2 : ℝ) ^ D * p i - (⌊(2 : ℝ) ^ D * p i⌋ : ℝ)) := by
      dsimp [R]
      simp only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat, Int.cast_sum, Int.fract]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_one]
    rw [allsum, ← Finset.sum_subset S.subset_univ (fun i _ hi => ?_)]
    · exact Finset.sum_congr rfl (fun i hi => by rw [floorS i hi])
    · obtain ⟨z, hz⟩ := hout i hi
      simp [hz]
  have upper : (R : ℝ) < (S.card : ℝ) := by
    rw [tail_sum]
    have H := Finset.sum_lt_sum_of_nonempty hS (fun i hi => show
        (2 : ℝ) ^ D * p i - k < 1 from by
      have hh := Int.lt_floor_add_one ((2 : ℝ) ^ D * p i)
      rw [floorS i hi] at hh
      linarith)
    simpa using H
  have upperI : R ≤ (S.card : ℤ) - 1 := by
    have H : R < (S.card : ℤ) := by exact_mod_cast upper
    omega
  have upperR : (R : ℝ) ≤ (S.card : ℝ) - 1 := by exact_mod_cast upperI
  have lower : (S.card : ℝ) * ((2 : ℝ) ^ D * t - k) ≤ (R : ℝ) := by
    rw [tail_sum]
    calc
      _ = ∑ i ∈ S, ((2 : ℝ) ^ D * t - k) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun i hi => sub_le_sub_right
        (mul_le_mul_of_nonneg_left (hlow i hi) (by positivity : (0 : ℝ) ≤ 2 ^ D)) (k : ℝ))
  have npos : (0 : ℝ) < S.card := by exact_mod_cast (Finset.card_pos.mpr hS)
  have bound : u ≤ (k : ℝ) + 1 - (2 : ℝ) ^ D * t := by
    nlinarith only [lower, upperR, hu, npos]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ D)).mpr
  change (t + 1 / (2 : ℝ) ^ D * u) * (2 : ℝ) ^ D ≤ (k : ℝ) + 1
  have eqn : (1 / (2 : ℝ) ^ D * u) * (2 : ℝ) ^ D = u := by field_simp
  rw [add_mul, eqn]
  linarith only [bound]


/-- Complete strict rounding on every full-real attaining law. -/
theorem result (m : ℕ) (hm : 2 ≤ m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (hk : ∀ i, p k ≤ p i) (ho : cost p / p k = alpha m) :
    StrictRoundingTarget m p k := by
  classical
  have term (i : Fin m) (hi : p k < p i) : ∃ D : ℕ, OnGrid (p i) D :=
    larger_terminal m hm p k hp hs hk ho i hi
  let depth : Fin m → ℕ := fun i => if hi : p k < p i then Nat.find (term i hi) else 0
  have spec (i : Fin m) (hi : p k < p i) :
      OnGrid (p i) (depth i) ∧ ∀ d < depth i, ¬OnGrid (p i) d := by
    dsimp only [depth]
    rw [dif_pos hi]
    exact ⟨Nat.find_spec (term i hi), fun d hd => Nat.find_min (term i hi) hd⟩
  have small (i : Fin m) : p i < 1 := by
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
    obtain ⟨j, hj⟩ := exists_ne i
    have H := Finset.add_le_sum (s := Finset.univ) (fun a _ => (hp a).le)
      (Finset.mem_univ i) (Finset.mem_univ j) (Ne.symm hj)
    rw [hs] at H
    linarith [hp j]
  have positive_depth (i : Fin m) (hi : p k < p i) : 1 ≤ depth i := by
    by_contra H
    have z := (spec i hi).1
    have de : depth i = 0 := by omega
    rw [de] at z
    obtain ⟨z, hz⟩ := z
    simp only [pow_zero, one_mul] at hz
    have fl : ⌊p i⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨(hp i).le, small i⟩
    have z0 : z = 0 := by simpa [hz] using fl
    rw [z0] at hz
    exact (hp i).ne' (by simpa using hz)
  have allround : ∀ i : Fin m, p k < p i → p i = round (p k) (depth i) := by
    by_contra H
    push Not at H
    obtain ⟨j0, hj0, ne0⟩ := H
    let E := Finset.univ.filter (fun i : Fin m => p k < p i ∧ p i ≠ round (p k) (depth i))
    have Ej0 : j0 ∈ E := by simp [E, hj0, ne0]
    obtain ⟨j, hj, maxdepth⟩ := Finset.exists_max_image E depth ⟨j0, Ej0⟩
    have J : p k < p j ∧ p j ≠ round (p k) (depth j) := by simpa [E] using hj
    let D := depth j
    let Q := round (p k) D
    let S := Finset.univ.filter (fun i : Fin m => p i < Q)
    have Sk : k ∈ S := by simp [S, Q, round_gt]
    have Sj : j ∉ S := by
      have H := round_le_grid (p k) (p j) D J.1 (spec j J.1).1
      simpa [S, Q, not_lt] using H
    have Sc : S.card < m := by
      have sub : S ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.filter_subset _ _, by intro eq; exact Sj (eq ▸ Finset.mem_univ j)⟩
      simpa using Finset.card_lt_card sub
    have grid_out (i : Fin m) (hi : i ∉ S) : OnGrid (p i) D := by
      have IQ : Q ≤ p i := by simpa [S, not_lt] using hi
      have It : p k < p i := (round_gt (p k) D).trans_le IQ
      by_cases hd : depth i ≤ D
      · exact grid_up (p i) (depth i) D hd (spec i It).1
      · have farther : D < depth i := by omega
        have ri : p i = round (p k) (depth i) := by
          by_contra ne
          have ei : i ∈ E := by simp [E, It, ne]
          have HH := maxdepth i ei
          change depth i ≤ D at HH
          omega
        have upper : p i ≤ Q := by
          rw [ri]
          exact round_antitone (p k) D (depth i) farther.le
        have eqn : p i = Q := le_antisymm upper IQ
        have gd : OnGrid (p i) D := by rw [eqn]; exact round_grid (p k) D
        exact False.elim ((spec i It).2 D farther gd)
    obtain ⟨q, u, up, qpos, qsum, qlow, qzero, qcost, ub⟩ := receiver_law m S ⟨k, Sk⟩
    have margin : p k + (1 / (2 : ℝ) ^ D) * u ≤ Q :=
      fractional_margin m D p (p k) hs S ⟨k, Sk⟩ (fun i _ => hk i)
        (fun i hi => by simpa [S] using hi) grid_out u ub
    have donor : Q + 1 / (2 : ℝ) ^ D ≤ p j :=
      exception_donor (p k) (p j) D J.1 (spec j J.1).1 J.2
    have donor' : p k + (1 / (2 : ℝ) ^ D) * (1 + u) ≤ p j := by
      nlinarith only [margin, donor]
    have outside (i : Fin m) (hi : i ∉ S) (hij : i ≠ j) :
        p k + (1 / (2 : ℝ) ^ D) * u ≤ p i := by
      exact margin.trans (by simpa [S, not_lt] using hi)
    have profit : cost q < alpha m * u := by
      rw [qcost]
      exact mul_lt_mul_of_pos_right (alpha_lt S.card m (Finset.card_pos.mpr ⟨k, Sk⟩) Sc) up
    have opt : cost p = alpha m * p k := by
      have H := (div_eq_iff (hp k).ne').mp ho
      simpa [mul_comm] using H
    have bit := least_grid_bit (p j) D (positive_depth j J.1) (spec j J.1).1 (spec j J.1).2
    exact D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange.profitable_leaf_impossible m D hm p q j (positive_depth j J.1)
      (fun i => (hp i).le) hs qpos qsum (qzero j Sj) S (p k) u (hp k) up
      (fun i hi => ⟨hk i, qlow i hi⟩) outside donor' opt profit bit
  intro i hi
  refine ⟨depth i, positive_depth i hi, (spec i hi).1, (spec i hi).2, ?_⟩
  simpa [round, Int.cast_add, Int.cast_one] using allround i hi


end D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding
