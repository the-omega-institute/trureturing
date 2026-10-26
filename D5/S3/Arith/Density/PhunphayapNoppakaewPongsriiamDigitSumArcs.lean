/- GID: D5/S3/Arith/Density/PhunphayapNoppakaewPongsriiamDigitSumArcs
   generality: G
   mirror-B: D5/B/S3/Arith/Density/PhunphayapNoppakaewPongsriiamDigitSumArcs
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Digit-sum arcs have gcd-controlled cofiniteness, infinitude, and density. -/
/-
Settlement of Question 3 in arXiv:2303.13017v1, preregistered in #19415.
admission_basis: open-problem-resolution (#19415; Proved)
escape_witness: none
Direct frozen dependencies: D5/S1/Digit/MaxDigitSumBase.digitSum
  statement_id: sha256:685be4a14b25d5106de2047a418119ee94c199c83c1479e7d9ab2c7f142ce490.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19481.
Direct frozen dependencies: D5/S3/ArithSums/A400361PillaiMean.quotient_ratio_limit
  statement_id: sha256:1f5f094c2b2c031ab14bc98a22319f9732b6b734b100101c37d7e319007de1db.
Direct frozen dependencies: D5/S3/Arith/Density/AsymptoticDensity.HasDensity
  statement_id: sha256:fcafccd138be17912083dad6ece4a8f0428180d5ade94387c1ef744f11d416df.
Direct frozen dependencies: D5/S3/Arith/Density/AsymptoticDensity.lowerDensity
  statement_id: sha256:74928e252672274b63c03a732cb0ec5ab1a5904b4df5fbd1fd040d5a79bdb1a3.
Direct frozen dependencies: D5/S3/Arith/Density/AsymptoticDensity.upperDensity
  statement_id: sha256:3a5fdb79fcbd6608db8d2a56641f1fcf7b5fbbe60504da68a8e3ae4ec2368a3b.
The digit-sum and density expressions in Out and claim are the literal supplied bodies;
proofs use MaxDigitSumBase.digitSum and AsymptoticDensity.HasDensity, with the density
correspondence supplied by the consumed private density_count_shift and density_as_limit.
The latter identifies positive-interval counts with zero-based counts after u ↦ u + 1.
The quotient ratio limit is reused from A400361PillaiMean.
The statements concern unbounded natural numbers and limits, so utility is none.
Out: proof_shape: bind-only; escape_witness: none; consumers: claim, out_add, out_self, out_dvd.
claim: proof_shape: bind-only; escape_witness: none; consumers: result.
sum_step: proof_shape: bind-only; escape_witness: none; consumers: sum_cons, sum_complement.
sum_cons: proof_shape: bind-only; escape_witness: none; consumers: sum_complement.
sum_pos: proof_shape: bind-only; escape_witness: none; consumers: out_self, out_complement, out_infinite_iff.
sum_congr: proof_shape: bind-only; escape_witness: none; consumers: out_dvd, out_setGcd.
sum_concat: proof_shape: bind-only; escape_witness: none; consumers: sum_multiple_complement, out_add.
sum_complement: proof_shape: content; escape_witness: none; consumers: sum_multiple_complement.
sum_multiple_complement: proof_shape: content; escape_witness: none; consumers: out_complement.
out_add: proof_shape: bind-only; escape_witness: none; consumers: out_closure.
out_self: proof_shape: bind-only; escape_witness: none; consumers: out_setGcd, out_infinite_iff.
out_dvd: proof_shape: bind-only; escape_witness: none; consumers: out_setGcd, out_infinite_iff, result.
out_complement: proof_shape: content; escape_witness: none; consumers: out_setGcd.
out_setGcd: proof_shape: content; escape_witness: none; consumers: out_cofinite.
out_closure: proof_shape: bind-only; escape_witness: none; consumers: out_cofinite.
out_cofinite: proof_shape: content; escape_witness: none; consumers: out_infinite_iff, result.
out_infinite_iff: proof_shape: content; escape_witness: none; consumers: result.
multiples_count: proof_shape: bind-only; escape_witness: none; consumers: density_cofinite_multiples.
density_count_shift: proof_shape: bind-only; escape_witness: none; consumers: density_as_limit, density_cofinite_multiples.
density_as_limit: proof_shape: bind-only; escape_witness: none; consumers: result.
density_cofinite_multiples: proof_shape: bind-only; escape_witness: none; consumers: result.
result: proof_shape: content; escape_witness: none; consumers: settling result.
-/
import D5.S1.Digit.MaxDigitSumBase
import D5.S3.ArithSums.A400361PillaiMean
import D5.S3.Arith.Density.AsymptoticDensity
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Order.Interval.Set.Nat

/-! Binding conventions for P. N. Phunphayap, P. Noppakaew and P. Pongsriiam, "Directed graphs of integers with arcs
determined by an arithmetic function", arXiv:2303.13017v1 (Utilitas Math. 124 (2025) 101–114): the base-b digit sum
s_b, the arc set Out(s_b, n) = {u ∈ ℕ | ∃ N ∈ ℕ, n ∣ N, s_b(N) = u} (positive integers), natural density, and
Question 3. -/

namespace D5.S3.Arith.Density.PhunphayapNoppakaewPongsriiamDigitSumArcs

open Filter Topology
open D5.S1.Digit.MaxDigitSumBase (digitSum)

/-- `Out(s_b, n)`: the positive integers `u` with an `s_b`-arc from `n`, i.e. some positive integer `N` divisible by
`n` has `s_b(N) = u`. -/
def Out (b n : ℕ) : Set ℕ :=
  {u | 0 < u ∧ ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits b N).sum = u}

/-- Question 3, answered as one statement for all `b ≥ 2`, `n ≥ 1` with `d = gcd(b − 1, n)`. The positive integers in
`Out(s_b, n)` not divisible by `s_b(n)` form an infinite set exactly when `d < s_b(n)`, and `Out(s_b, n)` has natural
density `1/d`. -/
def claim : Prop :=
  ∀ b n : ℕ, 2 ≤ b → 1 ≤ n →
    ((Out b n \ {u | (Nat.digits b n).sum ∣ u}).Infinite ↔
      Nat.gcd (b - 1) n < (Nat.digits b n).sum) ∧
      Tendsto (fun x : ℕ => (((Out b n ∩ Set.Icc 1 x).ncard : ℝ) / x))
        atTop (𝓝 (1 / (Nat.gcd (b - 1) n : ℝ)))

end D5.S3.Arith.Density.PhunphayapNoppakaewPongsriiamDigitSumArcs

namespace D5.S3.Arith.Density.PhunphayapNoppakaewPongsriiamDigitSumArcs

open Filter Topology
open scoped Classical
open D5.S1.Digit.MaxDigitSumBase (digitSum)

private theorem sum_step {b : ℕ} (hb : 2 ≤ b) (x : ℕ) :
    digitSum b x = x % b + digitSum b (x / b) := by
  by_cases hx : x = 0
  · simp [hx, digitSum]
  · simpa [digitSum] using congrArg List.sum (Nat.digits_def' (by omega : 1 < b)
      (Nat.pos_of_ne_zero hx))

private theorem sum_cons {b : ℕ} (hb : 2 ≤ b) (q r : ℕ) (hr : r < b) :
    digitSum b (b * q + r) = r + digitSum b q := by
  rw [sum_step hb]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hr, Nat.mul_add_div (by omega : 0 < b),
    Nat.div_eq_of_lt hr]

private theorem sum_pos {b x : ℕ} (hx : 0 < x) : 0 < digitSum b x := by
  have hne : Nat.digits b x ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have hlast := Nat.getLast_digit_ne_zero b (by omega : x ≠ 0)
  have hmem := List.getLast_mem hne
  have hle := List.single_le_sum (fun y _ => Nat.zero_le y) _ hmem
  change 0 < (Nat.digits b x).sum
  omega

private theorem sum_congr {b : ℕ} (hb : 2 ≤ b) (x : ℕ) :
    x ≡ digitSum b x [MOD b - 1] := by
  have h := Nat.ofDigits_modEq' b 1 (b - 1)
    (Nat.modEq_sub (by omega : 1 ≤ b)) (Nat.digits b x)
  simpa [Nat.ofDigits_digits, Nat.ofDigits_one, digitSum] using h

private theorem sum_concat {b : ℕ} (hb : 2 ≤ b) (r U V : ℕ) (hV : V < b ^ r) :
    digitSum b (b ^ r * U + V) = digitSum b U + digitSum b V := by
  by_cases hU : U = 0
  · simp [hU, digitSum]
  have hlen : (Nat.digits b V).length ≤ r :=
    (Nat.digits_length_le_iff (by omega : 1 < b) V).mpr hV
  have h := congrArg List.sum (Nat.digits_append_zeroes_append_digits
    (b := b) (n := V) (m := U) (k := r - (Nat.digits b V).length)
    (by omega : 1 < b) (by omega : 0 < U))
  rw [Nat.add_sub_of_le hlen] at h
  simpa [digitSum, List.sum_append, List.sum_replicate, add_comm] using h.symm

private theorem sum_complement {b : ℕ} (hb : 2 ≤ b) (L m : ℕ) (hm : m < b ^ L) :
    digitSum b (b ^ L - 1 - m) + digitSum b m = (b - 1) * L := by
  induction L generalizing m with
  | zero =>
      have : m = 0 := Nat.lt_one_iff.mp hm
      simp [this, digitSum]
  | succ L ih =>
      have hp : 0 < b ^ L := pow_pos (by omega) _
      have hq : m / b < b ^ L := by
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < b)).2
        simpa [pow_succ] using hm
      have hr := Nat.mod_lt m (by omega : 0 < b)
      have hdiv := Nat.mod_add_div m b
      have he : b ^ (L + 1) - 1 - m =
          b * (b ^ L - 1 - m / b) + (b - 1 - m % b) := by
        rw [pow_succ]
        have hsub := Nat.sub_add_cancel (show m / b ≤ b ^ L - 1 by omega)
        have hsub2 := Nat.sub_add_cancel (show m % b ≤ b - 1 by omega)
        have hsub3 := Nat.sub_add_cancel (show 1 ≤ b ^ L by omega)
        have hsub4 := Nat.sub_add_cancel (show 1 ≤ b by omega)
        have hmul := congrArg (fun t : ℕ => b * t)
          (show b ^ L - 1 - m / b + m / b + 1 = b ^ L by omega)
        simp only [mul_add, mul_one] at hmul
        have ht : b * (b ^ L - 1 - m / b) + (b - 1 - m % b) + m + 1 = b ^ L * b := by
          nlinarith
        omega
      rw [he, sum_cons hb _ _ (by omega), sum_step hb m]
      have hi := ih (m / b) hq
      rw [Nat.mul_succ]
      omega

private theorem sum_multiple_complement {b n L : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n)
    (hL : n < b ^ L) : digitSum b (n * (b ^ L - 1)) = (b - 1) * L := by
  have hp : 0 < b ^ L := pow_pos (by omega) _
  have he : n * (b ^ L - 1) = b ^ L * (n - 1) + (b ^ L - 1 - (n - 1)) := by
    have hsub := Nat.sub_add_cancel (show 1 ≤ b ^ L by omega)
    have hsubn := Nat.sub_add_cancel hn
    have hs := Nat.sub_add_cancel (show n - 1 ≤ b ^ L - 1 by omega)
    nlinarith
  rw [he, sum_concat hb _ _ _ (by omega)]
  have h := sum_complement hb L (n - 1) (by omega)
  omega



private theorem out_add {b n u v : ℕ} (hb : 2 ≤ b) (hu : u ∈ Out b n) (hv : v ∈ Out b n) :
    u + v ∈ Out b n := by
  obtain ⟨hu0, U, hU0, hUn, rfl⟩ := hu
  obtain ⟨hv0, V, hV0, hVn, rfl⟩ := hv
  let r := (Nat.digits b V).length
  refine ⟨by omega, V + b ^ r * U, by positivity,
    dvd_add hVn (dvd_mul_of_dvd_right hUn _), ?_⟩
  change digitSum b (V + b ^ r * U) = digitSum b U + digitSum b V
  rw [Nat.add_comm V]
  exact sum_concat hb r U V
    ((Nat.digits_length_le_iff (by omega : 1 < b) V).mp (le_refl _))

private theorem out_self {b n : ℕ} (hn : 1 ≤ n) : digitSum b n ∈ Out b n :=
  ⟨sum_pos (by omega), n, by omega, dvd_refl _, rfl⟩

private theorem out_dvd {b n u : ℕ} (hb : 2 ≤ b) (hu : u ∈ Out b n) :
    Nat.gcd (b - 1) n ∣ u := by
  obtain ⟨_, N, _, hnN, rfl⟩ := hu
  exact ((sum_congr hb N).dvd_iff (Nat.gcd_dvd_left _ _)).mp
    ((Nat.gcd_dvd_right _ _).trans hnN)

private theorem out_complement {b n L : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n)
    (hL : n < b ^ L) : (b - 1) * L ∈ Out b n := by
  have hpos : 0 < n * (b ^ L - 1) := by
    apply Nat.mul_pos (by omega) (by omega)
  refine ⟨?_, n * (b ^ L - 1), hpos, dvd_mul_right _ _, sum_multiple_complement hb hn hL⟩
  rw [← sum_multiple_complement hb hn hL]
  exact sum_pos hpos

private theorem out_setGcd {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    Nat.setGcd (Out b n) = Nat.gcd (b - 1) n := by
  apply Nat.dvd_antisymm
  · let L := (Nat.digits b n).length
    have hL : n < b ^ L :=
      (Nat.digits_length_le_iff (by omega : 1 < b) n).mp (le_refl _)
    have hLp : n < b ^ (L + 1) := lt_of_lt_of_le hL
      (Nat.pow_le_pow_right (by omega : 0 < b) (by omega : L ≤ L + 1))
    have h0 := Nat.setGcd_dvd_of_mem (out_complement hb hn hL)
    have h1 := Nat.setGcd_dvd_of_mem (out_complement hb hn hLp)
    have hc : Nat.setGcd (Out b n) ∣ b - 1 :=
      (Nat.dvd_add_iff_right h0).mpr h1
    have hs := Nat.setGcd_dvd_of_mem (out_self (b := b) hn)
    have hg := (sum_congr hb n).gcd_eq
    apply (Nat.dvd_gcd hc hs).trans
    have he : Nat.gcd (b - 1) (digitSum b n) = Nat.gcd (b - 1) n := by
      simpa [Nat.gcd_comm] using hg.symm
    rw [he]
  · exact Nat.dvd_setGcd_iff.mpr (fun u hu => out_dvd hb hu)

private theorem out_closure {b n u : ℕ} (hb : 2 ≤ b)
    (hu : u ∈ AddSubmonoid.closure (Out b n)) : u = 0 ∨ u ∈ Out b n := by
  induction hu using AddSubmonoid.closure_induction with
  | mem x hx => exact Or.inr hx
  | zero => exact Or.inl rfl
  | add x y hx hy ihx ihy =>
      rcases ihx with rfl | hx'
      · simpa using ihy
      rcases ihy with rfl | hy'
      · simpa using Or.inr hx'
      exact Or.inr (out_add hb hx' hy')

private theorem out_cofinite {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    ∃ T : ℕ, ∀ u ≥ T, 0 < u → Nat.gcd (b - 1) n ∣ u → u ∈ Out b n := by
  obtain ⟨T, hT⟩ := Nat.exists_mem_closure_of_ge (Out b n)
  refine ⟨T, fun u hu hu0 hdu => ?_⟩
  have h := out_closure hb (hT u hu (by rwa [out_setGcd hb hn]))
  exact h.resolve_left (by omega)

private theorem out_infinite_iff {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    (Out b n \ {u | digitSum b n ∣ u}).Infinite ↔ Nat.gcd (b - 1) n < digitSum b n := by
  let d := Nat.gcd (b - 1) n
  let s := digitSum b n
  have hd : 0 < d := Nat.gcd_pos_of_pos_left n (by omega)
  have hs : 0 < s := sum_pos (by omega)
  have hds : d ∣ s := out_dvd hb (out_self hn)
  constructor
  · intro hInf
    have hle : d ≤ s := Nat.le_of_dvd hs hds
    by_contra hlt
    have he : d = s := by omega
    obtain ⟨u, hu, hnu⟩ := hInf.nonempty
    apply hnu
    change s ∣ u
    rw [← he]
    exact out_dvd hb hu
  · intro hlt
    obtain ⟨T, hT⟩ := out_cofinite hb hn
    let f : ℕ → ℕ := fun t => s * (t + T) + d
    have hinj : Function.Injective f := by
      intro t v he
      dsimp [f] at he
      have h := Nat.mul_left_cancel hs (Nat.add_right_cancel he)
      omega
    apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨t, rfl⟩
    have hdiv : d ∣ f t := dvd_add (dvd_mul_of_dvd_left hds _) (dvd_refl d)
    have hge : T ≤ f t := by
      have h := Nat.le_mul_of_pos_left (t + T) hs
      dsimp [f]
      omega
    refine ⟨hT (f t) hge (by dsimp [f]; positivity) hdiv, ?_⟩
    change ¬s ∣ s * (t + T) + d
    intro hbad
    have hsd : s ∣ d := (Nat.dvd_add_right (dvd_mul_right s (t + T))).mp hbad
    have := Nat.le_of_dvd hd hsd
    omega

private theorem multiples_count (d x : ℕ) :
    (({u : ℕ | d ∣ u} ∩ Set.Icc 1 x).ncard) = x / d := by
  have he : ({u : ℕ | d ∣ u} ∩ Set.Icc 1 x) =
      ↑((Finset.Ioc 0 x).filter (fun u => d ∣ u)) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc,
      Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    omega
  rw [he, Set.ncard_coe_finset, Nat.Ioc_filter_dvd_card_eq_div]

private theorem density_count_shift (S : Set ℕ) (x : ℕ) :
    ((Finset.range x).filter (fun u => u + 1 ∈ S)).card = (S ∩ Set.Icc 1 x).ncard := by
  classical
  have he : (S ∩ Set.Icc 1 x) =
      ↑(((Finset.range x).filter (fun u => u + 1 ∈ S)).map
        ⟨Nat.succ, Nat.succ_injective⟩) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.mem_coe, Finset.mem_map,
      Finset.mem_filter, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hu, hpos, hle⟩
      exact ⟨u - 1, ⟨by omega, by simpa [Nat.sub_add_cancel hpos] using hu⟩,
        by omega⟩
    · rintro ⟨v, ⟨hv, hS⟩, rfl⟩
      exact ⟨hS, by omega, by omega⟩
  rw [he, Set.ncard_coe_finset, Finset.card_map]

private theorem density_as_limit (S : Set ℕ) (δ : ℝ)
    (h : D5.S3.Arith.Density.AsymptoticDensity.HasDensity {u | u + 1 ∈ S} δ) :
    Tendsto (fun x : ℕ => ((S ∩ Set.Icc 1 x).ncard : ℝ) / x) atTop (𝓝 δ) := by
  classical
  unfold D5.S3.Arith.Density.AsymptoticDensity.HasDensity
    D5.S3.Arith.Density.AsymptoticDensity.lowerDensity
    D5.S3.Arith.Density.AsymptoticDensity.upperDensity at h
  simp only [Set.mem_ofPred_eq, density_count_shift] at h
  have hupper (x : ℕ) : ((S ∩ Set.Icc 1 x).ncard : ℝ) / x ≤ 1 := by
    have hc : (S ∩ Set.Icc 1 x).ncard ≤ x := by
      simpa using (Set.ncard_le_ncard (s := S ∩ Set.Icc 1 x)
        Set.inter_subset_right (Set.finite_Icc 1 x))
    exact div_le_one_of_le₀ (by exact_mod_cast hc) (Nat.cast_nonneg x)
  exact tendsto_of_liminf_eq_limsup (h.1.trans h.2) h.2
    (isBoundedUnder_of_eventually_le (Eventually.of_forall hupper))
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun x => by positivity)))

private theorem density_cofinite_multiples (S : Set ℕ) (d : ℕ)
    (hsub : ∀ u ∈ S, d ∣ u)
    (hcof : ∃ T : ℕ, ∀ u ≥ T, 0 < u → d ∣ u → u ∈ S) :
    D5.S3.Arith.Density.AsymptoticDensity.HasDensity {u | u + 1 ∈ S} (1 / (d : ℝ)) := by
  classical
  obtain ⟨T, hT⟩ := hcof
  have hbound (x : ℕ) :
      (S ∩ Set.Icc 1 x).ncard ≤ x / d ∧
      x / d ≤ (S ∩ Set.Icc 1 x).ncard + T := by
    have hf : (S ∩ Set.Icc 1 x).Finite := (Set.finite_Icc 1 x).subset Set.inter_subset_right
    have hm : ({u : ℕ | d ∣ u} ∩ Set.Icc 1 x).Finite :=
      (Set.finite_Icc 1 x).subset Set.inter_subset_right
    constructor
    · rw [← multiples_count d x]
      exact Set.ncard_le_ncard (fun u hu => ⟨hsub u hu.1, hu.2⟩) hm
    · have hs : ({u : ℕ | d ∣ u} ∩ Set.Icc 1 x) ⊆
          (S ∩ Set.Icc 1 x) ∪ Set.Iio T := by
        intro u hu
        by_cases hge : T ≤ u
        · exact Or.inl ⟨hT u hge (by have := hu.2.1; omega) hu.1, hu.2⟩
        · exact Or.inr (by change u < T; omega)
      have h := (Set.ncard_le_ncard hs (hf.union (Set.finite_Iio T))).trans
        (Set.ncard_union_le (S ∩ Set.Icc 1 x) (Set.Iio T))
      simpa [multiples_count] using h
  let E : ℕ → ℝ := fun x => ((x / d : ℕ) : ℝ) - ((S ∩ Set.Icc 1 x).ncard : ℝ)
  have hE0 : ∀ x, 0 ≤ E x := by
    intro x
    have h := hbound x
    dsimp [E]
    exact sub_nonneg.mpr (by exact_mod_cast h.1)
  have hET : ∀ x, E x ≤ (T : ℝ) := by
    intro x
    have h := hbound x
    dsimp [E]
    have : ((x / d : ℕ) : ℝ) ≤ ((S ∩ Set.Icc 1 x).ncard : ℝ) + T := by
      exact_mod_cast h.2
    linarith
  have hElim : Tendsto (fun x : ℕ => E x / x) atTop (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (Filter.Eventually.of_forall hE0)
      (Filter.Eventually.of_forall hET) tendsto_natCast_atTop_atTop
  have hlim := (D5.S3.ArithSums.A400361PillaiMean.quotient_ratio_limit d).sub hElim
  have hresult : Tendsto (fun x : ℕ => ((S ∩ Set.Icc 1 x).ncard : ℝ) / x)
      atTop (𝓝 (1 / (d : ℝ))) := by
    convert hlim using 1
    · ext x
      dsimp [E]
      ring
    · simp
  have hrange : Tendsto (fun x : ℕ =>
      (((Finset.range x).filter (fun u => u + 1 ∈ S)).card : ℝ) / x)
      atTop (𝓝 (1 / (d : ℝ))) := by
    simpa only [density_count_shift] using hresult
  exact ⟨hrange.liminf_eq.trans hrange.limsup_eq.symm, hrange.limsup_eq⟩

theorem result : claim := by
  intro b n hb hn
  refine ⟨out_infinite_iff hb hn, ?_⟩
  exact density_as_limit (Out b n) _ (density_cofinite_multiples (Out b n) (Nat.gcd (b - 1) n)
    (fun u hu => out_dvd hb hu) (out_cofinite hb hn))


end D5.S3.Arith.Density.PhunphayapNoppakaewPongsriiamDigitSumArcs
