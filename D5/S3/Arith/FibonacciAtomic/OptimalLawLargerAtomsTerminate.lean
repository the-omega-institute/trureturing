/- GID: D5/S3/Arith/FibonacciAtomic/OptimalLawLargerAtomsTerminate
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/OptimalLawLargerAtomsTerminate
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Larger atoms of an attaining real law have terminating binary expansions. -/

import D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.OptimalLawLargerAtomsTerminate

open scoped BigOperators
open CarryGraphCriticalAttainment (alpha)
open DyadicSupportLines (cost residual)

/-- Redistributing a depth-d donor mass over a relabelled probability law
preserves total mass and increases the dyadic floor-tail cost by at most
2^(-d) times the receiver law's cost, provided the donor's shallower
floor counts do not change. -/
theorem transfer (m n : ℕ) (p : Fin m → ℝ) (hs : ∑ i, p i = 1)
    (I : Finset (Fin m)) (enum : I ≃ Fin n) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1)
    (j : Fin m) (jI : j ∉ I) (d : ℕ)
    (shallow : ∀ h : ℕ, h < d →
      ⌊(2 : ℝ) ^ h * (p j - 1 / (2 : ℝ) ^ d)⌋ = ⌊(2 : ℝ) ^ h * p j⌋) :
    let δ := 1 / (2 : ℝ) ^ d
    let R : Fin m → ℝ := fun i => if hi : i ∈ I then q (enum ⟨i, hi⟩) else 0
    let P : Fin m → ℝ := fun i => p i + δ * R i - if i = j then δ else 0
    (∑ i, P i) = 1 ∧ cost P ≤ cost p + δ * cost q := by
  classical
  dsimp only
  let δ := 1 / (2 : ℝ) ^ d
  let R : Fin m → ℝ := fun i => if hi : i ∈ I then q (enum ⟨i, hi⟩) else 0
  let P : Fin m → ℝ := fun i => p i + δ * R i - if i = j then δ else 0
  have δpos : 0 < δ := by dsimp only [δ]; positivity
  have data (n : ℕ) (P : Fin n → ℝ) (hS : ∑ i, P i = 1) :
      (∀ d, 0 ≤ residual P d) ∧
      Summable (fun d => residual P d / (2 : ℝ) ^ d) := by
    have frac (d : ℕ) :
        residual P d = ∑ i, Int.fract ((2 : ℝ) ^ d * P i) := by
      simp only [DyadicSupportLines.residual, Int.fract, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hS, mul_one, Int.cast_sum]
    have bounds (d : ℕ) : 0 ≤ residual P d ∧ residual P d ≤ n := by
      rw [frac]
      refine ⟨Finset.sum_nonneg (fun i _ => Int.fract_nonneg _), ?_⟩
      calc
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (Int.fract_lt_one _).le)
        _ = n := by simp
    refine ⟨fun d => (bounds d).1, ?_⟩
    apply Summable.of_nonneg_of_le
      (fun d => div_nonneg (bounds d).1 (by positivity))
      (fun d => div_le_div_of_nonneg_right (bounds d).2 (by positivity))
    simpa only [div_eq_mul_inv, one_mul, inv_pow] using
      (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left (n : ℝ)
  have relabel_sum (F : ℝ → ℝ) (hF : F 0 = 0) :
      (∑ i, F (R i)) = ∑ a, F (q a) := by
    have E (i : Fin m) : F (R i) = if hi : i ∈ I then F (q (enum ⟨i, hi⟩)) else 0 := by
      dsimp only [R]
      split_ifs <;> simp only [hF]
    simp_rw [E]
    calc
      _ = ∑ i ∈ I.attach, F (q (enum i)) :=
        (Finset.sum_attach_eq_sum_dite I (fun i => F (q (enum i)))).symm
      _ = ∑ i : I, F (q (enum i)) :=
        (Finset.sum_coe_sort_eq_attach I (fun i => F (q (enum i)))).symm
      _ = _ := enum.sum_comp (fun a => F (q a))
  have Rnonneg (i : Fin m) : 0 ≤ R i := by
    dsimp only [R]
    split_ifs <;> first | exact hq _ | exact le_rfl
  have Rsum : ∑ i, R i = 1 := (relabel_sum id rfl).trans hsum
  have Psum : ∑ i, P i = 1 := by
    simp only [P, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Rsum, hs, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
    ring
  have Rj : R j = 0 := by dsimp only [R]; rw [dif_neg jI]
  have head_bound (h : ℕ) (hh : h < d) : residual P h ≤ residual p h := by
    have terms (i : Fin m) : ⌊(2 : ℝ) ^ h * p i⌋ ≤ ⌊(2 : ℝ) ^ h * P i⌋ := by
      by_cases hij : i = j
      · subst i
        dsimp only [P]
        rw [Rj, mul_zero, add_zero, if_pos rfl]
        exact (shallow h hh).ge
      · apply Int.floor_mono
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp only [P]
        rw [if_neg hij, sub_zero]
        linarith [mul_nonneg δpos.le (Rnonneg i)]
    have H : (∑ i, (⌊(2 : ℝ) ^ h * p i⌋ : ℝ)) ≤
        ∑ i, (⌊(2 : ℝ) ^ h * P i⌋ : ℝ) :=
      Finset.sum_le_sum (fun i _ => Int.cast_le.mpr (terms i))
    simp only [DyadicSupportLines.residual, Int.cast_sum]
    linarith
  have tail_bound (h : ℕ) : residual P (h + d) ≤ residual p (h + d) + residual q h := by
    have scale (i : Fin m) : (2 : ℝ) ^ (h + d) * P i =
        (2 : ℝ) ^ (h + d) * p i + (2 : ℝ) ^ h * R i -
          if i = j then ((2 ^ h : ℤ) : ℝ) else 0 := by
      dsimp only [P, δ]
      rw [pow_add]
      push_cast
      split_ifs <;> field_simp <;> ring
    have terms (i : Fin m) :
        ⌊(2 : ℝ) ^ (h + d) * p i⌋ + ⌊(2 : ℝ) ^ h * R i⌋ -
          (if i = j then (2 : ℤ) ^ h else 0) ≤ ⌊(2 : ℝ) ^ (h + d) * P i⌋ := by
      rw [scale]
      by_cases hij : i = j
      · subst i
        simp only [Rj, mul_zero, Int.floor_zero, add_zero, if_true,
          Int.floor_sub_intCast, le_refl]
      · simpa only [if_neg hij, sub_zero] using
          Int.le_floor_add ((2 : ℝ) ^ (h + d) * p i) ((2 : ℝ) ^ h * R i)
    have relabel : (∑ i, (⌊(2 : ℝ) ^ h * R i⌋ : ℝ)) =
        ∑ a, (⌊(2 : ℝ) ^ h * q a⌋ : ℝ) :=
      relabel_sum (fun x => (⌊(2 : ℝ) ^ h * x⌋ : ℝ)) (by simp)
    have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => terms i)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at H
    have HC : (∑ i, (⌊(2 : ℝ) ^ (h + d) * p i⌋ : ℝ)) +
        (∑ i, (⌊(2 : ℝ) ^ h * R i⌋ : ℝ)) - (2 : ℝ) ^ h ≤
        ∑ i, (⌊(2 : ℝ) ^ (h + d) * P i⌋ : ℝ) := by exact_mod_cast H
    rw [relabel] at HC
    simp only [DyadicSupportLines.residual, Int.cast_sum]
    linarith
  have pD := data m p hs
  have PD := data m P Psum
  have qD := data n q hsum
  have tail_terms (h : ℕ) : residual P (h + d) / (2 : ℝ) ^ (h + d) ≤
      residual p (h + d) / (2 : ℝ) ^ (h + d) + δ * (residual q h / (2 : ℝ) ^ h) := by
    have H := div_le_div_of_nonneg_right (tail_bound h)
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (h + d))
    calc
      _ ≤ (residual p (h + d) + residual q h) / (2 : ℝ) ^ (h + d) := H
      _ = _ := by
        dsimp only [δ]
        rw [pow_add]
        field_simp
  have tail_sum : (∑' h, residual P (h + d) / (2 : ℝ) ^ (h + d)) ≤
      (∑' h, residual p (h + d) / (2 : ℝ) ^ (h + d)) + δ * cost q := by
    have shiftedP := (summable_nat_add_iff d).mpr PD.2
    have shiftedp := (summable_nat_add_iff d).mpr pD.2
    have H := shiftedP.tsum_le_tsum tail_terms (shiftedp.add (qD.2.mul_left δ))
    rwa [Summable.tsum_add shiftedp (qD.2.mul_left δ), tsum_mul_left] at H
  have cost_bound : cost P ≤ cost p + δ * cost q := by
    have H := Finset.sum_le_sum (s := Finset.range d) (fun h hh =>
      div_le_div_of_nonneg_right (head_bound h (Finset.mem_range.mp hh))
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ h))
    have eqP := PD.2.sum_add_tsum_nat_add d
    have eqp := pD.2.sum_add_tsum_nat_add d
    change _ = cost P at eqP
    change _ = cost p at eqp
    linarith only [H, tail_sum, eqP, eqp]
  exact ⟨Psum, cost_bound⟩

/-- Every atom strictly larger than the minimum in an attaining positive real law
has a terminating binary expansion. -/
theorem result (m : ℕ) (hm : 2 ≤ m) (p : Fin m → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (hopt : cost p = alpha m * sInf (Set.range p))
    (j : Fin m) (hj : sInf (Set.range p) < p j) :
    ∃ D N : ℕ, p j = (N : ℝ) / (2 : ℝ) ^ D := by
  classical
  by_contra hnondyadic
  have deep (x : ℝ) (hx : 0 < x)
      (hnondyadic : ¬ ∃ D N : ℕ, x = (N : ℝ) / (2 : ℝ) ^ D) (B : ℕ) :
      ∃ d : ℕ, B < d ∧
        ⌊(2 : ℝ) ^ d * x⌋ - 2 * ⌊(2 : ℝ) ^ (d - 1) * x⌋ = 1 ∧
        ∀ h : ℕ, h < d →
          ⌊(2 : ℝ) ^ h * (x - 1 / (2 : ℝ) ^ d)⌋ = ⌊(2 : ℝ) ^ h * x⌋ := by
    classical
    let r := Int.fract ((2 : ℝ) ^ B * x)
    have rpos : 0 < r := by
      apply Int.fract_pos.mpr
      intro eq
      have nonneg : 0 ≤ ⌊(2 : ℝ) ^ B * x⌋ := Int.floor_nonneg.mpr (by positivity)
      apply hnondyadic
      refine ⟨B, ⌊(2 : ℝ) ^ B * x⌋.toNat, ?_⟩
      have cast_nat : (⌊(2 : ℝ) ^ B * x⌋.toNat : ℝ) = (⌊(2 : ℝ) ^ B * x⌋ : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg nonneg)
      rw [cast_nat]
      exact (eq_div_iff (by positivity : (2 : ℝ) ^ B ≠ 0)).mpr (by nlinarith [eq])
    have rlt : r < 1 := Int.fract_lt_one _
    have crossing : ∃ n : ℕ, 1 ≤ (2 : ℝ) ^ n * r := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / r) (by norm_num : (1 : ℝ) < 2)
      exact ⟨n, ((div_lt_iff₀ rpos).mp hn).le⟩
    let n := Nat.find crossing
    have ncross : 1 ≤ (2 : ℝ) ^ n * r := Nat.find_spec crossing
    have npos : 0 < n := by
      by_contra H
      have nz : n = 0 := by omega
      rw [nz, pow_zero, one_mul] at ncross
      linarith
    have prevlt : (2 : ℝ) ^ (n - 1) * r < 1 :=
      lt_of_not_ge (Nat.find_min crossing (show n - 1 < n by omega))
    have nsucc : n - 1 + 1 = n := by omega
    have prevge : 1 / 2 ≤ (2 : ℝ) ^ (n - 1) * r := by
      rw [← nsucc, pow_succ] at ncross
      nlinarith
    let d := B + n
    let a := B + (n - 1)
    let C : ℤ := (2 : ℤ) ^ (n - 1) * ⌊(2 : ℝ) ^ B * x⌋
    have da : d = a + 1 := by dsimp [d, a]; omega
    have expansion : (2 : ℝ) ^ a * x = (C : ℝ) + (2 : ℝ) ^ (n - 1) * r := by
      dsimp only [a, C, r, Int.fract]
      push_cast
      rw [pow_add]
      ring
    have floor_a : ⌊(2 : ℝ) ^ a * x⌋ = C := by
      apply Int.floor_eq_iff.mpr
      constructor <;> linarith [expansion]
    have floor_d : ⌊(2 : ℝ) ^ d * x⌋ = 2 * C + 1 := by
      apply Int.floor_eq_iff.mpr
      rw [da, pow_succ]
      push_cast
      constructor <;> nlinarith [expansion]
    have reduced_a : ⌊(2 : ℝ) ^ a * (x - 1 / (2 : ℝ) ^ d)⌋ = C := by
      apply Int.floor_eq_iff.mpr
      have scale : (2 : ℝ) ^ a * (x - 1 / (2 : ℝ) ^ d) =
          (2 : ℝ) ^ a * x - 1 / 2 := by
        rw [da, pow_succ]
        field_simp
      rw [scale]
      constructor <;> linarith [expansion]
    refine ⟨d, by dsimp [d]; omega, ?_, ?_⟩
    · rw [show d - 1 = a by omega, floor_d, floor_a]
      omega
    · intro h hh
      have ha : h ≤ a := by omega
      have divide (z : ℝ) :
          (2 : ℝ) ^ a * z / ((2 ^ (a - h) : ℕ) : ℝ) = (2 : ℝ) ^ h * z := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        have power : (2 : ℝ) ^ a = (2 : ℝ) ^ h * (2 : ℝ) ^ (a - h) := by
          rw [← pow_add, Nat.add_sub_of_le ha]
        rw [power]
        field_simp
      have H := Int.floor_div_natCast ((2 : ℝ) ^ a * (x - 1 / (2 : ℝ) ^ d))
        ((2 : ℕ) ^ (a - h))
      have H' := Int.floor_div_natCast ((2 : ℝ) ^ a * x) ((2 : ℕ) ^ (a - h))
      rw [divide, reduced_a] at H
      rw [divide, floor_a] at H'
      exact H.trans H'.symm
  have slope_lower (P : Fin m → ℝ) (hP : ∀ i, 0 < P i)
      (hS : ∑ i, P i = 1) (k : Fin m) (hk : ∀ i, P k ≤ P i) :
      alpha m * P k ≤ cost P := by
    obtain ⟨V, f, _, _, paths, _, zero, _⟩ := CarryGraphCriticalAttainment.result m hm
    obtain ⟨γ, hγ, _, _, _, ha, hc⟩ := (CarryGraphEmbedding.result m hm).2.2.2 P hP hS k hk
    have H := (paths (alpha m)).2.2 γ hγ
    rw [zero, ha, hc] at H
    linarith
  have attaining (n : ℕ) (hn : 0 < n) :
      ∃ (q : Fin n → ℝ) (l : Fin n), (∀ i, 0 < q i) ∧ (∑ i, q i) = 1 ∧
        (∀ i, q l ≤ q i) ∧ cost q = alpha n * q l := by
    by_cases h1 : n = 1
    · subst n
      refine ⟨fun _ => 1, 0, by norm_num, by simp, fun _ => le_rfl, ?_⟩
      rw [OptimalLawStrictSlope.result.1, zero_mul]
      have zeros (d : ℕ) : residual (fun _ : Fin 1 => (1 : ℝ)) d / (2 : ℝ) ^ d = 0 := by
        have integer_pow : ⌊(2 : ℝ) ^ d⌋ = (2 : ℤ) ^ d := by
          exact_mod_cast (Int.floor_intCast (R := ℝ) ((2 : ℤ) ^ d))
        simp [DyadicSupportLines.residual, integer_pow]
      simp only [cost, zeros, tsum_zero]
    · have hn2 : 2 ≤ n := by omega
      obtain ⟨V, f, _, _, _, _, _, H⟩ := CarryGraphCriticalAttainment.result n hn2
      dsimp only at H
      rcases H with ⟨ht, hq, hsum, hmin, _, _, _, _, hcost⟩
      let γ := CarryGraphCriticalAttainment.policyPath n (f (alpha n))
        ⟨CarryGraphEmbedding.root n, by
          dsimp [CarryGraphEmbedding.IsState, CarryGraphEmbedding.root]
          omega⟩
      let q : Fin n → ℝ := fun i => Real.ofDigits (CarryGraphRealization.labelDigit γ i)
      change (∀ i, 0 < q i) at hq
      change (∑ i, q i) = 1 at hsum
      change sInf (Set.range q) = CarryGraphEmbedding.anchorValue γ at hmin
      change cost q = alpha n * CarryGraphEmbedding.anchorValue γ at hcost
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      obtain ⟨l, hl⟩ := (Set.range_nonempty q).csInf_mem (Set.finite_range q)
      refine ⟨q, l, hq, hsum, ?_, ?_⟩
      · intro i
        rw [hl]
        exact csInf_le (Set.finite_range q).bddBelow ⟨i, rfl⟩
      · rw [hl, hmin]
        exact hcost
  have growth : StrictMono (fun n : ℕ => alpha (n + 1)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    by_cases hn : n = 0
    · subst n
      norm_num only [Nat.zero_add, Nat.reduceAdd, OptimalLawStrictSlope.result.1,
        OptimalLawStrictSlope.result.2.1]
    · simpa only [Nat.add_sub_cancel] using
        OptimalLawStrictSlope.result.2.2 (n + 1 + 1) (by omega)
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨k, hk0⟩ := (Set.range_nonempty p).csInf_mem (Set.finite_range p)
  have hk : ∀ i, p k ≤ p i := by
    intro i
    rw [hk0]
    exact csInf_le (Set.finite_range p).bddBelow ⟨i, rfl⟩
  let t := p k
  have hjt : t < p j := by dsimp only [t]; rwa [hk0]
  let I : Finset (Fin m) := Finset.univ.filter (fun i => p i = t)
  have memI (i : Fin m) : i ∈ I ↔ p i = t := by simp only [I, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have kI : k ∈ I := (memI k).mpr rfl
  have jI : j ∉ I := fun H => (ne_of_gt hjt) ((memI j).mp H)
  let e := I.card
  have epos : 0 < e := Finset.card_pos.mpr ⟨k, kI⟩
  have elt : e < m := by
    have H : I ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ I, fun h => jI (h.symm ▸ Finset.mem_univ j)⟩
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card H
  let enum : I ≃ Fin e := I.equivFin
  obtain ⟨q, l, hq, hsum, hlow, hcost⟩ := attaining e epos
  let u := q l
  let R : Fin m → ℝ := fun i => if hi : i ∈ I then q (enum ⟨i, hi⟩) else 0
  have hα : alpha e < alpha m := by
    convert growth (show e - 1 < m - 1 by omega) using 1 <;> congr 1 <;> omega
  let J := Finset.univ.filter (fun i : Fin m => i ∉ I)
  have jJ : j ∈ J := by simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]; exact jI
  obtain ⟨z, hz, hzmin⟩ := Finset.exists_min_image J (fun i => p i - t) ⟨j, jJ⟩
  let g := p z - t
  have gpos : 0 < g := by
    have hzI : z ∉ I := (Finset.mem_filter.mp hz).2
    have H := hk z
    have H' : p z ≠ t := fun eq => hzI ((memI z).mpr eq)
    dsimp only [g, t]
    exact sub_pos.mpr (lt_of_le_of_ne H (Ne.symm H'))
  have gap (i : Fin m) (hi : i ∉ I) : t + g ≤ p i := by
    have H := hzmin i (by simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)
    dsimp only [g]
    linarith
  have upos : 0 < u := hq l
  have tpos : 0 < t := hp k
  obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt ((1 + u) / g)
    (by norm_num : (1 : ℝ) < 2)
  obtain ⟨d, hd, _, shallow⟩ := deep (p j) (hp j) hnondyadic B
  let δ := 1 / (2 : ℝ) ^ d
  have δpos : 0 < δ := by dsimp only [δ]; positivity
  have δsmall : δ * (1 + u) < g := by
    have H := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd.le
    have H' : (1 + u) / g < (2 : ℝ) ^ d := hB.trans_le H
    have H'' := (div_lt_iff₀ gpos).mp H'
    calc
      _ = (1 + u) / (2 : ℝ) ^ d := by dsimp only [δ]; ring
      _ < g := (div_lt_iff₀ (by positivity)).mpr (by nlinarith only [H''])
  let P : Fin m → ℝ := fun i => p i + δ * R i - if i = j then δ else 0
  have lower (i : Fin m) : t + δ * u ≤ P i := by
    by_cases hi : i ∈ I
    · have nij : i ≠ j := fun H => jI (H ▸ hi)
      have H := hlow (enum ⟨i, hi⟩)
      dsimp only [P, R, u]
      rw [dif_pos hi, if_neg nij, sub_zero, (memI i).mp hi]
      linarith only [mul_le_mul_of_nonneg_left H δpos.le]
    · have H := gap i hi
      dsimp only [P, R]
      rw [dif_neg hi, mul_zero, add_zero]
      split_ifs <;> linarith
  have Ppos (i : Fin m) : 0 < P i := by
    have H := lower i
    have H' : 0 < δ * u := mul_pos δpos upos
    linarith
  obtain ⟨Psum, cost_bound⟩ := transfer m e p hs I enum q
    (fun i => (hq i).le) hsum j jI d shallow
  let receiver : I := enum.symm l
  have receiver_not_j : (receiver : Fin m) ≠ j := fun H => jI (H ▸ receiver.property)
  have receiver_mass : P receiver = t + δ * u := by
    dsimp only [P, R]
    rw [dif_pos receiver.property, if_neg receiver_not_j, sub_zero,
      (memI receiver).mp receiver.property]
    dsimp only [receiver]
    rw [Equiv.apply_symm_apply]
  have optimum : cost p = alpha m * t := by
    simpa only [← hk0] using hopt
  have contradicts := slope_lower P Ppos Psum receiver
    (fun i => receiver_mass ▸ lower i)
  have improvement : alpha m * t + δ * (alpha e * u) < alpha m * (t + δ * u) := by
    have H := mul_lt_mul_of_pos_right hα (mul_pos δpos upos)
    nlinarith only [H]
  rw [receiver_mass] at contradicts
  have bound : cost P ≤ alpha m * t + δ * (alpha e * u) := by
    simpa only [optimum, hcost] using cost_bound
  exact (not_lt_of_ge (contradicts.trans bound)) improvement

end D5.S3.Arith.FibonacciAtomic.OptimalLawLargerAtomsTerminate
