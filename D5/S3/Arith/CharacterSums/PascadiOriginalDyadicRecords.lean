/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalDyadicRecords
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalDyadicRecords
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Actual physical dyadic scales give the global retained large-fiber moment. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalGoodRecordMoment
import D5.S3.Arith.CharacterSums.PascadiOriginalWeightAverage

/-! The physical basis supplies each coordinate box. Neither coordinate heights
nor a count of scales is assumed in the resulting second-moment estimate. -/

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem integer_abs_one {z : ℤ} (hz : z ≠ 0) : 1 ≤ |(z : ℝ)| := by
  have hh : (1 : ℤ) ≤ |z| := by have := abs_pos.mpr hz; omega
  exact_mod_cast hh

/-- Sum the large-fiber second moment over all actual physical dyadic scales.
The original integer parameter, reduced-basis witness and original word are
retained. The coordinate bounds and logarithmic number of scales are proved. -/
theorem actual_dyadic_large_second_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y H : ℝ)
      (a₁ a₂ : ZMod (p^3)) (q : Coordinate → Coordinate)
      (RV : Coordinate → Coordinate × Coordinate)
      (s : Finset Coordinate) (E : Coordinate → Finset Endpoint),
      0 < X → X ≤ Y → 3*Y < (p : ℝ)^2 → 0 < H → H^2 = X*Y →
      IsUnit a₁ → IsUnit a₂ →
      (∀ wt ∈ s, wt ∈ literalBox X Y) →
      (∀ wt ∈ s, ∃ B : ReducedMiddleBasis (p^3) wt.2 wt.1 X Y,
        B.R = (RV wt).1 ∧ B.V = (RV wt).2) →
      (∀ wt ∈ s, physical (RV wt).1 (RV wt).2 (q wt) = -wt) →
      (∀ wt ∈ s, (p^3 : ℝ)^2 < (X*Y)*weightedSq X Y (RV wt).1) →
      (∀ wt ∈ s, IsUnit ((RV wt).1.1 : ZMod (p^3))) →
      (∀ wt ∈ s, IsUnit (wt.2 : ZMod (p^3)) ∧ IsUnit (wt.1 : ZMod (p^3))) →
      (∀ wt ∈ s, ∀ e ∈ E wt, WordSolution (p^3) a₁ a₂ (RV wt).1 (RV wt).2 (q wt) e) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        IsUnit ((physical (RV wt).1 (RV wt).2 e.1).1 : ZMod (p^3)) ∧
        IsUnit ((physical (RV wt).1 (RV wt).2 e.2).1 : ZMod (p^3))) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        physical (RV wt).1 (RV wt).2 e.1 ∈ literalBox X Y ∧
        physical (RV wt).1 (RV wt).2 e.2 ∈ literalBox X Y) →
      (∀ wt ∈ s, 2 * actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) ≤
        (E wt).card) →
      (∑ wt ∈ s, ((E wt).card : ℝ)^2) ≤
        C*(p : ℝ)^ε*(X*Y/(p : ℝ)^3)^5*(1+Real.log (2*p)/Real.log 2) := by
  classical
  obtain ⟨C, hC, hmoment⟩ := actual_large_retained_second_moment ε hε
  refine ⟨2*288^5*C, by positivity, ?_⟩
  intro p hp X Y H a₁ a₂ q RV s E hX hXY hsmall hH hHsq ha₁ ha₂
    hsbox hred hanchor hlong hr hunit hword heunit hebox hlarge
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : Fact (1 < p^3) := ⟨one_lt_pow₀ hp.one_lt (by decide : 3 ≠ 0)⟩
  have hY : 0 < Y := hX.trans_le hXY
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hc : 0 < p^3 := pow_pos hp.pos _
  let Q := fun wt => weightedSq X Y (RV wt).1
  let T : ℝ := 2*(p : ℝ)^2
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  obtain ⟨N, hNlow, hNhigh⟩ := exists_nat_pow_near hT (by norm_num : (1 : ℝ) < 2)
  let P := fun k wt => ((2 : ℝ)^k)^2 ≤ Q wt ∧ Q wt < 4*((2 : ℝ)^k)^2
  let S := fun k => s.filter (P k)
  have hnorm (wt : Coordinate) (hw : wt ∈ s) :
      1 ≤ Real.sqrt (Q wt) ∧ Real.sqrt (Q wt) ≤ T := by
    obtain ⟨B, hBR, hBV⟩ := hred wt hw
    have hR₁ : (RV wt).1.1 ≠ 0 := by
      intro hz
      exact (hr wt hw).ne_zero (by simp only [hz, Int.cast_zero])
    have hR₂ : (RV wt).1.2 ≠ 0 := by
      intro hz
      have hm := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr B.memR
      rw [hBR] at hm
      push_cast at hm
      have hu := (hunit wt hw).1.mul (hr wt hw)
      apply hu.ne_zero
      simpa only [hz, Int.cast_zero, mul_zero, zero_sub, neg_eq_zero] using hm
    have hprod : 1 ≤ |((RV wt).1.1 : ℝ)| * |((RV wt).1.2 : ℝ)| := by
      simpa only [one_mul] using mul_le_mul (integer_abs_one hR₁)
        (integer_abs_one hR₂) (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg _)
    have hQ0 : 0 ≤ Q wt := weightedSq_nonneg hX hY _
    have hQ : Q wt < 2*(p : ℝ)^3 := by
      simpa only [Q, hBR, Nat.cast_pow] using (B.reduction_bounds hc hX hY).2.1
    have hpow : (p : ℝ)^3 ≤ (p : ℝ)^4 := pow_le_pow_right₀ hp1 (by decide : 3 ≤ 4)
    constructor
    · apply Real.le_sqrt_of_sq_le
      have hh := two_abs_product_le_weightedSq hX hY (RV wt).1
      dsimp [Q]
      nlinarith
    · apply (Real.sqrt_le_iff).mpr
      refine ⟨by dsimp [T]; positivity, ?_⟩
      dsimp [T]
      nlinarith [pow_nonneg hpR.le 4]
  have hcover (wt : Coordinate) (hw : wt ∈ s) :
      ((E wt).card : ℝ)^2 ≤ ∑ k ∈ Finset.range (N+1),
        if P k wt then ((E wt).card : ℝ)^2 else 0 := by
    obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near (hnorm wt hw).1
      (by norm_num : (1 : ℝ) < 2)
    have hk : k < N+1 := by
      apply (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      exact hklo.trans_lt ((hnorm wt hw).2.trans_lt hNhigh)
    have hPk : P k wt := by
      have hsq := Real.sq_sqrt (weightedSq_nonneg hX hY (RV wt).1)
      have hlo := (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg (Q wt))).mpr hklo
      have hhi := (sq_lt_sq₀ (Real.sqrt_nonneg (Q wt)) (by positivity)).mpr hkhi
      rw [show (2 : ℝ)^(k+1) = (2 : ℝ)^k * 2 by rw [pow_succ]] at hhi
      dsimp [P]
      change (Real.sqrt (Q wt))^2 = Q wt at hsq
      constructor <;> nlinarith
    have hh := Finset.single_le_sum
      (f := fun j => if P j wt then ((E wt).card : ℝ)^2 else 0)
      (fun _ _ => by split <;> positivity) (Finset.mem_range.mpr hk)
    simpa only [if_pos hPk] using hh
  have hscale (k : ℕ) : (∑ wt ∈ S k, ((E wt).card : ℝ)^2) ≤
      C*(p : ℝ)^ε*288^5*(X*Y/(p : ℝ)^3)^5 := by
    by_cases hne : (S k).Nonempty
    · obtain ⟨wt₀, hw₀⟩ := hne
      obtain ⟨hs₀, hscale₀⟩ := Finset.mem_filter.mp hw₀
      obtain ⟨B₀, hR₀, hV₀⟩ := hred wt₀ hs₀
      let J₁ := 8*H/(2 : ℝ)^k
      let J₂ := 4*H*(2 : ℝ)^k/(p : ℝ)^3
      have hscaleB₀ : ((2 : ℝ)^k)^2 ≤ weightedSq X Y B₀.R ∧
          weightedSq X Y B₀.R < 4*((2 : ℝ)^k)^2 := by simpa only [Q, hR₀] using hscale₀
      have hlongB₀ : ((p^3 : ℕ) : ℝ)^2 < H^2*weightedSq X Y B₀.R := by
        rw [hHsq, hR₀]
        simpa only [Nat.cast_pow] using hlong wt₀ hs₀
      obtain ⟨horder, hJ₂, hprod, _⟩ := B₀.long_scale_bounds hc hX hY H ((2 : ℝ)^k)
        hH hHsq (by positivity) hscaleB₀.1 hscaleB₀.2 hlongB₀
      have hJ₂'' : 2 < J₂ := by simpa only [J₂, Nat.cast_pow] using hJ₂
      have hJ₂' : 1 ≤ J₂ := by linarith
      have horder' : J₂ ≤ J₁ := by simpa only [J₁, J₂, Nat.cast_pow] using horder
      have hJ₁ : 1 ≤ J₁ := hJ₂'.trans horder'
      have hprod' : J₁*J₂ = 32*(X*Y/(p : ℝ)^3) := by
        simpa only [J₁, J₂, Nat.cast_pow] using hprod
      have hrestrict {A : Coordinate → Prop} (h : ∀ wt ∈ s, A wt) : ∀ wt ∈ S k, A wt :=
        fun wt hw => h wt (Finset.mem_filter.mp hw).1
      have hcoord (wt : Coordinate) (hw : wt ∈ S k) (z : Coordinate)
          (hz : physical (RV wt).1 (RV wt).2 z ∈ literalBox X Y) : CoordinateBound J₁ J₂ z := by
        obtain ⟨hs, hsk⟩ := Finset.mem_filter.mp hw
        obtain ⟨B, hBR, hBV⟩ := hred wt hs
        have hlo : ((2 : ℝ)^k)^2 ≤ weightedSq X Y B.R := by
          simpa only [Q, hBR] using hsk.1
        have hhi : weightedSq X Y B.R < 4*((2 : ℝ)^k)^2 := by
          simpa only [Q, hBR] using hsk.2
        have hzB : physical B.R B.V z ∈ literalBox X Y := by
          simpa only [hBR, hBV] using hz
        simpa only [J₁, J₂, Nat.cast_pow] using
          B.coordinate_bound hc hX hY H ((2 : ℝ)^k) hH hHsq (by positivity) hlo hhi z hzB
      have hqbound : ∀ wt ∈ S k, CoordinateBound J₁ J₂ (q wt) := by
        intro wt hw
        apply hcoord wt hw
        rw [hanchor wt (Finset.mem_filter.mp hw).1]
        simpa only [literalBox, Set.mem_setOf_eq, Prod.fst_neg, Prod.snd_neg,
          Int.cast_neg, abs_neg] using
          hsbox wt (Finset.mem_filter.mp hw).1
      have hebound : ∀ wt ∈ S k, ∀ e ∈ E wt,
          CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2 := by
        intro wt hw e he
        exact ⟨hcoord wt hw _ (hebox wt (Finset.mem_filter.mp hw).1 e he).1,
          hcoord wt hw _ (hebox wt (Finset.mem_filter.mp hw).1 e he).2⟩
      have hh := hmoment p hp X Y J₁ J₂ a₁ a₂ q RV (S k) E hX hXY hsmall
        hJ₁ hJ₂' ha₁ ha₂ (hrestrict hred) (hrestrict hanchor) (hrestrict hlong)
        (hrestrict hr) (hrestrict (fun wt hw => (hunit wt hw).1))
        (hrestrict hword) (hrestrict heunit) hqbound hebound (hrestrict hlarge)
      calc
        _ ≤ C*(p : ℝ)^ε*(9*J₁*J₂)^5 := hh
        _ = _ := by rw [show 9*J₁*J₂ = 9*(J₁*J₂) by ring, hprod']; ring
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hlogN : (N : ℝ)*Real.log 2 ≤ Real.log 2+2*Real.log (p : ℝ) := by
    have hh := Real.log_le_log (by positivity : 0 < (2 : ℝ)^N) hNlow
    simpa only [Real.log_pow, T, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (pow_ne_zero 2 hpR.ne'), Real.log_pow, Nat.cast_ofNat] using hh
  have hNcount : ((N+1 : ℕ) : ℝ) ≤ 2*(1+Real.log (2*p)/Real.log 2) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpR.ne']
    apply (mul_le_mul_iff_of_pos_right hlog2).mp
    push_cast
    field_simp
    nlinarith
  calc
    _ ≤ ∑ wt ∈ s, ∑ k ∈ Finset.range (N+1),
        if P k wt then ((E wt).card : ℝ)^2 else 0 := Finset.sum_le_sum hcover
    _ = ∑ k ∈ Finset.range (N+1), ∑ wt ∈ S k, ((E wt).card : ℝ)^2 := by
      rw [Finset.sum_comm]
      simp only [S, Finset.sum_filter]
    _ ≤ ∑ _k ∈ Finset.range (N+1), C*(p : ℝ)^ε*288^5*(X*Y/(p : ℝ)^3)^5 :=
      Finset.sum_le_sum fun k _ => hscale k
    _ = ((N+1 : ℕ) : ℝ)*(C*(p : ℝ)^ε*288^5*(X*Y/(p : ℝ)^3)^5) := by simp
    _ ≤ (2*(1+Real.log (2*p)/Real.log 2))*(C*(p : ℝ)^ε*288^5*(X*Y/(p : ℝ)^3)^5) :=
      mul_le_mul_of_nonneg_right hNcount (by positivity)
    _ = (2*288^5*C)*(p : ℝ)^ε*(X*Y/(p : ℝ)^3)^5*
        (1+Real.log (2*p)/Real.log 2) := by ring

/-- The global retained endpoint count, with all physical scales summed and
without a lower bound on fiber sizes. Small fibers pay their actual bad degree
once, while the remaining actual incidences satisfy Cauchy--Schwarz. -/
theorem actual_dyadic_retained_endpoint_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y H : ℝ)
      (a₁ a₂ : ZMod (p^3)) (q : Coordinate → Coordinate)
      (RV : Coordinate → Coordinate × Coordinate)
      (s : Finset Coordinate) (E : Coordinate → Finset Endpoint),
      0 < X → X ≤ Y → 3*Y < (p : ℝ)^2 → 0 < H → H^2 = X*Y →
      IsUnit a₁ → IsUnit a₂ →
      (∀ wt ∈ s, wt ∈ literalBox X Y) →
      (∀ wt ∈ s, ∃ B : ReducedMiddleBasis (p^3) wt.2 wt.1 X Y,
        B.R = (RV wt).1 ∧ B.V = (RV wt).2) →
      (∀ wt ∈ s, physical (RV wt).1 (RV wt).2 (q wt) = -wt) →
      (∀ wt ∈ s, (p^3 : ℝ)^2 < (X*Y)*weightedSq X Y (RV wt).1) →
      (∀ wt ∈ s, IsUnit ((RV wt).1.1 : ZMod (p^3))) →
      (∀ wt ∈ s, IsUnit (wt.2 : ZMod (p^3)) ∧ IsUnit (wt.1 : ZMod (p^3))) →
      (∀ wt ∈ s, ∀ e ∈ E wt, WordSolution (p^3) a₁ a₂ (RV wt).1 (RV wt).2 (q wt) e) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        IsUnit ((physical (RV wt).1 (RV wt).2 e.1).1 : ZMod (p^3)) ∧
        IsUnit ((physical (RV wt).1 (RV wt).2 e.2).1 : ZMod (p^3))) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        physical (RV wt).1 (RV wt).2 e.1 ∈ literalBox X Y ∧
        physical (RV wt).1 (RV wt).2 e.2 ∈ literalBox X Y) →
      (∑ wt ∈ s, ((E wt).card : ℝ)) ≤
        2*(∑ wt ∈ s,
          (actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) : ℝ)) +
        Real.sqrt ((s.card : ℝ)*C*(p : ℝ)^ε*(X*Y/(p : ℝ)^3)^5*
          (1+Real.log (2*p)/Real.log 2)) := by
  classical
  obtain ⟨C, hC, hmoment⟩ := actual_dyadic_large_second_moment ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp X Y H a₁ a₂ q RV s E hX hXY hYsmall hH hHsq ha₁ ha₂
    hsbox hred hanchor hlong hr hunit hword heunit hebox
  let D := fun wt => actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt)
  let L := s.filter fun wt => 2*D wt ≤ (E wt).card
  let S := s.filter fun wt => ¬ 2*D wt ≤ (E wt).card
  have hrestrict {P : Coordinate → Prop} (h : ∀ wt ∈ s, P wt) : ∀ wt ∈ L, P wt :=
    fun wt hw => h wt (Finset.mem_filter.mp hw).1
  have hsecond : (∑ wt ∈ L, ((E wt).card : ℝ)^2) ≤
      C*(p : ℝ)^ε*(X*Y/(p : ℝ)^3)^5*(1+Real.log (2*p)/Real.log 2) :=
    hmoment p hp X Y H a₁ a₂ q RV L E hX hXY hYsmall hH hHsq ha₁ ha₂
      (hrestrict hsbox) (hrestrict hred) (hrestrict hanchor) (hrestrict hlong)
      (hrestrict hr) (hrestrict hunit) (hrestrict hword) (hrestrict heunit)
      (hrestrict hebox) (fun wt hw => (Finset.mem_filter.mp hw).2)
  have hcauchy : (∑ wt ∈ L, ((E wt).card : ℝ))^2 ≤
      (L.card : ℝ)*(∑ wt ∈ L, ((E wt).card : ℝ)^2) := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq L (fun _ => (1 : ℝ)) (fun wt => ((E wt).card : ℝ))
  have hcard : (L.card : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Finset.card_filter_le s (fun wt => 2*D wt ≤ (E wt).card)
  have hroot : (∑ wt ∈ L, ((E wt).card : ℝ)) ≤
      Real.sqrt ((s.card : ℝ)*C*(p : ℝ)^ε*(X*Y/(p : ℝ)^3)^5*
        (1+Real.log (2*p)/Real.log 2)) := by
    apply Real.le_sqrt_of_sq_le
    calc
      _ ≤ (L.card : ℝ)*(∑ wt ∈ L, ((E wt).card : ℝ)^2) := hcauchy
      _ ≤ (s.card : ℝ)*(C*(p : ℝ)^ε*(X*Y/(p : ℝ)^3)^5*
          (1+Real.log (2*p)/Real.log 2)) :=
        mul_le_mul hcard hsecond (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          (Nat.cast_nonneg _)
      _ = _ := by simp only [mul_assoc]
  have hsmall : (∑ wt ∈ S, ((E wt).card : ℝ)) ≤ 2*(∑ wt ∈ s, (D wt : ℝ)) := by
    calc
      _ ≤ ∑ wt ∈ S, 2*(D wt : ℝ) := by
        apply Finset.sum_le_sum
        intro wt hw
        have hh := (Finset.mem_filter.mp hw).2
        exact_mod_cast (show (E wt).card ≤ 2*D wt by omega)
      _ ≤ ∑ wt ∈ s, 2*(D wt : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hsplit : (∑ wt ∈ s, ((E wt).card : ℝ)) =
      (∑ wt ∈ L, ((E wt).card : ℝ))+(∑ wt ∈ S, ((E wt).card : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not s _ _).symm
  rw [hsplit]
  exact (add_le_add hroot hsmall).trans_eq (add_comm _ _)

end
end D5.S3.Arith.CharacterSums.Original
