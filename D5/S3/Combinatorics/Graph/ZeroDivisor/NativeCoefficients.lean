/- GID: D5/S3/Combinatorics/Graph/ZeroDivisor/NativeCoefficients
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroDivisor/NativeCoefficients
   mirror-E: none(waiver:exact-native-coefficient-inequalities)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Cast]
   utility: none
   digest: Actual three-domain zero-divisor coefficients have exact support and strict interior log concavity. -/

import D5.S3.Combinatorics.Graph.ZeroDivisor.Support
import D5.S3.Combinatorics.Graph.ZeroDivisor.NormalizedCurvature

set_option autoImplicit false
noncomputable section
open scoped Classical
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

namespace D5.S3.Combinatorics.Graph.ZeroDivisor.NativeCoefficients

/-- Native coefficients for three ordered finite domains, including the smallest field. -/
set_option maxHeartbeats 1800000 in
theorem coefficients_three_domains
    {R : Type*} [CommRing R] [Fintype R]
    {L : Fin 3 → Type*} [∀ i, CommRing (L i)] [∀ i, NoZeroDivisors (L i)]
    [∀ i, Nontrivial (L i)] [∀ i, Fintype (L i)]
    (e : R ≃+* ∀ i, L i)
    (h01 : Fintype.card (L 0) ≤ Fintype.card (L 1))
    (h12 : Fintype.card (L 1) ≤ Fintype.card (L 2))
    (h1 : 3 ≤ Fintype.card (L 1)) (h2 : 5 ≤ Fintype.card (L 2)) :
    let a := Fintype.card (L 0) - 1
    let b := Fintype.card (L 1) - 1
    let c := Fintype.card (L 2) - 1
    let N := max (a*b+a*c+b*c) (c+a*c+b*c)
    let s := fun k => ((independencePolynomial (Support.graph R) Finset.univ).coeff k : ℚ)
    14 ≤ N ∧ (∀ k, k ≤ N → 0 < s k) ∧ (∀ k, N < k → s k = 0) ∧
      (∀ k, 1 ≤ k → k < N → s (k-1) * s (k+1) < s k ^ 2) := by
  classical
  let a := Fintype.card (L 0) - 1
  let b := Fintype.card (L 1) - 1
  let c := Fintype.card (L 2) - 1
  let A := a*b+a*c+b*c
  let T0 := a*b+a*c
  let T1 := a*b+b*c
  let T2 := a*c+b*c
  let U0 := a+a*b+a*c
  let U1 := b+a*b+b*c
  let U2 := c+a*c+b*c
  let N := max A U2
  let P := independencePolynomial (Support.graph R) Finset.univ
  let s := fun k => (P.coeff k : ℚ)
  change 14 ≤ N ∧ (∀ k, k ≤ N → 0 < s k) ∧ (∀ k, N < k → s k = 0) ∧ _
  have ha : 1 ≤ a := by
    have := Fintype.one_lt_card (α := L 0)
    dsimp [a]
    omega
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hc : 4 ≤ c := by dsimp [c]; omega
  have hab : a ≤ b := Nat.sub_le_sub_right h01 1
  have hbc : b ≤ c := Nat.sub_le_sub_right h12 1
  have hA : 14 ≤ A := by
    dsimp [A]
    nlinarith [Nat.mul_le_mul ha hb, Nat.mul_le_mul ha hc, Nat.mul_le_mul hb hc]
  have hN : 14 ≤ N := hA.trans (le_max_left _ _)
  have hU01 : U0 ≤ U1 := by
    have := Nat.mul_le_mul_left c hab
    dsimp [U0, U1]
    nlinarith
  have hU12 : U1 ≤ U2 := by
    have := Nat.mul_le_mul_left a hbc
    dsimp [U1, U2]
    omega
  have hAN : A ≤ N := le_max_left _ _
  have hU2N : U2 ≤ N := le_max_right _ _
  have hU1N : U1 ≤ N := hU12.trans hU2N
  have hU0N : U0 ≤ N := hU01.trans hU1N
  have hT0A : T0 ≤ A := by dsimp [T0, A]; omega
  have hT1A : T1 ≤ A := by dsimp [T1, A]; omega
  have hT2A : T2 ≤ A := by dsimp [T2, A]; omega
  have hT0U : T0 ≤ U0 := by dsimp [T0, U0]; omega
  have hT1U : T1 ≤ U1 := by dsimp [T1, U1]; omega
  have hT2U : T2 ≤ U2 := by dsimp [T2, U2]; omega
  have hpoly := Support.independencePolynomial_three_coordinates e
  have hs (k : ℕ) : s k = (A.choose k : ℚ) +
      ((U0.choose k : ℚ)-(T0.choose k : ℚ)) +
      ((U1.choose k : ℚ)-(T1.choose k : ℚ)) +
      ((U2.choose k : ℚ)-(T2.choose k : ℚ)) := by
    have h := congrArg (fun Q : Polynomial ℤ => (Q.coeff k : ℚ)) hpoly
    simpa only [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_one_add_X_pow, Int.cast_add, Int.cast_sub, Int.cast_natCast] using h
  have lower (k : ℕ) : (N.choose k : ℚ) ≤ s k := by
    have h0 : (T0.choose k : ℚ) ≤ U0.choose k := by
      exact_mod_cast Nat.choose_le_choose k hT0U
    have h1' : (T1.choose k : ℚ) ≤ U1.choose k := by
      exact_mod_cast Nat.choose_le_choose k hT1U
    by_cases hAU : U2 ≤ A
    · have hmax : N = A := max_eq_left hAU
      have h2' : (T2.choose k : ℚ) ≤ U2.choose k := by
        exact_mod_cast Nat.choose_le_choose k hT2U
      rw [hmax, hs]
      linarith
    · have hmax : N = U2 := max_eq_right (by omega)
      have h2' : (T2.choose k : ℚ) ≤ A.choose k := by
        exact_mod_cast Nat.choose_le_choose k hT2A
      rw [hmax, hs]
      linarith
  have pos (k : ℕ) (hk : k ≤ N) : 0 < s k :=
    lt_of_lt_of_le (by exact_mod_cast Nat.choose_pos hk) (lower k)
  have tail (k : ℕ) (hk : N < k) : s k = 0 := by
    rw [hs]
    simp [Nat.choose_eq_zero_of_lt (hAN.trans_lt hk),
      Nat.choose_eq_zero_of_lt (hU0N.trans_lt hk),
      Nat.choose_eq_zero_of_lt (hU1N.trans_lt hk),
      Nat.choose_eq_zero_of_lt (hU2N.trans_lt hk),
      Nat.choose_eq_zero_of_lt ((hT0A.trans hAN).trans_lt hk),
      Nat.choose_eq_zero_of_lt ((hT1A.trans hAN).trans_lt hk),
      Nat.choose_eq_zero_of_lt ((hT2A.trans hAN).trans_lt hk)]
  let v := A+a+b+c
  let E := A+3*a*b*c
  have hs0 : s 0 = 1 := by rw [hs]; norm_num
  have hs1 : s 1 = (v : ℚ) := by
    rw [hs]
    simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_mul]
    dsimp [v, A, U0, U1, U2, T0, T1, T2]
    push_cast
    ring
  have hs2 : s 2 = (v : ℚ)*((v : ℚ)-1)/2-(E : ℚ) := by
    rw [hs]
    simp only [Nat.cast_choose_two]
    dsimp [v, E, A, U0, U1, U2, T0, T1, T2]
    push_cast
    ring
  have hv : 21 ≤ v := by dsimp [v]; omega
  have count1 : (Fintype.card (Support.Vertex R) : ℚ) = s 1 := by
    have hsets : ((configurations (Support.graph R) Finset.univ).filter
        fun S => S.card = 1) =
        (Finset.univ : Finset (Support.Vertex R)).image (fun x => {x}) := by
      ext S
      simp only [Finset.mem_filter, configurations, Finset.mem_powerset,
        Finset.subset_univ, true_and, Finset.mem_image, Finset.mem_univ]
      constructor
      · rintro ⟨_, hS⟩
        obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hS
        exact ⟨x, trivial, rfl⟩
      · rintro ⟨x, _, rfl⟩
        simp [SimpleGraph.isIndepSet_iff]
    have hcount := Support.coefficient_card (R := R) Finset.univ 1
    rw [hsets, Finset.card_image_of_injective _ (by
      intro x y hxy
      simpa only [Finset.singleton_inj] using hxy), Finset.card_univ] at hcount
    exact_mod_cast hcount.symm
  have countcard : Fintype.card (Support.Vertex R) = v := by
    exact_mod_cast count1.trans hs1
  have hs3 : s 3 ≤ ((v.choose 3 : ℕ) : ℚ) := by
    have hsub : ((configurations (Support.graph R) Finset.univ).filter
        fun S => S.card = 3) ⊆
        (Finset.univ : Finset (Support.Vertex R)).powersetCard 3 := by
      intro S hS
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hS).2⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_powersetCard, Finset.card_univ, countcard] at hcard
    have hcount := Support.coefficient_card (R := R) Finset.univ 3
    have hcountQ : s 3 =
        (((configurations (Support.graph R) Finset.univ).filter
          fun S => S.card = 3).card : ℚ) := by exact_mod_cast hcount
    rw [hcountQ]
    exact_mod_cast hcard
  have density : 11*(E : ℚ) ≤ (v : ℚ)*((v : ℚ)-1) := by
    let x : ℚ := (a-1 : ℕ)
    let y : ℚ := (b-2 : ℕ)
    let z : ℚ := (c-4 : ℕ)
    have hx : 0 ≤ x := by positivity
    have hy : 0 ≤ y := by positivity
    have hz : 0 ≤ z := by positivity
    have hxx : 0 ≤ x^2-x := by
      have h : (a-1) ≤ (a-1)*(a-1) := Nat.le_mul_self _
      have h' : x ≤ x*x := by exact_mod_cast h
      nlinarith
    have hyy : 0 ≤ y^2-y := by
      have h : (b-2) ≤ (b-2)*(b-2) := Nat.le_mul_self _
      have h' : y ≤ y*y := by exact_mod_cast h
      nlinarith
    have hax : (a : ℚ) = x+1 := by dsimp [x]; rw [Nat.cast_sub ha]; ring
    have hby : (b : ℚ) = y+2 := by dsimp [y]; rw [Nat.cast_sub hb]; norm_num; ring
    have hcz : (c : ℚ) = z+4 := by dsimp [z]; rw [Nat.cast_sub hc]; norm_num; ring
    have hid : (v : ℚ)*((v : ℚ)-1)-11*(E : ℚ) =
        2+49*(x^2-x)+6*x+36*y^2+59*y+16*z^2+65*z+
        14*(x^2-x)*y+12*x*(y^2-y)+8*x*y+20*x*z+45*y*z+
        14*x^2*z+12*y^2*z+8*x*z^2+8*y*z^2+x*y*z+(x*y+x*z+y*z)^2 := by
      dsimp [v, E, A]
      push_cast
      rw [hax, hby, hcz]
      ring
    have hnon : 0 ≤ (v : ℚ)*((v : ℚ)-1)-11*(E : ℚ) := by
      rw [hid]
      positivity
    linarith
  have low1 : s 0*s 2 < s 1^2 := by
    rw [hs0, hs1, hs2]
    have hvQ : 21 ≤ (v : ℚ) := by exact_mod_cast hv
    have hE : 0 ≤ (E : ℚ) := by positivity
    nlinarith
  have low2 : s 1*s 3 < s 2^2 := by
    let C : ℚ := (v.choose 2 : ℕ)
    have hC : C = (v : ℚ)*((v : ℚ)-1)/2 := Nat.cast_choose_two v
    have hCpos : 0 < C := by dsimp [C]; exact_mod_cast Nat.choose_pos (by omega : 2 ≤ v)
    have h3 : (v.choose 3 : ℚ)*3 = (v.choose 2 : ℚ)*((v : ℚ)-2) := by
      have h := congrArg (fun n : ℕ => (n : ℚ)) (Nat.choose_succ_right_eq v 2)
      simpa [Nat.cast_sub (by omega : 2 ≤ v)] using h
    have hCv : (v : ℚ)*(v.choose 3 : ℚ) ≤ (2/3:ℚ)*C^2 := by
      have hvQ : 0 ≤ (v : ℚ) := by positivity
      have h3' : (v.choose 3 : ℚ) = C*((v : ℚ)-2)/3 := by
        dsimp [C]
        linarith [h3]
      have hdiff : (2/3:ℚ)*C^2-(v : ℚ)*(v.choose 3 : ℚ) = (v : ℚ)*C/3 := by
        rw [h3', hC]
        ring
      rw [← sub_nonneg]
      rw [hdiff]
      positivity
    have h2lower : (9/11:ℚ)*C ≤ s 2 := by rw [hs2]; rw [hC]; linarith
    have h2sq : (9/11:ℚ)^2*C^2 ≤ s 2^2 := by
      have hs2pos := pos 2 (by omega)
      nlinarith [h2lower]
    have h3upper : s 1*s 3 ≤ (2/3:ℚ)*C^2 := by
      rw [hs1]
      exact (mul_le_mul_of_nonneg_left hs3 (by positivity)).trans hCv
    nlinarith [sq_pos_of_pos hCpos]
  refine ⟨hN, pos, tail, ?_⟩
  intro k hk hkN
  by_cases hk1 : k = 1
  · subst k
    simpa using low1
  by_cases hk2 : k = 2
  · subst k
    simpa using low2
  have hk3 : 3 ≤ k := by omega
  let B := fun j => (N.choose j : ℚ)
  let f := fun j => s j / B j
  let D := fun m => (m.choose (k-1) : ℚ)/B (k-1) -
    2*((m.choose k : ℚ)/B k)+(m.choose (k+1) : ℚ)/B (k+1)
  have hB (j : ℕ) (hj : j ≤ N) : 0 < B j := by
    dsimp [B]
    exact_mod_cast Nat.choose_pos hj
  have hf (j : ℕ) (hj : j ≤ N) : 1 ≤ f j := by
    apply (le_div_iff₀ (hB j hj)).mpr
    simpa only [one_mul] using lower j
  have hDN : D N = 0 := by
    dsimp [D]
    simp only [show (N.choose (k-1) : ℚ) = B (k-1) from rfl,
      show (N.choose k : ℚ) = B k from rfl,
      show (N.choose (k+1) : ℚ) = B (k+1) from rfl,
      div_self (ne_of_gt (hB (k-1) (by omega))),
      div_self (ne_of_gt (hB k (by omega))),
      div_self (ne_of_gt (hB (k+1) (by omega)))]
    norm_num
  have hDnon (m : ℕ) (hm : m ≤ N) : 0 ≤ D m := by
    dsimp [D, B]
    rw [NormalizedCurvature.normalized_second_difference N m k hm hk hkN]
    positivity
  have hDbd (m : ℕ) (hm : m ≤ N) : D m ≤ 1/(3*((k : ℚ)+1)) :=
    NormalizedCurvature.normalized_second_difference_bound N m k (by omega) hm hk3 hkN
  have hdecomp : f (k-1)-2*f k+f (k+1) =
      D A+D U0+D U1+D U2-D T0-D T1-D T2 := by
    dsimp only [f]
    rw [hs (k-1), hs k, hs (k+1)]
    dsimp [D]
    ring
  have hthird : 3*(1/(3*((k : ℚ)+1))) = 1/((k : ℚ)+1) := by ring
  have curv : f (k-1)-2*f k+f (k+1) ≤ 1/((k : ℚ)+1) := by
    rw [hdecomp]
    have h0 := hDnon T0 (hT0A.trans hAN)
    have h1' := hDnon T1 (hT1A.trans hAN)
    have h2' := hDnon T2 (hT2A.trans hAN)
    by_cases hAU : U2 ≤ A
    · have hmax : N = A := max_eq_left hAU
      have hDA : D A = 0 := hmax ▸ hDN
      linarith [hDbd U0 hU0N, hDbd U1 hU1N, hDbd U2 hU2N]
    · have hmax : N = U2 := max_eq_right (by omega)
      have hDU : D U2 = 0 := hmax ▸ hDN
      linarith [hDbd A hAN, hDbd U0 hU0N, hDbd U1 hU1N]
  let x := f (k-1)
  let y := f k
  let z := f (k+1)
  let t := (k : ℚ)+1
  have hx : 1 ≤ x := hf _ (by omega)
  have hy : 1 ≤ y := hf _ (by omega)
  have hz : 1 ≤ z := hf _ (by omega)
  have ht : 0 < t := by dsimp [t]; positivity
  have hkQ : 0 ≤ (k : ℚ) := by positivity
  have hsum : t*(x+z) ≤ 2*t*y+1 := by
    have h := (le_div_iff₀ ht).mp curv
    dsimp only [x, y, z, t] at *
    nlinarith
  have hsumpos : 0 ≤ t*(x+z) := by positivity
  have hsquare : (t*(x+z))^2 ≤ (2*t*y+1)^2 := by
    nlinarith [mul_self_le_mul_self hsumpos hsum]
  have hfour : 4*t^2*x*z ≤ (2*t*y+1)^2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (x-z))]
  have hfourk := mul_le_mul_of_nonneg_left hfour hkQ
  have hysq : 0 ≤ y^2-y := by nlinarith
  have hslack : 0 < 4*t^3*y^2-(k : ℚ)*(2*t*y+1)^2 := by
    have hid : 4*t^3*y^2-(k : ℚ)*(2*t*y+1)^2 =
        4*t^2*(y^2-y)+4*t*(y-1)+3*(k : ℚ)+4 := by dsimp [t]; ring
    rw [hid]
    positivity
  have hscalar : (k : ℚ)*x*z < t*y^2 := by
    have hm : 0 < 4*t^2*(t*y^2-(k : ℚ)*x*z) := by nlinarith [hfourk, hslack]
    by_contra hn
    have hh : 4*t^2*(t*y^2-(k : ℚ)*x*z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  have hprev := congrArg (fun n : ℕ => (n : ℚ)) (Nat.choose_succ_right_eq N (k-1))
  have hnext := congrArg (fun n : ℕ => (n : ℚ)) (Nat.choose_succ_right_eq N k)
  simp only [Nat.sub_add_cancel hk, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub (by omega : k-1 ≤ N), Nat.cast_sub hk, Nat.cast_sub (by omega : k ≤ N)] at hprev hnext
  have hbinid : t*B (k-1)*B (k+1)+B (k-1)*B k = (k : ℚ)*B k^2 := by
    dsimp [t, B]
    linear_combination (N.choose (k-1) : ℚ)*hnext-(N.choose k : ℚ)*hprev
  have hbin : t*B (k-1)*B (k+1) ≤ (k : ℚ)*B k^2 := by
    nlinarith [mul_nonneg (hB (k-1) (by omega)).le (hB k (by omega)).le]
  have hsB (j : ℕ) (hj : j ≤ N) : s j = f j*B j := by
    dsimp [f]
    exact (div_mul_cancel₀ _ (ne_of_gt (hB j hj))).symm
  have hscaled : t*(s (k-1)*s (k+1)) < t*(s k)^2 := by
    rw [hsB (k-1) (by omega), hsB (k+1) (by omega), hsB k (by omega)]
    change t*(x*B (k-1)*(z*B (k+1))) < t*(y*B k)^2
    have hmul := mul_le_mul_of_nonneg_right hbin (mul_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ z))
    have hstrict := mul_lt_mul_of_pos_right hscalar (sq_pos_of_pos (hB k (by omega)))
    nlinarith [hmul, hstrict]
  exact (mul_lt_mul_iff_right₀ ht).mp hscaled

end D5.S3.Combinatorics.Graph.ZeroDivisor.NativeCoefficients
