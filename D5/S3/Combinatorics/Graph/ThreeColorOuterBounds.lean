/- GID: D5/S3/Combinatorics/Graph/ThreeColorOuterBounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ThreeColorOuterBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Order.BigOperators.Ring.Finset]
   utility: none
   digest: Unbounded reciprocal estimates for the outer mixed populations. -/

import D5.S3.Combinatorics.Graph.ThreeColorIncidence

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ThreeColorOuterBounds

open Finset
open D5.S3.Combinatorics.Graph.ThreeColorReciprocal

/-- With zero or one mixed vertex, the attachment expression is at least two
unless an ordinary side is a singleton with no third-color population. -/
theorem low_population (k a b c d e f : ℕ) (hk : k ≤ 1)
    (hab : a = 0 → b ≤ k) (hba : b = 0 → k + a = 0)
    (hcd : c = 0 → d ≤ k) (hdc : d = 0 → k + c = 0)
    (hef : e = 0 ↔ f = 0) :
    (2 : ℚ) ≤
      1 / ((k + a + c : ℕ) + 1 : ℚ) + 1 / ((b + e : ℕ) + 1 : ℚ) +
      1 / ((d + f : ℕ) + 1 : ℚ) + (k : ℚ) / 6 +
      ((a : ℚ) / (b + 1) + (b : ℚ) / (a + 1) +
       (c : ℚ) / (d + 1) + (d : ℚ) / (c + 1) +
       (e : ℚ) / (f + 1) + (f : ℚ) / (e + 1)) / 2 -
      (k : ℚ) / 2 * (1 / (((a : ℚ) + 1) * (a + 2)) +
        1 / (((c : ℚ) + 1) * (c + 2))) ∨
      (k = 1 ∧ (a = 0 ∨ c = 0) ∧ e = 0 ∧ f = 0) := by
  let r (n : ℕ) : ℚ := 1 / ((n : ℚ) + 1)
  let g (n : ℕ) : ℚ := 1 / (((n : ℚ) + 1) * (n + 2))
  let Q (a b : ℕ) : ℚ := ((a : ℚ) / (b + 1) + (b : ℚ) / (a + 1)) / 2
  let L (k a b c d e f : ℕ) : ℚ :=
    r (k+a+c) + r (b+e) + r (d+f) + (k : ℚ)/6 +
      Q a b + Q c d + Q e f - (k : ℚ)/2*(g a+g c)
  suffices (2 : ℚ) ≤ L k a b c d e f ∨
      (k = 1 ∧ (a = 0 ∨ c = 0) ∧ e = 0 ∧ f = 0) by
    convert this using 1 <;> dsimp [L, r, Q, g] <;> push_cast <;> ring
  have rp (n : ℕ) : 0 ≤ r n := by dsimp [r]; positivity
  have pair (a b : ℕ) : 1 ≤ Q a b + r b := by
    have hh : 0 ≤ ((a : ℚ) - b) * ((a : ℚ) - b + 1) := by
      by_cases h : b ≤ a
      · have h' : (b : ℚ) ≤ a := by exact_mod_cast h
        exact mul_nonneg (by linarith) (by linarith)
      · have h' : (a : ℚ) + 1 ≤ b := by exact_mod_cast (show a+1 ≤ b by omega)
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    dsimp [Q, r]
    apply (le_of_mul_le_mul_left (a := 2*((a : ℚ)+1)*((b : ℚ)+1)) ?_ (by positivity))
    field_simp
    nlinarith only [hh]
  have pair' (a b : ℕ) : 1 ≤ Q a b + r a := by
    simpa only [Q, add_comm] using pair b a
  have gb (a : ℕ) (ha : 1 ≤ a) : g a ≤ 1/6 := by
    have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
    dsimp [g]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < ((a : ℚ)+1)*(a+2))).mpr
    nlinarith
  have step (a : ℕ) : r (a+1) = r a - g a := by
    dsimp [r,g]; push_cast; field_simp; ring
  have symm (k a b c d e f : ℕ) : L k a b c d e f = L k c d a b f e := by
    dsimp [L, Q]
    rw [show k+a+c=k+c+a by omega]
    ring
  have thin (c d e f : ℕ) (hc : c=0 → d=1) (he : 1 ≤ e) :
      2 ≤ L 1 0 1 c d e f := by
    have pe := pair' e f
    have ge := gb e he
    have se := step e
    have ident : L 1 0 1 c d e f = 5/12 + r (c+1) + r (e+1) +
        r (d+f) + Q c d + Q e f - g c/2 := by
      dsimp [L,Q,r,g]; push_cast; ring
    rw [ident]
    by_cases hz : c = 0
    · have hd := hc hz
      subst c; subst d
      have hf := rp (1+f)
      norm_num only [zero_add, show r 1 = 1/2 by norm_num [r],
        show Q 0 1 = 1/2 by norm_num [Q], show g 0 = 1/2 by norm_num [g]]
      linarith only [pe, ge, se, hf]
    · have pc := pair' c d
      have gc := gb c (by omega)
      have hf := rp (d+f)
      have sc := step c
      linarith only [pe, ge, se, pc, gc, hf, sc]
  by_cases he : e = 0
  · have hf := hef.mp he
    subst e; subst f
    by_cases hzero : k = 0
    · left
      have p := pair a b
      have q := pair c d
      have h := rp (a+c)
      subst k
      simpa [L, Q] using (show 2 ≤ r (a+c)+r b+r d+Q a b+Q c d by linarith)
    · have hk1 : k=1 := by omega
      by_cases ha : a=0
      · exact Or.inr ⟨hk1, Or.inl ha, rfl, rfl⟩
      by_cases hc : c=0
      · exact Or.inr ⟨hk1, Or.inr hc, rfl, rfl⟩
      left
      have p := pair a b
      have q := pair c d
      have ga := gb a (by omega)
      have gc := gb c (by omega)
      have h := rp (1+a+c)
      subst k
      dsimp [L]
      norm_num [Q] at *
      linarith
  have he1 : 1 ≤ e := by omega
  have hf1 : 1 ≤ f := by by_contra h; exact he (hef.mpr (by omega))
  left
  by_cases ha : a=0
  · by_cases hzero : k=0
    · have hb : b=0 := by have := hab ha; omega
      subst k; subst a; subst b
      have p := pair' c d
      have q := pair' e f
      have h := rp (d+f)
      simpa [L, Q] using (show 2 ≤ r c+r e+r (d+f)+Q c d+Q e f by linarith)
    · have hk1 : k=1 := by omega
      have hb : b=1 := by have := hab ha; have := hba; omega
      subst k; subst a; subst b
      exact thin c d e f (fun hc => by have := hcd hc; have := hdc; omega) he1
  by_cases hc : c=0
  · rw [symm]
    by_cases hzero : k=0
    · have hd : d=0 := by have := hcd hc; omega
      subst k; subst c; subst d
      have p := pair' a b
      have q := pair' f e
      have h := rp (b+e)
      simpa [L, Q] using (show 2 ≤ r a+r f+r (b+e)+Q a b+Q f e by linarith)
    · have hk1 : k=1 := by omega
      have hd : d=1 := by have := hcd hc; have := hdc; omega
      subst k; subst c; subst d
      exact thin a b f e (fun ha => by have := hab ha; have := hba; omega) hf1
  have ha1 : 1 ≤ a := by omega
  have hc1 : 1 ≤ c := by omega
  have hb1 : 1 ≤ b := by by_contra h; have := hba (by omega); omega
  have hd1 : 1 ≤ d := by by_contra h; have := hdc (by omega); omega
  have cls (i a b : ℕ) (hi : i ≤ 1) (ha : 1 ≤ a) (hb : 1 ≤ b) :
      -(1/4 : ℚ) - (i : ℚ)/36 ≤ r (i+a+b) - r a/2 - r b/2 := by
    obtain ⟨u, rfl⟩ : ∃ u, a=u+1 := ⟨a-1, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ v, b=v+1 := ⟨b-1, by omega⟩
    interval_cases i <;> dsimp [r] <;> push_cast <;>
      apply le_of_sub_nonneg <;> field_simp <;> ring_nf <;> positivity
  have pp (a b : ℕ) : 1-r a/2-r b/2 ≤ Q a b := by
    dsimp [r,Q]
    apply (le_of_mul_le_mul_left (a := 2*((a : ℚ)+1)*((b : ℚ)+1)) ?_ (by positivity))
    field_simp
    nlinarith [sq_nonneg ((a : ℚ)-(b : ℚ))]
  have p := pp a b
  have q := pp c d
  have z := pp e f
  have x := cls k a c hk ha1 hc1
  have y := cls 0 b e (by omega) hb1 he1
  have w := cls 0 d f (by omega) hd1 hf1
  have ga := gb a ha1
  have gc := gb c hc1
  have hk' : (k : ℚ) ≤ 1 := by exact_mod_cast hk
  have kn := Nat.cast_nonneg (α := ℚ) k
  norm_num at y w
  dsimp [L]
  nlinarith

/-- At least six mixed vertices force the whole Cauchy expression to be at least two. -/
theorem large_population (m : Fin 3 → ℕ) (x : Fin 3 → Fin 3 → ℕ)
    (hdiag : ∀ i, x i i = 0) (hM6 : 6 ≤ ∑ i, m i) :
    (2 : ℚ) ≤ quadraticLower m x := by
  have wide (hM : 7 ≤ ∑ i, m i ∨ ((∑ i, m i)=6 ∧ 4 ≤ ∑ i, ∑ j, x i j)) :
      (2 : ℚ) ≤ quadraticLower m x := by
    let M : ℚ := ∑ i, (m i : ℚ)
    let N : ℚ := ∑ i, ∑ j, (x i j : ℚ)
    have hN : 0 ≤ N := sum_nonneg fun i hi => sum_nonneg fun j hj => Nat.cast_nonneg _
    have hm6 : 6 ≤ M := by
      dsimp [M]
      exact_mod_cast (show 6 ≤ ∑ i, m i by rcases hM with h | h <;> omega)
    have cls : 9 / (N + M + 3) ≤
        ∑ i : Fin 3, 1 / ((m i + ∑ j, x i j : ℕ) + 1 : ℚ) := by
      have hc := sq_sum_div_le_sum_sq_div (univ : Finset (Fin 3))
        (fun _ => (1 : ℚ))
        (g := fun i => ((m i + ∑ j, x i j : ℕ) : ℚ) + 1)
        (fun i hi => by positivity)
      simpa [show (3 : ℚ)^2 = 9 by norm_num, M, N, sum_add_distrib, add_comm, add_left_comm, add_assoc] using hc
    have prod_bound : (∑ i : Fin 3, ∑ j : Fin 3, (x i j : ℚ) * (x j i : ℚ)) ≤ N^2/2 := by
      let a : ℚ := x 0 1
      let b : ℚ := x 1 0
      let c : ℚ := x 0 2
      let d : ℚ := x 2 0
      let e : ℚ := x 1 2
      let f : ℚ := x 2 1
      have hp : 0 ≤ a*d+a*f+c*b+c*f+e*b+e*d := by
        dsimp [a,b,c,d,e,f]; positivity
      have hs := sq_nonneg ((a+c+e)-(b+d+f))
      dsimp [N]
      norm_num [Fin.sum_univ_succ, hdiag]
      dsimp [a,b,c,d,e,f] at hp hs
      nlinarith only [hp, hs]
    have inc_bound : (∑ i : Fin 3, ∑ j : Fin 3, (incoming m x i j : ℚ)) ≤ 2*M := by
      have hi (i j : Fin 3) : (incoming m x i j : ℚ) ≤ if i = j then 0 else (m j : ℚ) := by
        by_cases hij : i = j
        · subst j; simp [incoming, hdiag]
        · simp only [hij, if_false]
          exact_mod_cast (show incoming m x i j ≤ m j by
            unfold incoming; split <;> omega)
      have hs := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin 3))) =>
        sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin 3))) => hi i j
      have he : (∑ i : Fin 3, ∑ j : Fin 3, if i = j then (0 : ℚ) else (m j : ℚ)) = 2*M := by
        simp [M, Fin.sum_univ_succ]
        ring
      exact hs.trans_eq he
    let q := fun p : Fin 3 × Fin 3 =>
      ((x p.1 p.2 * (x p.2 p.1 + 1) + incoming m x p.1 p.2 : ℕ) : ℚ)
    let f := fun p : Fin 3 × Fin 3 => (x p.1 p.2 : ℚ)
    let A := (univ : Finset (Fin 3 × Fin 3)).filter fun p => x p.1 p.2 ≠ 0
    have hq (p : Fin 3 × Fin 3) : f p ≤ q p := by
      dsimp [f,q]
      exact_mod_cast (show x p.1 p.2 ≤ x p.1 p.2 * (x p.2 p.1 + 1) + incoming m x p.1 p.2 by
        nlinarith [Nat.zero_le (incoming m x p.1 p.2)])
    have hsumf : (∑ p ∈ A, f p) = N := by
      rw [show N = ∑ p : Fin 3 × Fin 3, f p by simp [N, f, Fintype.sum_prod_type]]
      apply sum_subset (filter_subset _ _)
      intro p hp hn
      simp only [A, mem_filter, mem_univ, true_and, not_not] at hn
      simp [f, hn]
    have hsumq : (∑ p ∈ A, q p) ≤ N^2/2 + N + 2*M := by
      have hsub : (∑ p ∈ A, q p) ≤ ∑ p : Fin 3 × Fin 3, q p :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p hp hn => by dsimp [q]; positivity)
      apply hsub.trans
      have he : (∑ p : Fin 3 × Fin 3, q p) =
          (∑ i : Fin 3, ∑ j : Fin 3, (x i j : ℚ)*(x j i : ℚ)) + N +
            ∑ i : Fin 3, ∑ j : Fin 3, (incoming m x i j : ℚ) := by
        simp [q, N, Fintype.sum_prod_type, mul_add, sum_add_distrib]
      rw [he]
      linarith
    have hrec : N^2/(N^2+2*N+4*M) ≤
        (1/2 : ℚ) * ∑ i : Fin 3, ∑ j : Fin 3,
          (x i j : ℚ)^2 / ((x i j * (x j i + 1) + incoming m x i j : ℕ) : ℚ) := by
      have he : (∑ p ∈ A, (f p)^2 / q p) =
          ∑ i : Fin 3, ∑ j : Fin 3,
            (x i j : ℚ)^2 / ((x i j * (x j i + 1) + incoming m x i j : ℕ) : ℚ) := by
        rw [show (∑ i : Fin 3, ∑ j : Fin 3,
            (x i j : ℚ)^2 / ((x i j * (x j i + 1) + incoming m x i j : ℕ) : ℚ)) =
            ∑ p : Fin 3 × Fin 3, (f p)^2/q p by simp [f,q,Fintype.sum_prod_type]]
        apply sum_subset (filter_subset _ _)
        intro p hp hn
        simp only [A, mem_filter, mem_univ, true_and, not_not] at hn
        simp [f, hn]
      rw [← he]
      by_cases hz : N = 0
      · simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
        apply mul_nonneg (by norm_num)
        exact sum_nonneg fun p hp => div_nonneg (sq_nonneg _) (by dsimp [q]; positivity)
      have hp : 0 < ∑ p ∈ A, q p := by
        have hsum := sum_le_sum (s := A) fun p hp => hq p
        rw [hsumf] at hsum
        exact lt_of_lt_of_le (lt_of_le_of_ne hN (Ne.symm hz)) hsum
      have hc := sq_sum_div_le_sum_sq_div A f (g := q) (fun p hp => by
        have hx : (0 : ℚ) < f p := by
          dsimp [f]
          exact_mod_cast Nat.pos_of_ne_zero (mem_filter.mp hp).2
        exact lt_of_lt_of_le hx (hq p))
      rw [hsumf] at hc
      have hb : 2 * (∑ p ∈ A, q p) ≤ N^2+2*N+4*M := by linarith
      have hdiv := div_le_div_of_nonneg_left (sq_nonneg N) (show 0 < 2*(∑ p ∈ A,q p) by positivity) hb
      have hh : N^2 / (2*(∑ p ∈ A,q p)) = (1/2 : ℚ)*(N^2/(∑ p ∈ A,q p)) := by ring
      rw [hh] at hdiv
      exact hdiv.trans (mul_le_mul_of_nonneg_left hc (by norm_num))
    have numeric : (2 : ℚ) ≤ M/6 + 9/(N+M+3) + N^2/(N^2+2*N+4*M) := by
      have hden1 : 0 < N+M+3 := by linarith
      have hden2 : 0 < N^2+2*N+4*M := by nlinarith [sq_nonneg N]
      rcases hM with hM | ⟨hM, hU⟩
      · have hm7 : 7 ≤ M := by dsimp [M]; exact_mod_cast hM
        let t := M-7
        have ht : 0 ≤ t := sub_nonneg.mpr hm7
        have hp : 0 ≤ 4*t^3+(N^2+6*N+48)*t^2+
            (N^3+13*N^2+18*N+156)*t+N^3+54*(N-11/9)^2+94/3 := by positivity
        apply (le_of_mul_le_mul_left (a := 6*(N+M+3)*(N^2+2*N+4*M)) ?_ (by positivity))
        dsimp [t] at hp
        field_simp
        nlinarith only [hp]
      · have hmEq : M=6 := by dsimp [M]; exact_mod_cast hM
        have hU' : 4 ≤ N := by dsimp [N]; exact_mod_cast hU
        rw [hmEq]
        apply (le_of_mul_le_mul_left (a := (N+6+3)*(N^2+2*N+4*6)) ?_ (by positivity))
        have hp : 0 ≤ N*(7*N-24) := mul_nonneg hN (by linarith)
        field_simp
        nlinarith only [hp]
    unfold quadraticLower
    change 2 ≤ _ + M/6 + _
    linarith
  by_cases hw : 7 ≤ ∑ i, m i ∨ ((∑ i, m i)=6 ∧ 4 ≤ ∑ i, ∑ j, x i j)
  · exact wide hw
  have hm6 : (∑ i, m i)=6 := by omega
  let U := ∑ i, ∑ j, x i j
  have hu : U ≤ 3 := by dsimp [U]; omega
  let n (i : Fin 3) := m i + ∑ j, x i j
  let P := max (n 0) (max (n 1) (n 2))
  have np (i : Fin 3) : n i ≤ P := by
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have degree (i j : Fin 3) : x j i + m j ≤ P := by
    have h : x j i ≤ ∑ k, x j k := single_le_sum (fun k hk => Nat.zero_le _) (mem_univ i)
    exact (show x j i + m j ≤ n j by dsimp [n]; omega).trans (np j)
  have term (i j : Fin 3) : (x i j : ℚ) / ((P : ℚ)+1) ≤
      (x i j : ℚ)^2 / ((x i j*(x j i+1)+incoming m x i j : ℕ) : ℚ) := by
    by_cases hz : x i j = 0
    · simp [hz]
    have hx : 1 ≤ x i j := by omega
    have hi : incoming m x i j ≤ m j := by unfold incoming; split <;> omega
    have hd := degree i j
    have hn : x i j*(x j i+1)+incoming m x i j ≤ x i j*(P+1) := by nlinarith
    have hpos : (0 : ℚ) < (x i j*(x j i+1)+incoming m x i j : ℕ) := by
      exact_mod_cast (show 0 < x i j*(x j i+1)+incoming m x i j by nlinarith)
    have hxq : (x i j : ℚ) ≠ 0 := by exact_mod_cast hz
    calc
      _ = (x i j : ℚ)^2 / ((x i j : ℚ)*((P : ℚ)+1)) := by field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) hpos (by exact_mod_cast hn)
  have terms := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin 3))) =>
    sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin 3))) => term i j
  have sumterms : (U : ℚ)/((P : ℚ)+1) ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      (x i j : ℚ)^2 / ((x i j*(x j i+1)+incoming m x i j : ℕ) : ℚ) := by
    simpa only [U, Nat.cast_sum, sum_div] using terms
  have total : n 0+n 1+n 2=U+6 := by
    have he : (∑ i, n i) = U + ∑ i, m i := by simp [n,U,sum_add_distrib,add_comm]
    simpa [Fin.sum_univ_succ, hm6, add_assoc] using he
  have scalar (p q r u : ℚ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
      (hu : 0 ≤ u) (hu3 : u ≤ 3) (hs : p+q+r=u+6) :
      2 ≤ 1 + u/(2*(p+1)) + 1/(p+1) + 1/(q+1) + 1/(r+1) := by
    have pair : 4/(q+r+2) ≤ 1/(q+1)+1/(r+1) := by
      apply (le_of_mul_le_mul_left (a := (q+r+2)*(q+1)*(r+1)) ?_ (by positivity))
      field_simp
      nlinarith [sq_nonneg (q-r)]
    have den : 0 < u+8-p := by linarith
    have core : 1 ≤ (u+2)/(2*(p+1))+4/(u+8-p) := by
      have pos : 0 ≤ (4*p-3*u-8)^2+u*(16-u) :=
        add_nonneg (sq_nonneg _) (mul_nonneg hu (by linarith))
      apply (le_of_mul_le_mul_left (a := 2*(p+1)*(u+8-p)) ?_ (by positivity))
      field_simp
      nlinarith only [pos]
    rw [show q+r+2=u+8-p by linarith] at pair
    have split : (u+2)/(2*(p+1))=u/(2*(p+1))+1/(p+1) := by field_simp <;> ring
    rw [split] at core
    linarith only [pair,core]
  have small (p q r : ℕ) (hs : p+q+r=U+6) :
      (2 : ℚ) ≤ 1 + (U : ℚ)/(2*((p : ℚ)+1)) +
        1/((p : ℚ)+1)+1/((q : ℚ)+1)+1/((r : ℚ)+1) := by
    exact scalar p q r U (by positivity) (by positivity) (by positivity)
      (by positivity) (by exact_mod_cast hu) (by exact_mod_cast hs)
  have num : (2 : ℚ) ≤ 1 + (U : ℚ)/(2*((P : ℚ)+1)) +
      ∑ i : Fin 3, 1/((n i : ℚ)+1) := by
    rcases le_total (n 1) (n 2) with h12 | h21
    · rcases le_total (n 0) (n 2) with h02 | h20
      · have he : P=n 2 := by simp [P,max_eq_right h12,max_eq_right h02]
        rw [he]
        have hb := small (n 2) (n 0) (n 1) (by omega)
        convert hb using 1 <;> simp [Fin.sum_univ_succ] <;> ring
      · have he : P=n 0 := by simp [P,max_eq_right h12,max_eq_left h20]
        rw [he]
        simpa [Fin.sum_univ_succ,add_assoc] using small (n 0) (n 1) (n 2) total
    · rcases le_total (n 0) (n 1) with h01 | h10
      · have he : P=n 1 := by simp [P,max_eq_left h21,max_eq_right h01]
        rw [he]
        have hb := small (n 1) (n 0) (n 2) (by omega)
        convert hb using 1 <;> simp [Fin.sum_univ_succ] <;> ring
      · have he : P=n 0 := by simp [P,max_eq_left h21,max_eq_left h10]
        rw [he]
        simpa [Fin.sum_univ_succ,add_assoc] using small (n 0) (n 1) (n 2) total
  have hmq : (∑ i, (m i : ℚ))=6 := by exact_mod_cast hm6
  unfold quadraticLower
  rw [hmq]
  change 2 ≤ (∑ i : Fin 3, 1/((n i : ℚ)+1)) + 6/6 + _
  have he : (U : ℚ)/(2*((P : ℚ)+1)) = (1/2 : ℚ)*((U : ℚ)/((P : ℚ)+1)) := by field_simp <;> ring
  rw [he] at num
  linarith only [num,sumterms]

end D5.S3.Combinatorics.Graph.ThreeColorOuterBounds
