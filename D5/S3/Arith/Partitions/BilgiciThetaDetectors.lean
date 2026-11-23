/- GID: D5/S3/Arith/Partitions/BilgiciThetaDetectors
   generality: I
   mirror-B: D5/B/S3/Arith/Partitions/BilgiciThetaDetectors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact trace ideal and dual-number evaluation give detectors on the quotient. -/

import D5.S3.Arith.Partitions.BilgiciThetaGrading

/-! The exact trace ideal and dual-number evaluation give detectors on the quotient. -/

open D5.S3.Arith.Partitions.BilgiciThetaQuartic hiding digit
open MvPolynomial

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural

abbrev D := TrivSqZeroExt K K

private def digitVal (i : Fin 9) : D :=
  let a : K := (i.val + 1 : ℕ)
  let s := sign (index i)
  (s * a, s * a^5)

noncomputable def eta : R →ₐ[K] D := aeval digitVal

private def epsEval (p : Sparse) : D :=
  (p.map fun (m,c) => TrivSqZeroExt.inl c * (m.map digitVal).prod).sum

private theorem eta_term (m : Word) (c : K) :
    eta (term (m,c)) = TrivSqZeroExt.inl c * (m.map digitVal).prod := by
  have hm : eta (term (m,1)) = (m.map digitVal).prod := by
    rw [← mon_index]
    induction m with
    | nil => exact map_one eta
    | cons i m ih =>
      change eta (Z (index i) * monomialWord (m.map index)) =
        digitVal i * (m.map digitVal).prod
      rw [map_mul, Z_base, show eta (X i) = digitVal i from aeval_X _ _, ih]
  have ht : term (m,c) = C c * term (m,1) := by
    change monomial _ c = C c * monomial _ (1 : K)
    rw [C_mul_monomial, mul_one]
  rw [ht, map_mul, hm]
  congr 1
  exact aeval_C _ _

private theorem epsEval_denote (p : Sparse) : eta (denote p) = epsEval p := by
  induction p with
  | nil => simp [epsEval]
  | cons u p ih =>
    obtain ⟨m,c⟩ := u
    rw [denote_cons, map_add, ih, eta_term]
    rfl

noncomputable def ellR (n : ℕ) : R →ₗ[K] K :=
  (Polynomial.lcoeff K n).comp trace.toLinearMap

noncomputable def epsR : R →ₗ[K] K := (TrivSqZeroExt.sndHom K K).comp eta.toLinearMap

theorem ellR_sparse (n : ℕ) (p : Sparse) :
    ellR n (denote p) = traceCoeff n p :=
  trace_coeff n p

private theorem epsR_sparse (p : Sparse) : epsR (denote p) = (epsEval p).snd := by
  change (eta (denote p)).snd = _
  rw [epsEval_denote]

theorem S_grades : S_Z.IsHomogeneous 3 ∧ S_Z.IsWeightedHomogeneous w 2 := by
  rw [← denote_sSparse]
  exact denote_grades _ _ _ (by decide)

private theorem S_eta_zero : eta S_Z = 0 := by
  rw [← denote_sSparse, epsEval_denote]
  exact TrivSqZeroExt.ext (by decide) (by decide)

private theorem S_trace_low (n : ℕ) (hn : n < 21) : ellR n S_Z = 0 := by
  have horders : ∀ t ∈ sSparse, 21 ≤ traceDegree t.1 := by decide
  rw [← denote_sSparse, ellR_sparse]
  change (List.map (fun (m,c) => if traceDegree m = n then c else 0) sSparse).sum = 0
  apply List.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  have h := horders t ht
  exact ite_eq_right (by omega)

end D5.S3.Arith.Partitions.BilgiciThetaStructural

open D5.S3.Arith.Partitions.BilgiciThetaQuartic hiding digit
open MvPolynomial
open D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening (digit x x_digit x_zero x_odd raw labels raw_pair_int)

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural

def dual (a b : K) : D := (a,b)

private theorem eta_x_digit (i : Fin 9) : eta (x (digit i)) = dual (digit i) (digit i ^ 5) := by
  rw [x_digit, map_smul, show eta (X i) = digitVal i from aeval_X _ _]
  have hs : sign (index i) * sign (index i) = 1 := by
    unfold sign; split <;> simp
  apply TrivSqZeroExt.ext
  · change sign (index i) *
      (sign (index i) * digit i) = digit i
    rw [← mul_assoc, hs, one_mul]
  · change sign (index i) *
      (sign (index i) * digit i ^ 5) = digit i ^ 5
    rw [← mul_assoc, hs, one_mul]

theorem eta_signed_index (r : K) : eta (x r) = dual r (r ^ 5) := by
  have hpos (n : ℕ) (hn : 1 ≤ n) (h₉ : n ≤ 9) :
      eta (x (n : K)) = dual (n : K) ((n : K)^5) := by
    let i : Fin 9 := ⟨n - 1, by omega⟩
    have hi : digit i = (n : K) := by
      change ((n - 1 + 1 : ℕ) : K) = (n : K)
      rw [show n - 1 + 1 = n by omega]
    simpa only [hi] using eta_x_digit i
  have hr : r.val < 19 := ZMod.val_lt r
  have hcast := ZMod.natCast_zmod_val r
  by_cases hzero : r.val = 0
  · have hz : r = 0 := by simpa only [hzero, Nat.cast_zero] using hcast.symm
    subst r
    rw [x_zero, map_zero]
    apply TrivSqZeroExt.ext
    · rfl
    · change (0 : K) = 0^5
      simp
  by_cases hsmall : r.val ≤ 9
  · simpa only [hcast] using hpos r.val (by omega) hsmall
  let n := 19 - r.val
  have hn₁ : 1 ≤ n := by dsimp [n]; omega
  have hn₉ : n ≤ 9 := by dsimp [n]; omega
  have hsum : r + (n : K) = 0 := calc
    r + (n : K) = (r.val : K) + (n : K) := congrArg (· + (n : K)) hcast.symm
    _ = ((r.val + n : ℕ) : K) := (Nat.cast_add ..).symm
    _ = 0 := by
      rw [show r.val + n = 19 by dsimp [n]; omega]
      exact ZMod.natCast_self 19
  have hr' : r = -(n : K) := eq_neg_of_add_eq_zero_left hsum
  rw [hr', x_odd, map_neg, hpos n hn₁ hn₉]
  apply TrivSqZeroExt.ext
  · rfl
  · change -((n : K)^5) = (-(n : K))^5
    ring

private theorem dual_pair (u v : K) :
    dual (u + v) ((u + v)^5) * dual (u - v) ((u - v)^5) =
      dual (u^2 - v^2) (2 * ((u^2)^3 - (v^2)^3) +
        10 * ((u^2)^2 * v^2 - u^2 * (v^2)^2)) := by
  apply TrivSqZeroExt.ext
  · change (u + v) * (u - v) = u^2 - v^2
    ring
  · rw [TrivSqZeroExt.snd_mul (R := K) (M := K)]
    simp only [dual, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, op_smul_eq_mul, smul_eq_mul]
    ring

private def f (a : K) : D := dual a (2 * a^3)
private def g (a : K) : D := dual 1 (-10 * a^2)

private theorem dual_wedge (a b : K) :
    dual (a - b) (2 * (a^3 - b^3) + 10 * (a^2*b - a*b^2)) =
      f a * g b - g a * f b := by
  apply TrivSqZeroExt.ext
  · change a - b = a * 1 - 1 * b
    ring
  · rw [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_mul (R := K) (M := K),
      TrivSqZeroExt.snd_mul (R := K) (M := K)]
    simp only [f, g, dual, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, op_smul_eq_mul, smul_eq_mul]
    ring

private theorem eta_pair (u v : ℤ) :
    eta (pair u v) =
      f ((u : K)^2) * g ((v : K)^2) - g ((u : K)^2) * f ((v : K)^2) := by
  change eta (Z (u+v) * Z (u-v)) = _
  rw [← raw_pair_int]
  change eta (x ((u : K) + (v : K)) * (x ((u : K) - (v : K)) * 1)) = _
  rw [mul_one, map_mul, eta_signed_index, eta_signed_index, dual_pair, dual_wedge]

private theorem plucker₂ {S : Type*} [CommRing S] {α : Type*}
    (f g : α → S) (a b c d : α) :
    let p := fun x y => f x * g y - g x * f y
    p a d * p b c - p a c * p b d + p a b * p c d = 0 := by
  dsimp
  ring

theorem eta_theta_zero (x : ℤ × ℤ × ℤ × ℤ) : eta (theta x) = 0 := by
  obtain ⟨a,b,c,d⟩ := x
  let p := pair
  change eta (p a d * p b c - p a c * p b d + p a b * p c d) = 0
  simp only [map_add, map_sub, map_mul, p, eta_pair]
  exact plucker₂ f g ((a : K)^2) ((b : K)^2) ((c : K)^2) ((d : K)^2)

end D5.S3.Arith.Partitions.BilgiciThetaStructural

open D5.S3.Arith.Partitions.BilgiciThetaQuartic hiding digit
open MvPolynomial
open scoped Polynomial

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural


private def traceExponent (s : ℤ) : ℕ := ((9 - s) * (10 - s)).toNat / 2

private theorem traceExponent_reflect (s : ℤ) : traceExponent (19 - s) = traceExponent s := by
  unfold traceExponent
  rw [show (9 - (19 - s)) * (10 - (19 - s)) = (9 - s) * (10 - s) by ring]

private theorem traceExponent_twice (s : ℤ) :
    2 * (traceExponent s : ℤ) = (9 - s) * (10 - s) := by
  have hn : 0 ≤ (9 - s) * (10 - s) := by
    by_cases h : s ≤ 9
    · exact mul_nonneg (by omega) (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have he : ((9 - s) * (10 - s)) % 2 = 0 := by
    rw [Int.mul_emod]
    by_cases h : (9 - s) % 2 = 0
    · simp [h]
    · rw [show (10-s) % 2 = 0 by omega]
      simp
  unfold traceExponent
  rw [Int.natCast_ediv, Int.toNat_of_nonneg hn, show ((2 : ℕ) : ℤ) = 2 by rfl,
    mul_comm, Int.ediv_mul_cancel_of_emod_eq_zero he]

private theorem trace_Z_base_int (s : ℤ) (h₁ : 1 ≤ s) (h₉ : s ≤ 9) :
    trace (Z s) = Polynomial.X ^ traceExponent s := by
  let i : Fin 9 := ⟨(s - 1).toNat, by omega⟩
  have hi : index i = s := by
    unfold index; dsimp [i]
    omega
  have he : tNatural i = traceExponent s := by
    unfold tNatural; rw [hi, traceExponent, Int.toNat_mul (by omega) (by omega)]
  rw [← hi, Z_base, show trace (X i) = Polynomial.X ^ tNatural i
    from aeval_X _ _, he, hi]

private theorem trace_Z_positive (s : ℤ) (h₁ : 1 ≤ s) (h₁₈ : s ≤ 18) :
    trace (Z s) = Polynomial.X ^ traceExponent s := by
  by_cases h₉ : s ≤ 9
  · exact trace_Z_base_int s h₁ h₉
  · rw [← Z_reflect s,
      trace_Z_base_int (19-s) (by omega) (by omega), traceExponent_reflect]

private def tracePairOrder (u v : ℤ) : ℕ := (90 - 19*u + u^2 + v^2).toNat

private theorem tracePairOrder_cast {u v : ℤ} (hu : u ≤ 9) :
    (tracePairOrder u v : ℤ) = 90 - 19*u + u^2 + v^2 := by
  apply Int.toNat_of_nonneg
  have h : 0 ≤ (9-u) * (10-u) := mul_nonneg (by omega) (by omega)
  nlinarith [sq_nonneg v]

private theorem theta_pairs (a b c d : ℤ) :
    theta (a,b,c,d) =
      pair a d * pair b c - pair a c * pair b d + pair a b * pair c d :=
  rfl

private theorem trace_pair_positive (u v : ℤ) (hv : 0 ≤ v) (hvu : v < u) (hu : u ≤ 9) :
    trace (pair u v) = Polynomial.X ^ tracePairOrder u v := by
  change trace (Z (u+v) * Z (u-v)) = _
  rw [map_mul, trace_Z_positive (u+v) (by omega) (by omega),
    trace_Z_positive (u-v) (by omega) (by omega), ← pow_add]
  have hsum : traceExponent (u+v) + traceExponent (u-v) = tracePairOrder u v := by
    have hs := traceExponent_twice (u+v)
    have hd := traceExponent_twice (u-v)
    have hp := tracePairOrder_cast (v := v) hu
    have h : (9-(u+v)) * (10-(u+v)) + (9-(u-v)) * (10-(u-v)) =
        2 * (90 - 19*u + u^2 + v^2) := by ring
    omega
  rw [hsum]

private theorem pair_swap (u v : ℤ) : pair v u = - pair u v := by
  change Z (v+u) * Z (v-u) = - (Z (u+v) * Z (u-v))
  rw [add_comm v u, show v-u = -(u-v) by ring, Z_neg, mul_neg]

private theorem pair_diag (u : ℤ) : pair u u = 0 := by
  change Z (u+u) * Z (u-u) = 0
  rw [sub_self, show Z 0 = 0 from Z_mul19 0, mul_zero]

private theorem theta_swap₁ (a b c d : ℤ) : theta (b,a,c,d) = -theta (a,b,c,d) := by
  simp only [theta_pairs]
  rw [pair_swap a b]
  ring

private theorem theta_swap₂ (a b c d : ℤ) : theta (a,c,b,d) = -theta (a,b,c,d) := by
  simp only [theta_pairs]
  rw [pair_swap b c]
  ring

private theorem theta_swap₃ (a b c d : ℤ) : theta (a,b,d,c) = -theta (a,b,c,d) := by
  simp only [theta_pairs]
  rw [pair_swap c d]
  ring

private theorem theta_repeat₁ (a c d : ℤ) : theta (a,a,c,d) = 0 := by
  let p := pair
  change p a d * p a c - p a c * p a d + p a a * p c d = 0
  simp only [p, pair_diag]
  ring

private theorem theta_repeat₂ (a b d : ℤ) : theta (a,b,b,d) = 0 := by
  let p := pair
  change p a d * p b b - p a b * p b d + p a b * p b d = 0
  simp only [p, pair_diag]
  ring

private theorem theta_repeat₃ (a b c : ℤ) : theta (a,b,c,c) = 0 := by
  let p := pair
  change p a c * p b c - p a c * p b c + p a b * p c c = 0
  simp only [p, pair_diag]
  ring

private theorem trace_theta_sorted (a b c d : ℤ) (hd : 0 ≤ d) (hcd : d < c)
    (hbc : c < b) (hab : b < a) (ha : a ≤ 9) :
    trace (theta (a,b,c,d)) = Polynomial.X ^ (tracePairOrder a b + tracePairOrder c d) := by
  let p := pair
  change trace (p a d * p b c - p a c * p b d + p a b * p c d) = _
  simp only [map_add, map_sub, map_mul, p]
  rw [trace_pair_positive a d hd (by omega) ha,
    trace_pair_positive b c (by omega) hbc (by omega),
    trace_pair_positive a c (by omega) (by omega) ha,
    trace_pair_positive b d hd (by omega) (by omega),
    trace_pair_positive a b (by omega) hab ha,
    trace_pair_positive c d hd hcd (by omega),
    ← pow_add, ← pow_add, ← pow_add]
  have he : tracePairOrder a d + tracePairOrder b c =
      tracePairOrder a c + tracePairOrder b d := by
    have h₁ := tracePairOrder_cast (v := d) ha
    have h₂ := tracePairOrder_cast (v := c) (show b ≤ 9 by omega)
    have h₃ := tracePairOrder_cast (v := c) ha
    have h₄ := tracePairOrder_cast (v := d) (show b ≤ 9 by omega)
    omega
  rw [he, sub_self, zero_add]

private theorem trace_order_lower {a b c d : ℤ} (ha : a ≤ 9) (hc : c ≤ 9)
    (hc₀ : 0 ≤ c) (hcb : c < b) :
    55 ≤ tracePairOrder a b + tracePairOrder c d := by
  have h₁ := tracePairOrder_cast (v := b) ha
  have h₂ := tracePairOrder_cast (v := d) hc
  have hs : (c+1)^2 ≤ b^2 := by
    simpa only [pow_two] using Int.mul_self_le_mul_self (show 0 ≤ c+1 by omega) (show c+1 ≤ b by omega)
  have hₐ : 0 ≤ (9-a) * (10-a) := mul_nonneg (by omega) (by omega)
  have hbound : 0 ≤ (c-4) * (2*c-9) := by
    by_cases h : c ≤ 4
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  have hquadratic : 2*c^2 - 17*c + 91 ≤ (tracePairOrder a b : ℤ) + (tracePairOrder c d : ℤ) := by
    nlinarith [sq_nonneg d]
  have hmin : 55 ≤ 2*c^2 - 17*c + 91 := by linarith only [hbound, show (c-4)*(2*c-9) = 2*c^2 - 17*c + 36 by ring]
  exact_mod_cast hmin.trans hquadratic

private theorem trace_theta_witness : trace (theta (9,5,4,0)) = Polynomial.X ^ 55 := by
  rw [trace_theta_sorted _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
  norm_num [tracePairOrder]

private noncomputable def thetaList : List ℤ → R
  | [a,b,c,d] => theta (a,b,c,d)
  | _ => 0

private theorem thetaList_swap (P : R → Prop) (hneg : ∀ r, P (-r) ↔ P r)
    (pre : List ℤ) (a b : ℤ) (tail : List ℤ) :
    P (thetaList (pre ++ b :: a :: tail)) ↔ P (thetaList (pre ++ a :: b :: tail)) := by
  rcases pre with _ | ⟨p, _ | ⟨q, _ | ⟨r, pre⟩⟩⟩
  · rcases tail with _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩
    · rfl
    · rfl
    · exact (congrArg P (theta_swap₁ a b c d)).to_iff.trans (hneg _)
    · rfl
  · rcases tail with _ | ⟨d, _ | ⟨e, tail⟩⟩
    · rfl
    · exact (congrArg P (theta_swap₂ p a b d)).to_iff.trans (hneg _)
    · rfl
  · rcases tail with _ | ⟨c, tail⟩
    · exact (congrArg P (theta_swap₃ p q a b)).to_iff.trans (hneg _)
    · rfl
  · rcases pre with _ | ⟨s, _ | ⟨t, pre⟩⟩ <;> rfl

/-- Permuting labels preserves every property of the theta value invariant under negation. -/
private theorem thetaList_perm (P : R → Prop) (hneg : ∀ r, P (-r) ↔ P r)
    {l m : List ℤ} (h : l.Perm m) (pre : List ℤ) :
    P (thetaList (pre ++ l)) ↔ P (thetaList (pre ++ m)) := by
  induction h generalizing pre with
  | nil => rfl
  | cons a h ih => simpa only [List.append_assoc, List.singleton_append] using ih (pre ++ [a])
  | swap a b tail => exact thetaList_swap P hneg pre a b tail
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ pre).trans (ih₂ pre)

private theorem trace_theta_reduced (a b c d : ℤ)
    (hbounds : ∀ z ∈ [a,b,c,d], 0 ≤ z ∧ z ≤ 9) :
    Polynomial.X ^ 55 ∣ trace (theta (a,b,c,d)) := by
  let l := [a,b,c,d]
  let m := l.insertionSort (· ≥ ·)
  have hp : m.Perm l := List.perm_insertionSort _ _
  have hs : m.Pairwise (· ≥ ·) := List.pairwise_insertionSort _ _
  obtain ⟨a', b', c', d', hm⟩ := List.length_eq_four.mp (show m.length = 4 from hp.length_eq)
  rw [hm] at hp hs
  have ha : a' ≤ 9 := (hbounds a' (hp.mem_iff.mp (by simp))).2
  have hd : 0 ≤ d' := (hbounds d' (hp.mem_iff.mp (by simp))).1
  have hab : b' ≤ a' := List.rel_of_pairwise_cons hs (by simp)
  have hbc : c' ≤ b' := List.rel_of_pairwise_cons hs.of_cons (by simp)
  have hcd : d' ≤ c' := List.rel_of_pairwise_cons hs.of_cons.of_cons (by simp)
  let P : R → Prop := fun r => Polynomial.X ^ 55 ∣ trace r
  have hneg (r : R) : P (-r) ↔ P r := by simp [P]
  apply (thetaList_perm P hneg hp []).mp
  change Polynomial.X ^ 55 ∣ trace (theta (a',b',c',d'))
  rcases eq_or_lt_of_le hab with hab | hab
  · rw [hab, theta_repeat₁, map_zero]
    exact dvd_zero _
  rcases eq_or_lt_of_le hbc with hbc | hbc
  · rw [hbc, theta_repeat₂, map_zero]
    exact dvd_zero _
  rcases eq_or_lt_of_le hcd with hcd | hcd
  · rw [hcd, theta_repeat₃, map_zero]
    exact dvd_zero _
  rw [trace_theta_sorted _ _ _ _ hd hcd hbc hab ha]
  exact pow_dvd_pow _ (trace_order_lower ha (by omega) (by omega) hbc)

private theorem trace_theta_dvd (x : ℤ × ℤ × ℤ × ℤ) : Polynomial.X ^ 55 ∣ trace (theta x) := by
  obtain ⟨a,b,c,d⟩ := x
  rw [theta_reduce]
  apply trace_theta_reduced
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  have bounds (x : ℤ) : 0 ≤ representative x ∧ representative x ≤ 9 := by
    obtain ⟨h₀, h₁⟩ := representative_bounds x
    exact ⟨h₀, by omega⟩
  rcases hz with rfl | rfl | rfl | rfl <;> exact bounds _

theorem trace_ITheta_map :
    Ideal.map trace.toRingHom ITheta = Ideal.span ({Polynomial.X ^ 55} : Set (Polynomial K)) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨x,rfl⟩
    exact Ideal.mem_span_singleton.mpr (trace_theta_dvd x)
  · apply Ideal.span_le.mpr
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht, ← trace_theta_witness]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨_, rfl⟩)

end D5.S3.Arith.Partitions.BilgiciThetaStructural

open D5.S3.Arith.Partitions.BilgiciThetaQuartic hiding digit
open MvPolynomial

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural

private theorem eta_ideal {f : R} (hf : f ∈ ITheta) : eta f = 0 := by
  have h : ITheta ≤ RingHom.ker eta.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact eta_theta_zero x
  exact h hf

private theorem trace_ideal {f : R} (hf : f ∈ ITheta) :
    Polynomial.X^55 ∣ trace f := by
  have h := Ideal.mem_map_of_mem trace.toRingHom hf
  rw [trace_ITheta_map] at h
  exact Ideal.mem_span_singleton.mp h

noncomputable def eps : A →ₗ[K] K :=
  (TrivSqZeroExt.sndHom K K).comp
    (Ideal.Quotient.liftₐ ITheta eta (fun _ => eta_ideal)).toLinearMap

theorem eps_q (f : R) : eps (q f) = epsR f := rfl

noncomputable def ell (n : ℕ) (hn : n < 55) : A →ₗ[K] K :=
  Submodule.liftQ (ITheta.restrictScalars K) (ellR n)
    (fun _ hf => Polynomial.X_pow_dvd_iff.mp (trace_ideal hf) n hn)

theorem ell_q (n : ℕ) (hn : n < 55) (f : R) : ell n hn (q f) = ellR n f := rfl

private theorem eps_mul_S_Z (f : A) : eps (q S_Z * f) = 0 := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective f
  change eps (q S_Z * q r) = 0
  rw [← map_mul, eps_q]
  change (eta (S_Z * r)).snd = 0
  rw [map_mul, S_eta_zero, zero_mul]
  rfl

private theorem ell_mul_S_Z (f : A) : ell 11 (by decide) (q S_Z * f) = 0 := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective f
  change ell 11 (by decide) (q S_Z * q r) = 0
  rw [← map_mul, ell_q]
  have hS : Polynomial.X^21 ∣ trace S_Z :=
    Polynomial.X_pow_dvd_iff.mpr S_trace_low
  change (trace (S_Z * r)).coeff 11 = 0
  rw [map_mul]
  exact Polynomial.X_pow_dvd_iff.mp (dvd_mul_of_dvd_left hS _) _ (by decide)

noncomputable def tests : A →ₗ[K] K × K := (ell 11 (by decide)).prod eps

theorem tests_mul_S_Z (p : A) : tests (q S_Z * p) = 0 :=
  Prod.ext (ell_mul_S_Z p) (eps_mul_S_Z p)


end D5.S3.Arith.Partitions.BilgiciThetaStructural

open D5.S3.Arith.Partitions.BilgiciThetaQuartic hiding digit
open MvPolynomial

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural

noncomputable def u : R := P (monomialWord [5,8,9,9,9,9,9])
noncomputable def v : R := P (monomialWord [1,2,3,4,6,9,9])
noncomputable def h₁ : R := P (monomialWord [6,7,9,9])
noncomputable def h₂ : R := P (monomialWord [3,6,8,9])

private theorem u_tests : ellR 11 u = 17 ∧ epsR u = 13 := by
  rw [u, ← spProject_denote, ellR_sparse, epsR_sparse]
  exact ⟨by decide, by decide⟩

private theorem v_tests : ellR 11 v = 0 ∧ epsR v = 1 := by
  rw [v, ← spProject_denote, ellR_sparse, epsR_sparse]
  exact ⟨by decide, by decide⟩

theorem u_grades : u.IsHomogeneous 7 ∧ u.IsWeightedHomogeneous w 11 := by
  rw [u, ← spProject_denote]
  exact denote_grades _ _ _ (by decide)

theorem v_grades : v.IsHomogeneous 7 ∧ v.IsWeightedHomogeneous w 11 := by
  rw [v, ← spProject_denote]
  exact denote_grades _ _ _ (by decide)

theorem h₁_grades : h₁.IsHomogeneous 4 ∧ h₁.IsWeightedHomogeneous w 9 := by
  rw [h₁, ← spProject_denote]
  exact denote_grades _ _ _ (by decide)

theorem h₂_grades : h₂.IsHomogeneous 4 ∧ h₂.IsWeightedHomogeneous w 9 := by
  rw [h₂, ← spProject_denote]
  exact denote_grades _ _ _ (by decide)

theorem S_h₁_trace : ellR 30 (S_Z * h₁) = 17 ∧ ellR 49 (S_Z * h₁) = 9 := by
  rw [h₁, ← spProject_denote, ← denote_sSparse, ← denote_rawMul]
  rw [ellR_sparse, ellR_sparse]
  exact ⟨by decide, by decide⟩

theorem S_h₂_trace : ellR 30 (S_Z * h₂) = 0 ∧ ellR 49 (S_Z * h₂) = 1 := by
  rw [h₂, ← spProject_denote, ← denote_sSparse, ← denote_rawMul]
  rw [ellR_sparse, ellR_sparse]
  exact ⟨by decide, by decide⟩

theorem quotient_u_tests : tests (q u) = (17, 13) :=
  Prod.ext u_tests.1 u_tests.2

theorem quotient_v_tests : tests (q v) = (0, 1) :=
  Prod.ext v_tests.1 v_tests.2


end D5.S3.Arith.Partitions.BilgiciThetaStructural
