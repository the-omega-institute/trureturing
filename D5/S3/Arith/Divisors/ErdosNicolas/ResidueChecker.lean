/- GID: D5/S3/Arith/Divisors/ErdosNicolas/ResidueChecker
   generality: G
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; instance=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP23.chunk_checked
   digest: Integer square tests and finite convolution certificates for residue bounds. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Residual

/-! Integer residue tests and exact finite convolution bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- The integer criterion (20), including all denominator positivity checks. -/
def residueKernelCheck (p ell Q T M : ℕ) : Bool :=
  decide (0 < p ∧ 0 < ell ∧ 0 < Q ∧ 0 < T ∧ M < (p - 1) * Q * T ∧
    4 * (ell * p + 1) * (ell + 1) * Q ^ 2 * T ^ 2 <
      ell ^ 2 * ((p - 1) * Q * T - M) ^ 2)

/-- Exact rational interpretation of a successful integer residue square test. -/
private theorem residueKernelCheck_sound {p ell Q T M : ℕ}
    (h : residueKernelCheck p ell Q T M = true) :
    KernelTest 1 p (ell * p) 1 1 ((M : ℚ) / (p * Q * T)) := by
  obtain ⟨hp, he, hQ, hT, hM, hs⟩ := of_decide_eq_true h
  have hp₁ : 1 ≤ p := hp
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have heq : (0 : ℚ) < ell := by exact_mod_cast he
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hTq : (0 : ℚ) < T := by exact_mod_cast hT
  have hp0 := ne_of_gt hpq
  have he0 := ne_of_gt heq
  have hQ0 := ne_of_gt hQq
  have hT0 := ne_of_gt hTq
  let z := (p - 1) * Q * T - M
  have hz : (z : ℚ) = ((p : ℚ) - 1) * Q * T - M := by
    dsimp [z]
    rw [Nat.cast_sub hM.le, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp₁]
    simp
  have hzpos : (0 : ℚ) < z := by
    exact_mod_cast Nat.sub_pos_of_lt hM
  have hsq : 4 * ((ell : ℚ) * p + 1) * (ell + 1) * Q ^ 2 * T ^ 2 <
      (ell : ℚ) ^ 2 * (z : ℚ) ^ 2 := by
    exact_mod_cast hs
  have hgap : criterionGap 1 p 1 1 ((M : ℚ) / (p * Q * T)) =
      (z : ℚ) / (p * Q * T) := by
    rw [hz]
    unfold criterionGap
    push_cast
    field_simp
    <;> ring
  unfold KernelTest
  rw [hgap]
  constructor
  · exact div_pos hzpos (by positivity)
  · have hid :
        4 * (1 + 1 / ((ell : ℚ) * p)) * (1 / p + 1 / ((ell : ℚ) * p)) =
        (4 * ((ell : ℚ) * p + 1) * (ell + 1) * Q ^ 2 * T ^ 2) /
          ((ell : ℚ) ^ 2 * ((p : ℚ) * Q * T) ^ 2) := by
      field_simp
      <;> ring
    norm_num only [Nat.cast_one, one_mul, Nat.cast_mul]
    rw [hid, div_pow]
    have hden : (0 : ℚ) < (ell : ℚ) ^ 2 * ((p : ℚ) * Q * T) ^ 2 := by
      positivity
    apply (div_lt_div_iff₀ hden (by positivity :
      (0 : ℚ) < ((p : ℚ) * Q * T) ^ 2)).mpr
    nlinarith only [mul_lt_mul_of_pos_right hsq
      (by positivity : (0 : ℚ) < ((p : ℚ) * Q * T) ^ 2)]

/-- An integer form of the kernel test with both input bounds sharing denominator `D`. -/
def liftKernelCheck (a p ell D A B Q T M : ℕ) : Bool :=
  let C := A * p * Q * T + a * B * Q * T + D * M
  let S := (a + 1) * D * p * Q * T
  decide (0 < p ∧ 0 < ell ∧ 0 < D ∧ 0 < Q ∧ 0 < T ∧ C < S ∧
    4 * a * (A * ell * p + D) * (B * ell + D) * Q ^ 2 * T ^ 2 <
      ell ^ 2 * (S - C) ^ 2)

/-- Successful integer lift tests imply the exact rational kernel comparisons. -/
private theorem liftKernelCheck_sound {a p ell D A B Q T M : ℕ}
    (h : liftKernelCheck a p ell D A B Q T M = true) :
    KernelTest a p (ell * p) ((A : ℚ) / D) ((B : ℚ) / D)
      ((M : ℚ) / (p * Q * T)) := by
  obtain ⟨hp, he, hD, hQ, hT, hM, hs⟩ := of_decide_eq_true h
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have heq : (0 : ℚ) < ell := by exact_mod_cast he
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hTq : (0 : ℚ) < T := by exact_mod_cast hT
  have hp0 := ne_of_gt hpq
  have he0 := ne_of_gt heq
  have hD0 := ne_of_gt hDq
  have hQ0 := ne_of_gt hQq
  have hT0 := ne_of_gt hTq
  let z := (a + 1) * D * p * Q * T -
    (A * p * Q * T + a * B * Q * T + D * M)
  have hz : (z : ℚ) = ((a : ℚ) + 1) * D * p * Q * T -
      ((A : ℚ) * p * Q * T + a * B * Q * T + D * M) := by
    dsimp [z]
    rw [Nat.cast_sub hM.le]
    push_cast
    ring
  have hzpos : (0 : ℚ) < z := by
    exact_mod_cast Nat.sub_pos_of_lt hM
  have hsq :
      4 * (a : ℚ) * ((A : ℚ) * ell * p + D) * ((B : ℚ) * ell + D) *
          Q ^ 2 * T ^ 2 < (ell : ℚ) ^ 2 * (z : ℚ) ^ 2 := by
    exact_mod_cast hs
  have hgap :
      criterionGap a p ((A : ℚ) / D) ((B : ℚ) / D)
          ((M : ℚ) / (p * Q * T)) = (z : ℚ) / (D * p * Q * T) := by
    rw [hz]
    unfold criterionGap
    field_simp
    <;> ring
  unfold KernelTest
  rw [hgap]
  constructor
  · exact div_pos hzpos (by positivity)
  · have hid :
        4 * (a : ℚ) * ((A : ℚ) / D + 1 / ((ell : ℚ) * p)) *
            ((B : ℚ) / D / p + 1 / ((ell : ℚ) * p)) =
        (4 * (a : ℚ) * ((A : ℚ) * ell * p + D) * ((B : ℚ) * ell + D) *
          Q ^ 2 * T ^ 2) /
          ((ell : ℚ) ^ 2 * ((D : ℚ) * p * Q * T) ^ 2) := by
      field_simp
      <;> ring
    norm_num only [Nat.cast_mul]
    rw [hid, div_pow]
    have hden : (0 : ℚ) < (ell : ℚ) ^ 2 * ((D : ℚ) * p * Q * T) ^ 2 := by
      positivity
    apply (div_lt_div_iff₀ hden (by positivity :
      (0 : ℚ) < ((D : ℚ) * p * Q * T) ^ 2)).mpr
    nlinarith only [mul_lt_mul_of_pos_right hsq
      (by positivity : (0 : ℚ) < ((D : ℚ) * p * Q * T) ^ 2)]

/-- A prefix divisor list contributes this integer row to the residue vector. -/
def residueSum (p : ℕ) (B : ℕ → ℕ) (ds : List ℕ) (r : ℕ) : ℕ :=
  (ds.map fun d => B (r * d % p)).sum

/-- Divisor products, with the unknown suffix traversed outside the fixed prefix. -/
def residueProducts (ds es : List ℕ) : List ℕ :=
  es.flatMap fun e => ds.map (e * ·)

/-- Multiplication of divisor lists is exactly the residue convolution (19). -/
private theorem residueSum_products (p : ℕ) (B : ℕ → ℕ) (ds es : List ℕ) (r : ℕ) :
    residueSum p B (residueProducts ds es) r =
      (es.map fun e => residueSum p B ds (r * e % p)).sum := by
  induction es with
  | nil => simp [residueSum, residueProducts]
  | cons e es ih =>
    simp only [residueSum, residueProducts, List.flatMap_cons, List.map_append,
      List.sum_append, List.map_cons, List.sum_cons, List.map_map,
      Function.comp_def] at *
    rw [ih]
    congr 1
    congr 1
    apply List.map_congr_left
    intro d hd
    congr 1
    simp only [← Nat.mul_assoc, Nat.mul_mod, Nat.mod_mod]

/-- A uniform prefix row bound survives every suffix, paying only its number of divisors. -/
private theorem residueSum_products_le {p M : ℕ} (hp : 0 < p) (B : ℕ → ℕ)
    (ds es : List ℕ) (hM : ∀ r < p, residueSum p B ds r ≤ M) (r : ℕ) :
    residueSum p B (residueProducts ds es) r ≤ es.length * M := by
  rw [residueSum_products]
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h := hM (r * e % p) (Nat.mod_lt _ hp)
    nlinarith

/-- A complete finite row check; the zero residue is harmless for the integer vector. -/
def residueVectorCheck (p : ℕ) (B : ℕ → ℕ) (ds : List ℕ) (M : ℕ) : Bool :=
  (List.range p).all fun r => decide (residueSum p B ds r ≤ M)

/-- Every row, rather than a sampled subset, is controlled by the checked prefix. -/
private theorem residueVectorCheck_sound {p M : ℕ} {B : ℕ → ℕ} {ds : List ℕ}
    (h : residueVectorCheck p B ds M = true) :
    ∀ r < p, residueSum p B ds r ≤ M := by
  intro r hr
  have hh := List.all_eq_true.mp h r (List.mem_range.mpr hr)
  exact of_decide_eq_true hh

/-- Integer residue row bounds imply the rational average used by the kernel criterion. -/
private theorem residue_average_of_integer_bound {p L Q m M : ℕ} {B : ℕ → ℕ}
    (hp : 0 < p) (hQ : 0 < Q) (hm : 0 < m)
    (hB : ∀ d ∈ m.divisors, (p * Q : ℕ) * f p L (d % p) ≤ (B (d % p) : ℚ))
    (hM : ∑ d ∈ m.divisors, B (d % p) ≤ M) :
    (∑ d ∈ m.divisors, f p L (d % p)) / (m.divisors.card : ℚ) ≤
      (M : ℚ) / (p * Q * m.divisors.card) := by
  have ht : (0 : ℚ) < m.divisors.card := by
    exact_mod_cast card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm.ne'⟩
  have hden : (0 : ℚ) < p * Q := by positivity
  have hs : (p * Q : ℕ) * (∑ d ∈ m.divisors, f p L (d % p)) ≤ (M : ℚ) := by
    calc
      _ = ∑ d ∈ m.divisors, (p * Q : ℕ) * f p L (d % p) := by rw [mul_sum]
      _ ≤ ∑ d ∈ m.divisors, (B (d % p) : ℚ) := sum_le_sum hB
      _ = ((∑ d ∈ m.divisors, B (d % p) : ℕ) : ℚ) := by push_cast; rfl
      _ ≤ M := by exact_mod_cast hM
  apply (div_le_iff₀ ht).mpr
  have hbound : (∑ d ∈ m.divisors, f p L (d % p)) ≤ (M : ℚ) / (p * Q) := by
    apply (le_div_iff₀ hden).mpr
    simpa only [Nat.cast_mul, mul_comm] using hs
  calc
    _ ≤ (M : ℚ) / (p * Q) := hbound
    _ = (M : ℚ) / (p * Q * m.divisors.card) * m.divisors.card := by field_simp

/-- A fully checked integer residue total closes the conditional exponent-one branch. -/
theorem residue_integer_closes {p ell Q m M : ℕ} {B : ℕ → ℕ}
    (hp : p.Prime) (hpm : ¬p ∣ m)
    (hcheck : residueKernelCheck p ell Q (m.divisors.card) M = true)
    (hB : ∀ d ∈ m.divisors,
      (p * Q : ℕ) * f p (ell * p) (d % p) ≤ (B (d % p) : ℚ))
    (hM : ∑ d ∈ m.divisors, B (d % p) ≤ M)
    (hA : hHat m ≤ (m.divisors.card : ℚ)) :
    hHat (p * m) < ((p * m).divisors.card : ℚ) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (by
    intro hzero
    exact hpm (hzero ▸ dvd_zero p))
  obtain ⟨_, he, hQ, _, _, _⟩ := of_decide_eq_true hcheck
  have hF := residue_average_of_integer_bound hp.pos hQ hm hB hM
  have ht : KernelTest 1 p ((ell * p : ℕ) : ℚ) 1 1
      ((M : ℚ) / (p * Q * m.divisors.card)) := by
    simpa only [Nat.cast_mul] using residueKernelCheck_sound hcheck
  have hB' : hHat ((p ^ 1 * m) / p) ≤ (1 : ℚ) * 1 * m.divisors.card := by
    simpa only [pow_one, Nat.mul_div_right _ hp.pos, one_mul] using hA
  have hh := kernel_criterion_residue_average (bA := 1) (bB := 1)
    hp hpm
    (mul_pos he hp.pos) (by simpa using hA) hB' hF ht
  simpa using hh

/-- Rounded residue totals also certify lifts with distinct rational input bounds. -/
private theorem lift_integer_closes {a p ell D A B Q m M : ℕ} {V : ℕ → ℕ}
    (hp : p.Prime) (hm : 0 < m) (hpm : ¬p ∣ m)
    (hcheck : liftKernelCheck a p ell D A B Q (m.divisors.card) M = true)
    (hV : ∀ d ∈ m.divisors,
      (p * Q : ℕ) * f p (ell * p) (d % p) ≤ (V (d % p) : ℚ))
    (hM : ∑ d ∈ m.divisors, V (d % p) ≤ M)
    (hA : hHat m ≤ ((A : ℚ) / D) * m.divisors.card)
    (hB : hHat ((p ^ a * m) / p) ≤ ((B : ℚ) / D) * a * m.divisors.card) :
    hHat (p ^ a * m) < ((p ^ a * m).divisors.card : ℚ) := by
  obtain ⟨_, he, _, hQ, _, _, _⟩ := of_decide_eq_true hcheck
  have hF := residue_average_of_integer_bound hp.pos hQ hm hV hM
  have ht : KernelTest a p ((ell * p : ℕ) : ℚ) ((A : ℚ) / D) ((B : ℚ) / D)
      ((M : ℚ) / (p * Q * m.divisors.card)) := by
    simpa only [Nat.cast_mul] using liftKernelCheck_sound hcheck
  exact kernel_criterion_residue_average hp hpm (mul_pos he hp.pos) hA hB hF ht

#print axioms lift_integer_closes

private theorem residue_sum_list_finset (ds : List ℕ) (hd : ds.Nodup)
    (g : ℕ → ℕ) : (ds.map g).sum = ∑ d ∈ ds.toFinset, g d := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have hh := List.nodup_cons.mp hd
    simp [List.toFinset_cons, hh.1, ih hh.2]

/-- An arbitrary unknown suffix costs at most its cardinality in the numerator. -/
private theorem residue_prefix_integer_bound {p M m : ℕ} {B : ℕ → ℕ}
    (hp : 0 < p) (ds es : List ℕ)
    (hd : (residueProducts ds es).Nodup)
    (he : (residueProducts ds es).toFinset = m.divisors)
    (hcheck : residueVectorCheck p B ds M = true) :
    ∑ d ∈ m.divisors, B (d % p) ≤ es.length * M := by
  have h := residueSum_products_le hp B ds es (residueVectorCheck_sound hcheck) 1
  have heq : residueSum p B (residueProducts ds es) 1 =
      ∑ d ∈ m.divisors, B (d % p) := by
    simp only [residueSum, one_mul]
    rw [residue_sum_list_finset _ hd, he]
  rwa [heq] at h

/-- The unknown suffix divisor count cancels out of the residue average (18). -/
private theorem residue_prefix_average {p L Q M m : ℕ} {B : ℕ → ℕ}
    (hp : 0 < p) (hQ : 0 < Q) (hm : 0 < m) (ds es : List ℕ)
    (hds : 0 < ds.length) (hes : 0 < es.length)
    (hd : (residueProducts ds es).Nodup)
    (he : (residueProducts ds es).toFinset = m.divisors)
    (ht : m.divisors.card = ds.length * es.length)
    (hcheck : residueVectorCheck p B ds M = true)
    (hB : ∀ d ∈ m.divisors, (p * Q : ℕ) * f p L (d % p) ≤ (B (d % p) : ℚ)) :
    (∑ d ∈ m.divisors, f p L (d % p)) / (m.divisors.card : ℚ) ≤
      (M : ℚ) / (p * Q * ds.length) := by
  have hnum := residue_prefix_integer_bound hp ds es hd he hcheck
  have h := residue_average_of_integer_bound hp hQ hm hB hnum
  apply h.trans_eq
  rw [ht]
  push_cast
  have hdsq : (ds.length : ℚ) ≠ 0 := by exact_mod_cast hds.ne'
  have hesq : (es.length : ℚ) ≠ 0 := by exact_mod_cast hes.ne'
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hQq : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  field_simp
  <;> ring

/-- A prefix closure certifies every compatible suffix with the same induction bound. -/
theorem residue_prefix_closes {p ell Q M m : ℕ} {B : ℕ → ℕ}
    (hp : p.Prime) (hpm : ¬p ∣ m) (ds es : List ℕ)
    (hd : (residueProducts ds es).Nodup)
    (he : (residueProducts ds es).toFinset = m.divisors)
    (hvector : residueVectorCheck p B ds M = true)
    (hkernel : residueKernelCheck p ell Q ds.length M = true)
    (hB : ∀ d ∈ m.divisors,
      (p * Q : ℕ) * f p (ell * p) (d % p) ≤ (B (d % p) : ℚ))
    (hA : hHat m ≤ (m.divisors.card : ℚ)) :
    hHat (p * m) < ((p * m).divisors.card : ℚ) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (by
    intro hzero
    exact hpm (hzero ▸ dvd_zero p))
  obtain ⟨_, hell, hQ, hds, _, _⟩ := of_decide_eq_true hkernel
  have ht : m.divisors.card = ds.length * es.length := by
    rw [← he, List.toFinset_card_of_nodup hd]
    simp [residueProducts, Nat.mul_comm]
  have hcard : 0 < m.divisors.card :=
    card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm.ne'⟩
  have hes : 0 < es.length := by rw [ht] at hcard; nlinarith
  have hF := residue_prefix_average hp.pos hQ hm ds es hds hes hd he ht hvector hB
  have htest : KernelTest 1 p ((ell * p : ℕ) : ℚ) 1 1
      ((M : ℚ) / (p * Q * ds.length)) := by
    simpa only [Nat.cast_mul] using residueKernelCheck_sound hkernel
  have hB' : hHat ((p ^ 1 * m) / p) ≤ (1 : ℚ) * 1 * m.divisors.card := by
    simpa only [pow_one, Nat.mul_div_right _ hp.pos, one_mul] using hA
  have hh := kernel_criterion_residue_average (bA := 1) (bB := 1)
    hp hpm
    (mul_pos hell hp.pos) (by simpa using hA) hB' hF htest
  simpa using hh

#print axioms residue_prefix_integer_bound
#print axioms residue_prefix_average
#print axioms residue_prefix_closes

#print axioms residueVectorCheck_sound
#print axioms residue_average_of_integer_bound
#print axioms residue_integer_closes

#print axioms residueSum_products
#print axioms residueSum_products_le

#print axioms liftKernelCheck_sound

#print axioms residueKernelCheck_sound

end D5.S3.Arith.ErdosNicolas
