/- GID: D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture
   generality: I
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Braun-Bruegge facet-sum conjecture 5.1 settlement. -/

/-
   result: proof_shape: bind-only; escape_witness: none
   Escape audit unfinished for result: https://github.com/the-omega-institute/trureturing/issues/20246
   admission_basis: open-problem-resolution (#19695; Proved)
   Direct frozen dependencies (declaration statement_id):
     _private.D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.0.D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.choose_le_of_middle
       sha256:27cfe8295f57799ed3c72613ef396f1acef3d828bb7b8e80b114d73d9baf6381
   The public claim keeps the preregistered facet-sum and admissibility expressions literally;
   the private row proof uses the frozen binomial monotonicity owner through `open private`.
   Declarations: public F, Admissible, claim, result; all transfer and normalization helpers
   are private and consumed by the settling proof.
-/

import D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound

open scoped BigOperators

namespace D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture

namespace BraunBrueggeTransfer

/-- Positive increments have weights at least as large as all negative increments. -/
private theorem single_crossing_weighted_sum_nonneg {ι : Type*} (s : Finset ι)
    (δ w : ι → ℚ) (hzero : ∑ i ∈ s, δ i = 0)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, 0 < δ i → δ j < 0 → w j ≤ w i) :
    0 ≤ ∑ i ∈ s, w i * δ i := by
  classical
  by_cases hp : ∃ i ∈ s, 0 < δ i
  · let pos := s.filter (fun i => 0 < δ i)
    have hpos : pos.Nonempty := by
      exact Finset.filter_nonempty_iff.mpr hp
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image pos w hpos
    have hi' := Finset.mem_filter.mp hi
    have hnonneg : ∀ j ∈ s, 0 ≤ (w j - w i) * δ j := by
      intro j hj
      rcases lt_trichotomy (δ j) 0 with hn | hz | hp
      · exact mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr (hcross i hi'.1 j hj hi'.2 hn)) hn.le
      · simp [hz]
      · exact mul_nonneg (sub_nonneg.mpr (hmin j (Finset.mem_filter.mpr ⟨hj, hp⟩))) hp.le
    have h := Finset.sum_nonneg hnonneg
    simpa only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, mul_zero,
      sub_zero] using h
  · have hnonpos : ∀ i ∈ s, δ i ≤ 0 := by
      intro i hi
      exact le_of_not_gt (fun h => hp ⟨i, hi, h⟩)
    have hz : ∀ i ∈ s, δ i = 0 := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hzero
    have hs : ∑ i ∈ s, w i * δ i = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hz i hi, mul_zero])
    rw [hs]


end BraunBrueggeTransfer

open private choose_le_of_middle from D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound

namespace BraunBrueggeTransfer

/-- Centered row, indexed by a nonnegative distance from the center. -/
private def row (m r : ℕ) : ℚ :=
  if r ≤ m ∧ m % 2 = r % 2 then (m.choose ((m-r)/2) : ℚ) else 0

private lemma row_nonneg (m r : ℕ) : 0 ≤ row m r := by
  unfold row
  split_ifs <;> positivity

private lemma row_eq_zero_of_lt {m r : ℕ} (h : m < r) : row m r = 0 := by
  simp [row, not_le.mpr h]

private lemma row_pos_iff (m r : ℕ) : 0 < row m r ↔ r ≤ m ∧ m % 2 = r % 2 := by
  unfold row
  split_ifs with h
  · constructor
    · exact fun _ => h
    · intro _
      exact_mod_cast Nat.choose_pos ((Nat.div_le_self (m-r) 2).trans (Nat.sub_le m r))
  · simp [h]

private lemma choose_mono_left_half {m k l : ℕ} (hkl : k ≤ l) (hl : l ≤ m/2) :
    m.choose k ≤ m.choose l := by
  exact choose_le_of_middle hkl (by omega)

private lemma row_antitone_same_parity {m r s : ℕ} (hrs : r ≤ s)
    (hpar : m % 2 = r % 2) (hpar' : m % 2 = s % 2) : row m s ≤ row m r := by
  by_cases hs : s ≤ m
  · have hr : r ≤ m := hrs.trans hs
    simp only [row, ite_eq_left (And.intro hs hpar'), ite_eq_left (And.intro hr hpar)]
    exact_mod_cast choose_mono_left_half
      (Nat.div_le_div_right (by omega : m-s ≤ m-r))
      (Nat.div_le_div_right (Nat.sub_le m r))
  · rw [row_eq_zero_of_lt (by omega)]
    exact row_nonneg _ _

/-- The cross-multiplied two-row raising identity. -/
private lemma choose_raise_two (m k : ℕ) (hk : k ≤ m) :
    ((m+2).choose (k+1) : ℚ) * (k+1) * (m+1-k) =
      (m.choose k : ℚ) * (m+1) * (m+2) := by
  have h₁ := Nat.add_one_mul_choose_eq m k
  have h₂ := Nat.choose_mul_succ_eq (m+1) (k+1)
  have he : m+1+1-(k+1) = m+1-k := by exact Nat.add_sub_add_right (m + 1) 1 k
  rw [he] at h₂
  have h₁' : (m+1 : ℚ) * (m.choose k : ℚ) =
      ((m+1).choose (k+1) : ℚ) * (k+1) := by exact_mod_cast h₁
  have h₂' : ((m+1).choose (k+1) : ℚ) * ((m+2 : ℕ) : ℚ) =
      ((m+2).choose (k+1) : ℚ) * ((m+1-k : ℕ) : ℚ) := by
    exact_mod_cast (by simpa [Nat.add_assoc] using h₂)
  rw [Nat.cast_sub (by omega : k ≤ m+1)] at h₂'
  push_cast at h₂'
  calc
    _ = (((m+2).choose (k+1) : ℚ) * ((m : ℚ)+1-k)) * (k+1) := by ring
    _ = (((m+1).choose (k+1) : ℚ) * ((m : ℚ)+2)) * (k+1) := by rw [← h₂']
    _ = (((m+1).choose (k+1) : ℚ) * (k+1)) * ((m : ℚ)+2) := by ring
    _ = _ := by rw [← h₁']; ring

/-- Row raising in centered coordinates; no quotient occurs in the conclusion. -/
private lemma row_raise_two {m r : ℕ} (hr : r ≤ m) (hp : m%2 = r%2) :
    row (m+2) r * (((m : ℚ)+2)^2 - (r : ℚ)^2) =
      4 * ((m : ℚ)+2) * ((m : ℚ)+1) * row m r := by
  let k := (m-r)/2
  have hm : m = 2*k+r := by dsimp [k]; omega
  have he : (m+2-r)/2 = k+1 := by omega
  have hpar : (m+2)%2 = r%2 := by exact (Nat.add_mod_right m 2).trans hp
  have hk : k ≤ m := by exact (Nat.div_le_self (m-r) 2).trans (Nat.sub_le m r)
  have h := choose_raise_two m k hk
  have hm' : (m : ℚ) = 2*(k : ℚ)+r := by exact_mod_cast hm
  have hr' : r ≤ m+2 := by exact Nat.le_add_right_of_le hr
  simp only [row, hr', hpar, hr, hp, and_self, ↓reduceIte, he]
  change ((m+2).choose (k+1) : ℚ) * (((m : ℚ)+2)^2-(r : ℚ)^2) =
    4*((m : ℚ)+2)*((m : ℚ)+1)*(m.choose k : ℚ)
  have hid : ((m : ℚ)+2)^2-(r : ℚ)^2 =
      4*((k : ℚ)+1)*((m : ℚ)+1-k) := by rw [hm']; ring
  rw [hid]
  calc
    _ = 4 * (((m+2).choose (k+1) : ℚ) * (k+1) * ((m : ℚ)+1-k)) := by ring
    _ = _ := by rw [h]; ring


end BraunBrueggeTransfer

open scoped BigOperators
namespace BraunBrueggeTransfer

private lemma sum_even_symmetric (n : ℕ) (f : ℕ → ℚ)
    (hf : ∀ j ≤ 2*n, f (2*n-j) = f j) :
    (∑ j ∈ Finset.range (2*n+1), f j) = f n + 2 * ∑ j ∈ Finset.range n, f j := by
  have htail : (∑ j ∈ Finset.range n, f (n+1+j)) = ∑ j ∈ Finset.range n, f j := by
    calc
      _ = ∑ j ∈ Finset.range n, f (n-1-j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [← hf (n+1+j) (by omega)]
        congr 1
        omega
      _ = _ := Finset.sum_range_reflect f n
  rw [show 2*n+1 = (n+1)+n by omega, Finset.sum_range_add, Finset.sum_range_succ,
    htail]
  ring

private lemma sum_odd_symmetric (n : ℕ) (f : ℕ → ℚ)
    (hf : ∀ j ≤ 2*n+1, f (2*n+1-j) = f j) :
    (∑ j ∈ Finset.range (2*n+2), f j) = 2 * ∑ j ∈ Finset.range (n+1), f j := by
  have htail : (∑ j ∈ Finset.range (n+1), f (n+1+j)) =
      ∑ j ∈ Finset.range (n+1), f j := by
    calc
      _ = ∑ j ∈ Finset.range (n+1), f (n-j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [← hf (n+1+j) (by omega)]
        congr 1
        omega
      _ = _ := by simpa using Finset.sum_range_reflect f (n+1)
  rw [show 2*n+2 = (n+1)+(n+1) by omega, Finset.sum_range_add, htail]
  ring

/-- Multiplicity of a distance on the even or odd lattice. -/
private def latticeMultiplicity (e i : ℕ) : ℚ := if e=0 ∧ i=0 then 1 else 2

private lemma latticeMultiplicity_pos (e i : ℕ) : 0 < latticeMultiplicity e i := by
  unfold latticeMultiplicity
  split_ifs <;> norm_num

private lemma reflected_even_sum (n : ℕ) (f : ℕ → ℚ) :
    (∑ i ∈ Finset.range (n+1), latticeMultiplicity 0 i * f (n-i)) =
      f n + 2 * ∑ j ∈ Finset.range n, f j := by
  rw [Finset.sum_range_succ']
  simp only [latticeMultiplicity, and_self, ite_true, Nat.sub_zero, one_mul,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
  rw [← Finset.mul_sum]
  have h : (∑ i ∈ Finset.range n, f (n-(i+1))) = ∑ j ∈ Finset.range n, f j := by
    convert Finset.sum_range_reflect f n using 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    omega
  rw [h]
  ring

private lemma reflected_odd_sum (n : ℕ) (f : ℕ → ℚ) :
    (∑ i ∈ Finset.range (n+1), latticeMultiplicity 1 i * f (n-i)) =
      2 * ∑ j ∈ Finset.range (n+1), f j := by
  simp only [latticeMultiplicity, Nat.one_ne_zero, false_and, ite_false]
  rw [← Finset.mul_sum]
  congr 1
  simpa using Finset.sum_range_reflect f (n+1)

end BraunBrueggeTransfer

namespace BraunBrueggeTransfer
private lemma sum_symmetric_compression (e C : ℕ) (he : e ≤ 1) (f g : ℕ → ℚ)
    (hf : ∀ j ≤ 2*C+e, f (2*C+e-j) = f j)
    (hg : ∀ i ≤ C, g i = f (C-i)) :
    (∑ i ∈ Finset.range (C+1), latticeMultiplicity e i * g i) =
      ∑ j ∈ Finset.range (2*C+e+1), f j := by
  have hs : (∑ i ∈ Finset.range (C+1), latticeMultiplicity e i * g i) =
      ∑ i ∈ Finset.range (C+1), latticeMultiplicity e i * f (C-i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hg i (by simpa using hi)]
  rw [hs]
  rcases e with _ | e
  · simpa only [Nat.add_zero] using
      (reflected_even_sum C f).trans (sum_even_symmetric C f (by simpa using hf)).symm
  · have he' : e=0 := by exact Nat.lt_one_iff.mp he
    subst e
    simpa only [Nat.zero_add, Nat.add_assoc] using
      (reflected_odd_sum C f).trans (sum_odd_symmetric C f (by simpa using hf)).symm

end BraunBrueggeTransfer

namespace BraunBrueggeTransfer

private lemma row_lower_two {c r : ℕ} (hc : 2 ≤ c) (hr : r ≤ c) (hp : c%2=r%2) :
    row c r * ((c : ℚ)^2-(r : ℚ)^2) =
      4*(c : ℚ)*((c : ℚ)-1)*row (c-2) r := by
  by_cases he : r=c
  · subst r
    rw [row_eq_zero_of_lt (by omega : c-2<c)]
    ring
  · have hr' : r ≤ c-2 := by omega
    have hp' : (c-2)%2=r%2 := by omega
    have h := row_raise_two hr' hp'
    have hec : c-2+2=c := by exact Nat.sub_add_cancel hc
    have hec' : ((c-2 : ℕ) : ℚ) = (c : ℚ)-2 := by exact Nat.cast_sub hc
    rw [hec, hec'] at h
    convert h using 1 <;> ring

/-- Signed change in the paired centered mass under transfer. -/
private def delta (a c r : ℕ) : ℚ := row (a+2) r * row (c-2) r - row a r * row c r

private lemma delta_support {a c r : ℕ} (hc : 2 ≤ c) (hd : delta a c r ≠ 0) :
    r ≤ c ∧ c%2=r%2 := by
  by_cases hr : r ≤ c
  · refine ⟨hr, ?_⟩
    by_contra hp
    have hp' : (c-2)%2 ≠ r%2 := by omega
    have hz : row c r = 0 := by simp [row, hp]
    have hz' : row (c-2) r = 0 := by simp [row, hp']
    exact hd (by simp [delta, hz, hz'])
  · have hz : row c r = 0 := row_eq_zero_of_lt (by omega)
    have hz' : row (c-2) r = 0 := row_eq_zero_of_lt (by omega)
    exact False.elim (hd (by simp [delta, hz, hz']))

private lemma delta_identity {a c r : ℕ} (hc : 2 ≤ c) (ha : c ≤ a)
    (hp : a%2=c%2) (hr : r ≤ c) (hpr : c%2=r%2) :
    delta a c r * ((c : ℚ)*((c : ℚ)-1)*(((a : ℚ)+2)^2-(r : ℚ)^2)) =
      row a r * row c r * ((a : ℚ)+2-c) *
        ((c : ℚ)*((a : ℚ)+2)-((a : ℚ)+c+1)*(r : ℚ)^2) := by
  have h₁ := row_raise_two (hr.trans ha) (hp.trans hpr)
  have h₂ := row_lower_two hc hr hpr
  have hprod :
      4 * (row (a+2) r * row (c-2) r *
        ((c : ℚ)*((c : ℚ)-1)*(((a : ℚ)+2)^2-(r : ℚ)^2))) =
      4 * (((a : ℚ)+2)*((a : ℚ)+1)*((c : ℚ)^2-(r : ℚ)^2)*
        (row a r * row c r)) := by
    calc
      _ = (row (a+2) r * (((a : ℚ)+2)^2-(r : ℚ)^2)) *
        (4*(c : ℚ)*((c : ℚ)-1)*row (c-2) r) := by ring
      _ = _ := by rw [h₁, ← h₂]; ring
  have he := mul_left_cancel₀ (by norm_num : (4 : ℚ) ≠ 0) hprod
  unfold delta
  rw [sub_mul, he]
  ring

private lemma delta_sign {a c r : ℕ} (hc : 3 ≤ c) (ha : c ≤ a)
    (hp : a%2=c%2) (hr : r ≤ c) (hpr : c%2=r%2) :
    (0 < delta a c r ↔ 0 < (c : ℚ)*((a : ℚ)+2)-((a : ℚ)+c+1)*(r : ℚ)^2) ∧
    (delta a c r < 0 ↔ (c : ℚ)*((a : ℚ)+2)-((a : ℚ)+c+1)*(r : ℚ)^2 < 0) := by
  have hca : (c : ℚ) ≤ a := by exact_mod_cast ha
  have hrc : (r : ℚ) ≤ c := by exact_mod_cast hr
  have hc' : (3 : ℚ) ≤ c := by exact_mod_cast hc
  have hsq : 0 < ((a : ℚ)+2)^2-(r : ℚ)^2 := by
    exact sub_pos.mpr ((sq_lt_sq₀ (Nat.cast_nonneg r) (by positivity)).2 (by linarith))
  have hden : 0 < (c : ℚ)*((c : ℚ)-1)*(((a : ℚ)+2)^2-(r : ℚ)^2) :=
    mul_pos (mul_pos (by linarith) (by linarith)) hsq
  have hq : 0 < row a r * row c r * ((a : ℚ)+2-c) := by
    exact mul_pos (mul_pos ((row_pos_iff _ _).mpr ⟨hr.trans ha,hp.trans hpr⟩)
      ((row_pos_iff _ _).mpr ⟨hr,hpr⟩)) (by linarith)
  have hid := delta_identity (by omega : 2 ≤ c) ha hp hr hpr
  constructor
  · have h : 0 < delta a c r *
        ((c : ℚ)*((c : ℚ)-1)*(((a : ℚ)+2)^2-(r : ℚ)^2)) ↔
        0 < (c : ℚ)*((a : ℚ)+2)-((a : ℚ)+c+1)*(r : ℚ)^2 := by
      rw [hid, mul_pos_iff_of_pos_left hq]
    simpa only [mul_pos_iff_of_pos_right hden] using h
  · have h : delta a c r *
        ((c : ℚ)*((c : ℚ)-1)*(((a : ℚ)+2)^2-(r : ℚ)^2)) < 0 ↔
        (c : ℚ)*((a : ℚ)+2)-((a : ℚ)+c+1)*(r : ℚ)^2 < 0 := by
      rw [hid]
      simpa only [mul_zero] using
        (mul_lt_mul_iff_right₀ (b := (c : ℚ)*((a : ℚ)+2)-((a : ℚ)+c+1)*(r : ℚ)^2)
          (c := 0) hq)
    have hneg : delta a c r *
        ((c : ℚ)*((c : ℚ)-1)*(((a : ℚ)+2)^2-(r : ℚ)^2)) < 0 ↔ delta a c r < 0 := by
      simpa only [zero_mul] using
        (mul_lt_mul_iff_left₀ (b := delta a c r) (c := 0) hden)
    exact hneg.symm.trans h

/-- Every positive increment lies strictly closer to the center than every negative increment. -/
private lemma delta_single_crossing {a c r s : ℕ} (hc : 3 ≤ c) (ha : c ≤ a)
    (hp : a%2=c%2) (hr : 0 < delta a c r) (hs : delta a c s < 0) : r < s := by
  obtain ⟨hrc, hpr⟩ := delta_support (by omega : 2 ≤ c) (ne_of_gt hr)
  obtain ⟨hsc, hps⟩ := delta_support (by omega : 2 ≤ c) (ne_of_lt hs)
  have hr' := (delta_sign hc ha hp hrc hpr).1.mp hr
  have hs' := (delta_sign hc ha hp hsc hps).2.mp hs
  by_contra h
  have hsr : (s : ℚ) ≤ r := by exact_mod_cast (show s ≤ r by omega)
  have hsq : (s : ℚ)^2 ≤ (r : ℚ)^2 := by exact pow_le_pow_left₀ (Nat.cast_nonneg s) hsr 2
  have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (a : ℚ)+c+1)
  linarith

end BraunBrueggeTransfer
namespace BraunBrueggeTransfer

/-- Centered row in half-size coordinates. -/
private lemma row_half {m e i : ℕ} (hi : i ≤ m) :
    row (2*m+e) (2*i+e) = ((2*m+e).choose (m-i) : ℚ) := by
  have hbound : 2*i+e ≤ 2*m+e := by exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hi) e
  have hpar : (2*m+e)%2=(2*i+e)%2 := by simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
  have hind : (2*m+e-(2*i+e))/2=m-i := by
    simpa only [Nat.add_sub_add_right, ← Nat.mul_sub_left_distrib] using Nat.mul_div_cancel_left (m-i) (by decide : 0<2)
  simp [row, hbound, hpar, hind]

/-- Vandermonde with reflected indices, in precisely the pairing used by the transfer. -/
private lemma pair_vandermonde {a c : ℕ} (ha : c ≤ a) (hp : a%2=c%2) :
    (∑ j ∈ Finset.range (c+1), (c.choose j : ℚ) * (a.choose ((a-c)/2+j) : ℚ)) =
      ((a+c).choose ((a+c)/2) : ℚ) := by
  let d := (a-c)/2
  let K := (a+c)/2
  have had : a=c+2*d := by dsimp [d]; omega
  have hK : K=c+d := by dsimp [K,d]; omega
  have hn : (∑ j ∈ Finset.range (c+1), c.choose j * a.choose (d+j)) =
      (a+c).choose K := by
    calc
      _ = ∑ j ∈ Finset.range (c+1), c.choose j * a.choose (K-j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjc : j ≤ c := by simpa using hj
        rw [← Nat.choose_symm (by omega : d+j ≤ a)]
        congr 2
        omega
      _ = ∑ j ∈ Finset.range (K+1), c.choose j * a.choose (K-j) := by
        have hsub : Finset.range (c+1) ⊆ Finset.range (K+1) :=
          Finset.range_subset_range.mpr (by omega)
        apply Finset.sum_subset hsub
        intro j hj hn
        have hjc : c<j := by simp only [Finset.mem_range] at hn; omega
        rw [Nat.choose_eq_zero_of_lt hjc, zero_mul]
      _ = (a+c).choose K := by
        rw [Nat.add_comm a c, Nat.add_choose_eq,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact_mod_cast hn

/-- Finite mass of two centered rows, with each radius counted at its lattice latticeMultiplicity. -/
private def pairMass (e N a c : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (N+1), latticeMultiplicity e i * row a (2*i+e) * row c (2*i+e)

private lemma pair_mass_vandermonde {e N A C : ℕ} (he : e ≤ 1) (hCA : C ≤ A) (hCN : C ≤ N) :
    pairMass e N (2*A+e) (2*C+e) =
      ((2*A+e+ (2*C+e)).choose ((2*A+e+(2*C+e))/2) : ℚ) := by
  let a := 2*A+e
  let c := 2*C+e
  let d := (a-c)/2
  let f : ℕ → ℚ := fun j => (c.choose j : ℚ) * (a.choose (d+j) : ℚ)
  have ha : c ≤ a := by exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hCA) e
  have hp : a%2=c%2 := by simp only [a, c, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
  have hd : d=A-C := by dsimp [d,a,c]; omega
  have hsym : ∀ j ≤ c, f (c-j) = f j := by
    intro j hj
    dsimp [f]
    rw [Nat.choose_symm hj]
    have hind : d+(c-j)=a-(d+j) := by dsimp [d,a,c]; omega
    rw [hind, Nat.choose_symm (by dsimp [d,a,c]; omega : d+j ≤ a)]
  have hterms : ∀ i ≤ C, row a (2*i+e) * row c (2*i+e) = f (C-i) := by
    intro i hi
    dsimp [a,c,f]
    rw [row_half (hi.trans hCA), row_half hi]
    have hind : d+(C-i)=A-i := by omega
    rw [hind]
    ring
  have hsmall : pairMass e N a c = pairMass e C a c := by
    unfold pairMass
    symm
    have hsub : Finset.range (C+1) ⊆ Finset.range (N+1) := by
      exact Finset.range_mono (Nat.add_le_add_right hCN 1)
    apply Finset.sum_subset hsub
    intro i hi hn
    have hgt : c < 2*i+e := by dsimp [c]; simp only [Finset.mem_range] at hn; omega
    rw [row_eq_zero_of_lt hgt, mul_zero]
  rw [hsmall]
  calc
    pairMass e C a c = ∑ j ∈ Finset.range (c+1), f j := by
      unfold pairMass
      simp_rw [mul_assoc]
      exact sum_symmetric_compression e C he f
        (fun i => row a (2*i+e)*row c (2*i+e)) hsym hterms
    _ = _ := pair_vandermonde ha hp

private lemma pair_mass_transfer {e N a c : ℕ} (he : e ≤ 1) (hc : 3 ≤ c)
    (ha : c ≤ a) (hp : a%2=c%2) (hcp : c%2=e) (hN : c/2 ≤ N) :
    pairMass e N (a+2) (c-2) = pairMass e N a c := by
  have haform : a=2*(a/2)+e := by
    exact (Nat.div_add_mod a 2).symm.trans (congrArg (fun t => 2*(a/2)+t) (hp.trans hcp))
  have hcform : c=2*(c/2)+e := by simpa only [hcp] using (Nat.div_add_mod c 2).symm
  have haform' : a+2=2*((a+2)/2)+e := by
    simpa only [Nat.add_mod_right, hp, hcp] using (Nat.div_add_mod (a+2) 2).symm
  have hcform' : c-2=2*((c-2)/2)+e := by omega
  have h₁ := pair_mass_vandermonde he (by omega : c/2 ≤ a/2) hN
  have h₂ := pair_mass_vandermonde he (by omega : (c-2)/2 ≤ (a+2)/2)
    (by omega : (c-2)/2 ≤ N)
  rw [← haform, ← hcform] at h₁
  rw [← haform', ← hcform'] at h₂
  rw [h₁,h₂]
  congr 2 <;> omega

end BraunBrueggeTransfer

/-! Binding conventions for B. Braun and K. Bruegge, "Facets of Symmetric Edge Polytopes for Graphs with Few Edges",
arXiv:2201.13303v4: the facet count `F(m₁, m₂, m₃) = ∑_{j=0}^{m₃} C(m₃, j) ∏_{k=1}^{2} C(m_k, (m_k − m₃)/2 + j)` of
Proposition 4.4 for `m₁ ≥ m₂ ≥ m₃` of a common parity, and Conjecture 5.1: for `n = 2k`, `k ≥ 2`, and
`x₁ + x₂ + x₃ = n + 1`, `F` is maximized at `F(n − 1, 1, 1)`; for `n = 2k − 1`, `k ≥ 3`, at `F(n − 3, 2, 2)`; and for
`x₁ ≥ x₂ ≥ x₃ ≥ 3` all even or all odd, `F(x₁, x₂, x₃) ≤ F(x₁ + 2, x₂, x₃ − 2)` and `F(x₁, x₂, x₃) ≤ F(x₁ + 2, x₂ − 2, x₃)`
"when the subtraction by 2 will maintain the inequalities on the `xᵢ`'s". -/


/-- Proposition 4.4 with `t = 3`: for `a ≥ b ≥ c` of a common parity,
`F(a, b, c) = ∑_{j=0}^{c} C(c, j) C(b, (b − c)/2 + j) C(a, (a − c)/2 + j)`. -/
def F (a b c : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (c + 1), c.choose j * b.choose ((b - c) / 2 + j) * a.choose ((a - c) / 2 + j)

/-- Positive integers `a ≥ b ≥ c ≥ 1`, all even or all odd: the domain of `F` in Proposition 4.4. -/
def Admissible (a b c : ℕ) : Prop :=
  b ≤ a ∧ c ≤ b ∧ 1 ≤ c ∧ a % 2 = b % 2 ∧ b % 2 = c % 2

/-- Conjecture 5.1, all four assertions. -/
def claim : Prop :=
  (∀ k : ℕ, 2 ≤ k → ∀ a b c : ℕ, Admissible a b c → a + b + c = 2 * k + 1 →
      F a b c ≤ F (2 * k - 1) 1 1) ∧
    (∀ k : ℕ, 3 ≤ k → ∀ a b c : ℕ, Admissible a b c → a + b + c = 2 * k - 1 + 1 →
      F a b c ≤ F (2 * k - 1 - 3) 2 2) ∧
    (∀ a b c : ℕ, Admissible a b c → 3 ≤ c → F a b c ≤ F (a + 2) b (c - 2)) ∧
    (∀ a b c : ℕ, Admissible a b c → 3 ≤ c → c ≤ b - 2 → F a b c ≤ F (a + 2) (b - 2) c)


/-- Strong induction reduces every same-parity triple to its minimal two coordinates. -/
private theorem maximum_of_transfers
    (h₁ : ∀ a b c : ℕ, Admissible a b c → 3 ≤ c →
      F a b c ≤ F (a+2) b (c-2))
    (h₂ : ∀ a b c : ℕ, Admissible a b c → 3 ≤ b → c ≤ b-2 →
      F a b c ≤ F (a+2) (b-2) c)
    (q : ℕ) (hq : q=1 ∨ q=2) :
    ∀ a b c : ℕ, Admissible a b c → c%2=q%2 →
      F a b c ≤ F (a+b+c-2*q) q q := by
  have H : ∀ m : ℕ, ∀ a b c : ℕ, b+c=m → Admissible a b c → c%2=q%2 →
      F a b c ≤ F (a+b+c-2*q) q q := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a b c hm had hp
      rcases had with ⟨hba, hcb, hc, hab, hbc⟩
      have hqc : q ≤ c := by rcases hq with rfl | rfl <;> omega
      by_cases hec : c=q
      · by_cases heb : b=q
        · subst c
          subst b
          have he : a+q+q-2*q=a := by omega
          rw [he]
        · have hb : q+2 ≤ b := by rcases hq with rfl | rfl <;> omega
          have had' : Admissible (a+2) (b-2) c := by
            refine ⟨by omega, by omega, hc, by omega, by omega⟩
          have hstep := h₂ a b c ⟨hba,hcb,hc,hab,hbc⟩ (by omega) (by omega)
          have hrec := ih ((b-2)+c) (by omega) (a+2) (b-2) c rfl had' hp
          have he : (a+2)+(b-2)+c-2*q=a+b+c-2*q := by omega
          rw [he] at hrec
          exact hstep.trans hrec
      · have hcg : q+2 ≤ c := by rcases hq with rfl | rfl <;> omega
        have had' : Admissible (a+2) b (c-2) := by
          refine ⟨by omega, by omega, by omega, by omega, by omega⟩
        have hp' : (c-2)%2=q%2 := by omega
        have hstep := h₁ a b c ⟨hba,hcb,hc,hab,hbc⟩ (by omega)
        have hrec := ih (b+(c-2)) (by omega) (a+2) b (c-2) rfl had' hp'
        have he : (a+2)+b+(c-2)-2*q=a+b+c-2*q := by omega
        rw [he] at hrec
        exact hstep.trans hrec
  intro a b c had hp
  exact H (b+c) a b c rfl had hp

/-- The strengthened second transfer includes the endpoint weights 1 and 2. -/
private theorem result_of_transfers
    (h₁ : ∀ a b c : ℕ, Admissible a b c → 3 ≤ c →
      F a b c ≤ F (a+2) b (c-2))
    (h₂ : ∀ a b c : ℕ, Admissible a b c → 3 ≤ b → c ≤ b-2 →
      F a b c ≤ F (a+2) (b-2) c) : claim := by
  refine ⟨?_, ?_, h₁, ?_⟩
  · intro k hk a b c had hsum
    have hp : c%2=1%2 := by
      rcases had with ⟨hba,hcb,hc,hab,hbc⟩
      omega
    have h := maximum_of_transfers h₁ h₂ 1 (Or.inl rfl) a b c had hp
    have he : a+b+c-2*1=2*k-1 := by omega
    simpa only [he] using h
  · intro k hk a b c had hsum
    have hp : c%2=2%2 := by
      rcases had with ⟨hba,hcb,hc,hab,hbc⟩
      omega
    have h := maximum_of_transfers h₁ h₂ 2 (Or.inr rfl) a b c had hp
    have he : a+b+c-2*2=2*k-1-3 := by omega
    simpa only [he] using h
  · intro a b c had hc hcb
    exact h₂ a b c had (by rcases had with ⟨_,h,_,_,_⟩; omega) hcb

open BraunBrueggeTransfer

/-- The finite symmetric expression used internally in the proof. -/
private def centeredSum (e N a b c : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (N+1), latticeMultiplicity e i * row a (2*i+e) *
    row b (2*i+e) * row c (2*i+e)

private lemma centered_sum_swap (e N a b c : ℕ) :
    centeredSum e N a b c = centeredSum e N a c b := by
  unfold centeredSum
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma F_eq_centered_sum {e N a b c : ℕ} (had : Admissible a b c)
    (he : e ≤ 1) (hcp : c%2=e) (hN : c/2 ≤ N) :
    (F a b c : ℚ) = centeredSum e N a b c := by
  rcases had with ⟨hba,hcb,hc,hab,hbc⟩
  let A := a/2
  let B := b/2
  let C := c/2
  let da := (a-c)/2
  let db := (b-c)/2
  have hCA : C ≤ A := by exact Nat.div_le_div_right (hcb.trans hba)
  have hCB : C ≤ B := by exact Nat.div_le_div_right hcb
  have haform : a=2*A+e := by simpa only [A, hab, hbc, hcp] using (Nat.div_add_mod a 2).symm
  have hbform : b=2*B+e := by simpa only [B, hbc, hcp] using (Nat.div_add_mod b 2).symm
  have hcform : c=2*C+e := by simpa only [C, hcp] using (Nat.div_add_mod c 2).symm
  have hda : da=A-C := by dsimp [da,A,C]; omega
  have hdb : db=B-C := by dsimp [db,B,C]; omega
  let f : ℕ → ℚ := fun j => (c.choose j : ℚ) * (b.choose (db+j) : ℚ) *
    (a.choose (da+j) : ℚ)
  have hsym : ∀ j ≤ c, f (c-j) = f j := by
    intro j hj
    dsimp [f]
    rw [Nat.choose_symm hj]
    have hia : da+(c-j)=a-(da+j) := by dsimp [da]; omega
    have hib : db+(c-j)=b-(db+j) := by dsimp [db]; omega
    rw [hia,hib, Nat.choose_symm (by dsimp [da]; omega : da+j ≤ a),
      Nat.choose_symm (by dsimp [db]; omega : db+j ≤ b)]
  have hterms : ∀ i ≤ C, row a (2*i+e)*row b (2*i+e)*row c (2*i+e) = f (C-i) := by
    intro i hi
    rw [haform,hbform,hcform,row_half (hi.trans hCA), row_half (hi.trans hCB),
      row_half hi]
    dsimp [f]
    have hia : da+(C-i)=A-i := by omega
    have hib : db+(C-i)=B-i := by omega
    rw [hia,hib,haform,hbform,hcform]
    ring
  have hsmall : centeredSum e N a b c = centeredSum e C a b c := by
    unfold centeredSum
    symm
    have hsub : Finset.range (C+1) ⊆ Finset.range (N+1) := by
      exact Finset.range_mono (Nat.add_le_add_right hN 1)
    apply Finset.sum_subset hsub
    intro i hi hn
    have hgt : c<2*i+e := by rw [hcform]; simp only [Finset.mem_range] at hn; omega
    rw [row_eq_zero_of_lt hgt,mul_zero]
  rw [hsmall]
  calc
    (F a b c : ℚ) = ∑ j ∈ Finset.range (c+1), f j := by
      simp only [F,Nat.cast_sum,Nat.cast_mul,f,da,db]
    _ = centeredSum e C a b c := by
      symm
      unfold centeredSum
      simp_rw [mul_assoc]
      simpa only [← hcform,mul_assoc] using sum_symmetric_compression e C he f
        (fun i => row a (2*i+e)*row b (2*i+e)*row c (2*i+e))
        (by simpa only [← hcform] using hsym) hterms

/-- The actual transfer, for any binomial weight on the common parity lattice. -/
private theorem centered_transfer {e N a b c : ℕ} (he : e ≤ 1) (hc : 3 ≤ c)
    (ha : c ≤ a) (hp : a%2=c%2) (hcp : c%2=e) (hbp : b%2=e) (hN : c/2 ≤ N) :
    centeredSum e N a b c ≤ centeredSum e N (a+2) b (c-2) := by
  let d : ℕ → ℚ := fun i => latticeMultiplicity e i * delta a c (2*i+e)
  have hmass := pair_mass_transfer he hc ha hp hcp hN
  have hzero : ∑ i ∈ Finset.range (N+1), d i = 0 := by
    simp_rw [d, delta, mul_sub, ← mul_assoc]
    rw [Finset.sum_sub_distrib]
    change pairMass e N (a+2) (c-2)-pairMass e N a c=0
    rw [hmass,sub_self]
  have hcross : ∀ i ∈ Finset.range (N+1), ∀ j ∈ Finset.range (N+1),
      0<d i → d j<0 → row b (2*j+e) ≤ row b (2*i+e) := by
    intro i hi j hj hdi hdj
    have hdi' : 0<delta a c (2*i+e) :=
      (mul_pos_iff_of_pos_left (latticeMultiplicity_pos e i)).mp hdi
    have hdj' : delta a c (2*j+e)<0 := by
      apply (mul_lt_mul_iff_right₀ (latticeMultiplicity_pos e j)).mp
      simpa only [mul_zero] using hdj
    have hlt := delta_single_crossing hc ha hp hdi' hdj'
    exact row_antitone_same_parity hlt.le (by omega) (by omega)
  have h := single_crossing_weighted_sum_nonneg (Finset.range (N+1)) d
    (fun i => row b (2*i+e)) hzero hcross
  have hid : (∑ i ∈ Finset.range (N+1), row b (2*i+e)*d i) =
      centeredSum e N (a+2) b (c-2)-centeredSum e N a b c := by
    unfold centeredSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [d,delta]
    ring
  rw [hid] at h
  exact sub_nonneg.mp h

private lemma first_transfer : ∀ a b c : ℕ, Admissible a b c → 3 ≤ c →
    F a b c ≤ F (a+2) b (c-2) := by
  intro a b c had hc
  rcases had with ⟨hba,hcb,hcpos,hab,hbc⟩
  let e := c%2
  let N := a+b+c
  have he : e ≤ 1 := by exact Nat.le_of_lt_succ (Nat.mod_lt c (by decide : 0<2))
  have hcp : c%2=e := rfl
  have hp : a%2=c%2 := hab.trans hbc
  have hN : c/2 ≤ N := by exact (Nat.div_le_self c 2).trans (Nat.le_add_left c (a+b))
  have had' : Admissible (a+2) b (c-2) :=
    ⟨by omega,by omega,by omega,by omega,by omega⟩
  have h := centered_transfer (e:=e) (N:=N) (a:=a) (b:=b) (c:=c) he hc (hcb.trans hba) hp hcp
    (by dsimp [e]; omega) hN
  have hfold := F_eq_centered_sum ⟨hba,hcb,hcpos,hab,hbc⟩ he hcp hN
  have hfnew := F_eq_centered_sum had' he (by dsimp [e]; omega)
    (by dsimp [N]; omega : (c-2)/2 ≤ N)
  rw [← hfold,← hfnew] at h
  exact_mod_cast h

private lemma second_transfer : ∀ a b c : ℕ, Admissible a b c → 3 ≤ b → c ≤ b-2 →
    F a b c ≤ F (a+2) (b-2) c := by
  intro a b c had hb hcb'
  rcases had with ⟨hba,hcb,hcpos,hab,hbc⟩
  let e := c%2
  let N := a+b+c
  have he : e ≤ 1 := by exact Nat.le_of_lt_succ (Nat.mod_lt c (by decide : 0<2))
  have hbp : b%2=e := by exact hbc
  have hN : b/2 ≤ N := by
    exact (Nat.div_le_self b 2).trans ((Nat.le_add_left b a).trans (Nat.le_add_right (a+b) c))
  have had' : Admissible (a+2) (b-2) c :=
    ⟨by omega,hcb',hcpos,by omega,by omega⟩
  have h := centered_transfer (e:=e) (N:=N) (a:=a) (b:=c) (c:=b) he hb hba hab hbp (show c%2=e from rfl) hN
  rw [centered_sum_swap e N a c b, centered_sum_swap e N (a+2) c (b-2)] at h
  have hfold := F_eq_centered_sum ⟨hba,hcb,hcpos,hab,hbc⟩ he rfl
    (by dsimp [N]; omega : c/2 ≤ N)
  have hfnew := F_eq_centered_sum had' he rfl (by dsimp [N]; omega : c/2 ≤ N)
  rw [← hfold,← hfnew] at h
  exact_mod_cast h

theorem result : claim :=
  result_of_transfers first_transfer second_transfer


end D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture
