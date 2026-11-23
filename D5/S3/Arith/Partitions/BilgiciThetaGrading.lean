/- GID: D5/S3/Arith/Partitions/BilgiciThetaGrading
   generality: I
   mirror-B: D5/B/S3/Arith/Partitions/BilgiciThetaGrading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Character projection and grading in the theta quotient. -/

import D5.S3.Arith.Partitions.BilgiciThetaQuartic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.Field.ZMod

/-! Character projection and grading in the theta quotient. -/

open D5.S3.Arith.Partitions.BilgiciThetaQuartic MvPolynomial
open scoped BigOperators

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural

abbrev K := ZMod 19
instance : Fact (Nat.Prime 19) := ⟨by decide⟩
abbrev R := MvPolynomial (Fin 9) K
abbrev A := R ⧸ ITheta
abbrev Word := List (Fin 9)
abbrev Sparse := List (Word × K)
noncomputable abbrev q : R →ₐ[K] A := Ideal.Quotient.mkₐ K ITheta

noncomputable def P : R →ₗ[K] R :=
  (17 : K) • ∑ j ∈ Finset.range 9, (5 : K)^j • (Tpow j).toLinearMap

private def spProject (digits : List ℤ) : Sparse :=
  sparseSum (List.range 9) fun j =>
    scale ((17 : K) * (5 : K)^j) (orbitWordSparse j digits)

private theorem P_apply (f : R) : P f = (17 : K) • ∑ j ∈ Finset.range 9, (5 : K)^j • Tpow j f := by
  simp [P, LinearMap.sum_apply]

theorem spProject_denote (digits : List ℤ) :
    denote (spProject digits) = P (monomialWord digits) := by
  rw [P_apply, Finset.smul_sum]
  simp only [spProject, denote_sparseSum, denote_scale,
    denote_orbitWordSparse, ← MvPolynomial.smul_eq_C_mul, smul_smul]
  let F : ℕ → R := fun j => ((17 : K) * 5^j) • Tpow j (monomialWord digits)
  change (List.map F (List.range 9)).sum = ∑ j ∈ Finset.range 9, F j
  rw [← List.sum_toFinset F (List.nodup_range (n := 9)),
    List.toFinset, Multiset.coe_range, Multiset.toFinset_range]

theorem mon_index (m : Word) :
    monomialWord (m.map index) = term (m, 1) := by
  induction m with
  | nil => change (1 : R) = monomial 0 1; simp
  | cons i m ih =>
    have hh := term_timesTerm ([i], 1) (m, 1)
    rw [term_singleton, map_one, one_mul] at hh
    have htimes : timesTerm ([i], 1) (m, 1) =
        (sortWord (i :: m), 1) := by
      change (sortWord (i :: m), (1 : K) * 1) = _
      rw [one_mul]
    rw [htimes] at hh
    have hs : term (sortWord (i :: m), 1) =
        term (i :: m, 1) := by
      change monomial (exponent (sortWord (i :: m))) (1 : K) =
        monomial (exponent (i :: m)) (1 : K)
      rw [exponent_sort]
    rw [hs] at hh
    change Z (index i) * monomialWord (m.map index) = _
    rw [Z_base, ih, hh]

theorem T_Tp (j : ℕ) (f : R) : T (Tpow j f) = Tpow (j+1) f := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih => exact ih (T f)

private theorem T9 (f : R) : Tpow 9 f = f := by
  suffices h : Tpow 9 = AlgHom.id K R from AlgHom.congr_fun h f
  apply MvPolynomial.algHom_ext
  intro i
  change Tpow 9 (X i) = X i
  have hs : monomialWord [index i] = X i := by
    change Z (index i) * 1 = X i
    rw [mul_one, Z_base]
  simp only [← hs]
  rw [← denote_orbitWordSparse 9]
  have htable : orbitWordSparse 9 [index i] =
      orbitWordSparse 0 [index i] := by
    fin_cases i <;> decide
  rw [htable, denote_orbitWordSparse]
  rfl

theorem T_P (f : R) : T (P f) = (4 : K) • P f := by
  let F : ℕ → R := fun j => (5 : K)^j • Tpow j f
  have hshift (j : ℕ) : (5 : K)^j • Tpow (j+1) f = (4 : K) • F (j+1) := by
    rw [show (4 : K) • F (j+1) = ((4 : K) * 5^(j+1)) • Tpow (j+1) f from smul_smul ..,
      pow_succ', ← mul_assoc, show (4 : K) * 5 = 1 by decide, one_mul]
  have hlast : F 9 = F 0 := by
    have hz : Tpow 0 f = f := rfl
    simp [F, T9, hz, show (5 : K)^9 = 1 by decide]
  have hsum : (∑ j ∈ Finset.range 9, F (j+1)) = ∑ j ∈ Finset.range 9, F j := by
    calc
      ∑ j ∈ Finset.range 9, F (j+1) =
          (∑ j ∈ Finset.range 8, F (j+1)) + F 9 := Finset.sum_range_succ _ _
      _ = (∑ j ∈ Finset.range 8, F (j+1)) + F 0 := by rw [hlast]
      _ = ∑ j ∈ Finset.range 9, F j := (Finset.sum_range_succ' _ _).symm
  calc
    T (P f) = (17 : K) • ∑ j ∈ Finset.range 9, (5 : K)^j • Tpow (j+1) f := by
      rw [P_apply, map_smul, map_sum]
      simp only [map_smul, T_Tp]
    _ = (17 : K) • ∑ j ∈ Finset.range 9, (4 : K) • F (j+1) := by simp_rw [hshift]
    _ = (4 : K) • P f := by
      rw [← Finset.smul_sum, hsum, smul_comm (17 : K) (4 : K), P_apply]

private theorem Tp_mem (j : ℕ) {f : R} (hf : f ∈ ITheta) : Tpow j f ∈ ITheta := by
  have h : ITheta ≤ Ideal.comap (Tpow j).toRingHom ITheta := by
    apply Ideal.span_le.mpr
    rintro _ ⟨x, rfl⟩
    change Tpow j (theta x) ∈ ITheta
    rw [Tpow_theta]
    exact Ideal.subset_span ⟨_, rfl⟩
  exact h hf

private theorem P_mem {f : R} (hf : f ∈ ITheta) : P f ∈ ITheta := by
  rw [P_apply, MvPolynomial.smul_eq_C_mul]
  apply Ideal.mul_mem_left
  apply Submodule.sum_mem _
  intro j _
  rw [MvPolynomial.smul_eq_C_mul]
  exact Ideal.mul_mem_left _ _ (Tp_mem j hf)

end D5.S3.Arith.Partitions.BilgiciThetaStructural

open D5.S3.Arith.Partitions.BilgiciThetaQuartic MvPolynomial
open scoped BigOperators

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural

private def centeredWeight (i : Fin 9) : K := ((i.val + 1 : ℕ) : K)^2

def centered (m : Word) : K := (m.map centeredWeight).sum

noncomputable def word (m : Word) : R := (m.map X).prod

private theorem word_index (m : Word) : word m = monomialWord (m.map index) := by
  unfold word
  change (m.map X).prod = ((m.map index).map Z).prod
  simp only [List.map_map, Function.comp_def, Z_base]

private theorem word_term (m : Word) : word m = term (m, 1) :=
  (word_index m).trans (mon_index m)

private theorem exponent_multiset (m : Word) : exponent m = (m : Multiset (Fin 9)).toFinsupp := by
  induction m with
  | nil => rfl
  | cons i m ih =>
    change Finsupp.single i 1 + exponent m = _
    rw [ih]
    have hh : (↑(i :: m) : Multiset (Fin 9)) = {i} + (m : Multiset (Fin 9)) := by simp
    rw [hh, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

private theorem exists_word (e : Fin 9 →₀ ℕ) :
    ∃ m : Word, m.Pairwise (· ≤ ·) ∧ exponent m = e := by
  obtain ⟨l, hl⟩ := Quot.exists_rep e.toMultiset
  refine ⟨l.insertionSort (· ≤ ·), List.pairwise_insertionSort _ _, ?_⟩
  rw [exponent_perm (List.perm_insertionSort (· ≤ ·) l), exponent_multiset]
  change Multiset.toFinsupp (Quot.mk _ l) = e
  rw [hl, Finsupp.toMultiset_toFinsupp]

private theorem word_monomial (m : Word) (c : K) :
    monomial (exponent m) c = c • word m := by
  rw [word_term, show term (m, 1) = monomial (exponent m) (1 : K) from rfl]
  simp [MvPolynomial.smul_monomial]

private theorem centered_index (i : Fin 9) : centeredWeight i = 2 * w i - 14 := by
  fin_cases i <;> decide

private theorem centered_weight (m : Word) :
    centered m = 2 * wordWeight m - 14 * (m.length : K) := by
  induction m with
  | nil => decide
  | cons i m ih =>
    change centeredWeight i + centered m =
      2 * (w i + wordWeight m) - 14 * ((m.length + 1 : ℕ) : K)
    rw [centered_index, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem centered_zero_iff (m : Word) (d : ℕ) (n : K)
    (hlen : m.length = d) (hn : 2*n = 14*(d : K)) :
    centered m = 0 ↔ wordWeight m = n := by
  rw [centered_weight, hlen, ← hn, sub_eq_zero]
  exact ⟨mul_left_cancel₀ (show (2 : K) ≠ 0 by decide), fun h => congrArg ((2 : K) * ·) h⟩

private def rotationIndex (i : Fin 9) : Fin 9 :=
  digit (2 * index i)

private def rotationSign (i : Fin 9) : K := sign (index i + 1)

private def rotate (m : Word) : Word := (m.map rotationIndex).insertionSort (· ≤ ·)

private def wordSign (m : Word) : K := (m.map rotationSign).prod

private theorem rotation_X (i : Fin 9) : T (X i) = rotationSign i • X (rotationIndex i) := by
  rw [← Z_base i, T_Z_base, MvPolynomial.smul_eq_C_mul]
  have hbase : Z (2 * index i) = X (rotationIndex i) := by
    have hn : (2 * index i) % 19 ≠ 0 := by fin_cases i <;> decide
    have hs : sign ((2 * index i) / 19) = 1 := by fin_cases i <;> decide
    rw [Z, ite_eq_right hn, hs, map_one, one_mul]
    congr 1
    fin_cases i <;> rfl
  rw [hbase]
  rfl

private theorem rotation_center (i : Fin 9) : centeredWeight (rotationIndex i) = 4 * centeredWeight i := by
  fin_cases i <;> decide

theorem centered_perm {a b : Word} (h : a.Perm b) : centered a = centered b :=
  (h.map centeredWeight).sum_eq

private theorem rotate_length (m : Word) : (rotate m).length = m.length := by
  unfold rotate
  rw [(List.perm_insertionSort (· ≤ ·) (m.map rotationIndex)).length_eq, List.length_map]

private theorem rotate_center (m : Word) : centered (rotate m) = 4 * centered m := by
  unfold rotate
  rw [centered_perm (List.perm_insertionSort (· ≤ ·) (m.map rotationIndex))]
  induction m with
  | nil => simp [centered]
  | cons i m ih =>
    change centeredWeight (rotationIndex i) + centered (m.map rotationIndex) =
      4 * (centeredWeight i + centered m)
    rw [rotation_center, ih, mul_add]

private theorem word_perm {a b : Word} (h : a.Perm b) : word a = word b :=
  (h.map X).prod_eq

private theorem T_word (m : Word) : T (word m) = wordSign m • word (rotate m) := by
  unfold rotate
  rw [word_perm (List.perm_insertionSort (· ≤ ·) (m.map rotationIndex))]
  induction m with
  | nil => change T 1 = (1 : K) • (1 : R); simp
  | cons i m ih =>
    change T (X i * word m) = (rotationSign i * wordSign m) •
      (X (rotationIndex i) * word (m.map rotationIndex))
    rw [map_mul, rotation_X, ih, smul_mul_smul_comm]

theorem P_T (f : R) : P (T f) = (4 : K) • P f := by
  rw [P_apply (T f), ← T_P f, P_apply f, map_smul, map_sum]
  simp only [map_smul, T_Tp]
  rfl

noncomputable def grade (d : ℕ) (n : K) : Submodule K R :=
  homogeneousSubmodule (Fin 9) K d ⊓ weightedHomogeneousSubmodule K w n

theorem grade_mem {d : ℕ} {n : K} {f : R} :
    f ∈ grade d n ↔ f.IsHomogeneous d ∧ f.IsWeightedHomogeneous w n := Iff.rfl

theorem word_grade {d : ℕ} {n : K} {m : Word}
    (hd : m.length = d) (hn : wordWeight m = n) : word m ∈ grade d n := by
  rw [word_term, grade_mem]
  exact ⟨isHomogeneous_monomial 1 ((exponent_degree m).trans hd),
    isWeightedHomogeneous_monomial w _ _ ((exponent_weight m).trans hn)⟩

theorem support_word {d : ℕ} {n : K} {f : R} (hf : f ∈ grade d n) {e : Fin 9 →₀ ℕ}
    (he : e ∈ f.support) :
    ∃ m : Word, m.Pairwise (· ≤ ·) ∧ m.length = d ∧ wordWeight m = n ∧
      monomial e (f.coeff e) = f.coeff e • word m := by
  obtain ⟨m, hsorted, hexp⟩ := exists_word e
  obtain ⟨hd, hn⟩ := grade_mem.mp hf
  refine ⟨m, hsorted, ?_, ?_, ?_⟩
  · rw [← exponent_degree m, hexp, Finsupp.degree_eq_weight_one]
    exact hd (mem_support_iff.mp he)
  · rw [← exponent_weight m, hexp]
    exact hn (mem_support_iff.mp he)
  · rw [← hexp, word_monomial]

private theorem T_grade {d : ℕ} {n : K} (hn : 2*n = 14*(d : K)) {f : R} (hf : f ∈ grade d n) :
    T f ∈ grade d n := by
  rw [← support_sum_monomial_coeff f, map_sum]
  apply Submodule.sum_mem _
  intro e he
  obtain ⟨m, _, hlen, hw, hm⟩ := support_word hf he
  rw [hm, map_smul, T_word]
  apply Submodule.smul_mem _ _
  apply Submodule.smul_mem _ _
  have hz := (centered_zero_iff m d n hlen hn).mpr hw
  have hlen' : (rotate m).length = d := (rotate_length _).trans hlen
  exact word_grade hlen' ((centered_zero_iff _ d n hlen' hn).mp (by rw [rotate_center, hz, mul_zero]))

private theorem Tp_grade {d : ℕ} {n : K} (hn : 2*n = 14*(d : K)) {f : R} (hf : f ∈ grade d n) (j : ℕ) :
    Tpow j f ∈ grade d n := by
  induction j with
  | zero => exact hf
  | succ j ih => rw [← T_Tp]; exact T_grade hn ih

private theorem P_grade {d : ℕ} {n : K} (hn : 2*n = 14*(d : K)) {f : R} (hf : f ∈ grade d n) :
    P f ∈ grade d n := by
  rw [P_apply]
  apply Submodule.smul_mem _ _
  apply Submodule.sum_mem _
  intro j hj
  exact Submodule.smul_mem _ _ (Tp_grade hn hf j)

private noncomputable def Tbar : A →ₐ[K] A :=
  Ideal.Quotient.liftₐ ITheta (q.comp T)
    (fun _ hf => Ideal.Quotient.eq_zero_iff_mem.mpr (Tp_mem 1 hf))

theorem Tbar_q (f : R) : Tbar (q f) = q (T f) := rfl

private theorem P_quotient_fixed (f : R) (h : Tbar (q f) = (4 : K) • q f) : q (P f) = q f := by
  have hpow (j : ℕ) : q (Tpow j f) = ((4 : K)^j) • q f := by
    induction j with
    | zero => change q f = ((4 : K)^0) • q f; simp
    | succ j ih =>
      rw [← T_Tp, ← Tbar_q, ih, map_smul, h, smul_smul, pow_succ]
  rw [P_apply, map_smul, map_sum]
  simp_rw [map_smul, hpow, smul_smul, ← mul_pow, show (5 : K) * 4 = 1 by decide, one_pow, one_smul]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  rw [show (17 : K) * (9 : ℕ) = 1 by decide, one_smul]

noncomputable def eigengrade (d : ℕ) (n : K) : Submodule K A :=
  ((grade d n).map q.toLinearMap) ⊓ LinearMap.ker (Tbar.toLinearMap - (4 : K) • LinearMap.id)

theorem eigengrade_mem {d : ℕ} {n : K} {x : A} :
    x ∈ eigengrade d n ↔ (∃ f ∈ grade d n, q f = x) ∧ Tbar x = (4 : K) • x := by
  simp [eigengrade, sub_eq_zero]

theorem eigengrade_of_projected (m : List ℤ) {d : ℕ} {n : K} (h : P (monomialWord m) ∈ grade d n) :
    q (P (monomialWord m)) ∈ eigengrade d n :=
  eigengrade_mem.mpr ⟨⟨_, h, rfl⟩, by rw [Tbar_q, T_P, map_smul]⟩

theorem eigengrade_exact {d : ℕ} {n : K} (hn : 2*n = 14*(d : K)) :
    eigengrade d n = (grade d n).map (q.toLinearMap.comp P) := by
  ext x
  change (x ∈ eigengrade d n) ↔ (∃ f ∈ grade d n, q (P f) = x)
  rw [eigengrade_mem]
  constructor
  · rintro ⟨⟨f, hf, rfl⟩, he⟩
    exact ⟨f, hf, P_quotient_fixed f he⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨P f, P_grade hn hf, rfl⟩, by rw [Tbar_q, T_P, map_smul]⟩


end D5.S3.Arith.Partitions.BilgiciThetaStructural

open D5.S3.Arith.Partitions.BilgiciThetaQuartic MvPolynomial

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening
open D5.S3.Arith.Partitions.BilgiciThetaStructural

def digit (i : Fin 9) : K := (i.val + 1 : ℕ)

def absIndex (r : K) : Fin 9 :=
  Fin.ofNat 9 (min r.val (19 - r.val) - 1)

def epsilon (r : K) : K := if r = 0 then 0 else if r.val ≤ 9 then 1 else -1

noncomputable def x (r : K) : R :=
  C (sign (r.val : ℤ)) * Z (r.val : ℤ)

theorem x_int (n : ℤ) : x (n : K) = C (sign n) * Z n := by
  rw [x, ZMod.val_intCast, show (n % (19 : ℕ)) = n % 19 by rfl]
  conv_rhs => rw [Z_remainder n]
  rw [← mul_assoc, ← map_mul, ← sign_add]
  have h : sign (n + n / 19) = sign (n % 19) := by
    unfold sign;
    rw [show (n + n / 19) % 2 = (n % 19) % 2 by omega]
  rw [h]

theorem x_odd (r : K) : x (-r) = -x r := by
  rw [← ZMod.natCast_zmod_val r, ← Int.cast_natCast, ← Int.cast_neg, x_int, x_int,
    Z_neg, mul_neg]
  have hs : sign (-(r.val : ℤ)) = sign (r.val : ℤ) := by
    unfold sign;
    rw [show (-(r.val : ℤ)) % 2 = (r.val : ℤ) % 2 by omega]
  rw [hs]

theorem x_zero : x 0 = 0 := by
  rw [← Int.cast_zero, x_int, show Z 0 = 0 from Z_mul19 0, mul_zero]

theorem T_x (r : K) : T (x r) = -x (2 * r) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, (n : K) = r := ⟨r.val, by simp [ZMod.natCast_zmod_val]⟩
  have hC (c : K) : T (C c) = C c := by simp
  have hs : sign (n + (n + 1)) = -sign (2*n) := by
    unfold sign;
    rw [ite_eq_right (show (n+(n+1)) % 2 ≠ 0 by omega),
      ite_eq_left (show (2*n) % 2 = 0 by omega)]
  rw [x_int, map_mul, T_Z, hC, ← mul_assoc, ← map_mul,
    ← sign_add, hs, map_neg, neg_mul, ← show (((2*n : ℤ) : K)) = 2*(n : K) by push_cast; rfl, ← x_int]

private theorem digit_val (i : Fin 9) : (digit i).val = i.val + 1 :=
  ZMod.val_natCast_of_lt (by have := i.isLt; omega)

private theorem absIndex_digit_val (r : K) (hr : r ≠ 0) :
    (digit (absIndex r)).val = min r.val (19 - r.val) := by
  have hv : r.val < 19 := ZMod.val_lt r
  have hp : 0 < r.val := ZMod.val_pos.mpr hr
  have hm : min r.val (19 - r.val) - 1 < 9 := by omega
  rw [digit_val, absIndex, Fin.val_ofNat, Nat.mod_eq_of_lt hm]
  omega

theorem epsilon_abs (r : K) : r = epsilon r * digit (absIndex r) := by
  by_cases hr : r = 0
  · simp [hr, epsilon]
  have hv := absIndex_digit_val r hr
  have hlt : r.val < 19 := ZMod.val_lt r
  by_cases h : r.val ≤ 9
  · rw [epsilon, ite_eq_right hr, ite_eq_left h, one_mul]
    apply ZMod.val_injective
    rw [hv, min_eq_left (by omega)]
  · rw [epsilon, ite_eq_right hr, ite_eq_right h, neg_one_mul, eq_neg_iff_add_eq_zero]
    have hd : -r = digit (absIndex r) := by
      apply ZMod.val_injective
      rw [ZMod.neg_val, ite_eq_right hr, hv, min_eq_right (by omega)]
    rw [← hd, add_neg_cancel]

private theorem epsilon_cases (r : K) : epsilon r = 0 ∨ epsilon r = 1 ∨ epsilon r = -1 := by
  unfold epsilon
  by_cases h : r = 0
  · exact Or.inl (ite_eq_left h)
  · rw [ite_eq_right h]
    split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem x_abs (r : K) : x r = epsilon r • x (digit (absIndex r)) := by
  have h := epsilon_abs r
  rcases epsilon_cases r with he | he | he
  · rw [he, zero_mul] at h
    rw [he, zero_smul, h, x_zero]
  · rw [he, one_mul] at h
    simpa only [he, one_smul] using congrArg x h
  · rw [he, neg_one_mul] at h
    calc
      x r = x (-digit (absIndex r)) := congrArg x h
      _ = _ := by rw [x_odd, he, neg_one_smul]

theorem abs_square (r : K) (hr : r ≠ 0) : digit (absIndex r) ^ 2 = r ^ 2 := by
  have h := epsilon_abs r
  rcases epsilon_cases r with he | he | he
  · rw [he, zero_mul] at h
    exact (hr h).elim
  · rw [he, one_mul] at h
    rw [← h]
  · rw [he, neg_one_mul] at h
    have hs : r ^ 2 = (-digit (absIndex r)) ^ 2 := congrArg (fun z : K => z ^ 2) h
    rw [neg_sq] at hs
    exact hs.symm

theorem digit_nonzero (i : Fin 9) : digit i ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [digit_val, ZMod.val_zero] at hv
  omega

theorem digit_square_injective : Function.Injective (fun i : Fin 9 => digit i ^ 2) := by
  intro i j h
  rcases eq_or_eq_neg_of_sq_eq_sq (digit i) (digit j) h with h' | h'
  · have hv := congrArg ZMod.val h'
    rw [digit_val, digit_val] at hv
    exact Fin.ext (by omega)
  · have hv := congrArg ZMod.val h'
    rw [digit_val, ZMod.neg_val, ite_eq_right (digit_nonzero j), digit_val] at hv
    have hi := i.isLt
    have hj := j.isLt
    omega

theorem x_digit (i : Fin 9) : x (digit i) = sign (index i) • X i := by
  have h : digit i = ((index i : ℤ) : K) := by
    simp [digit]
    unfold index;
    simp
  rw [h, x_int, Z_base, smul_eq_C_mul]

def labels (u v : K) : List K := [u + v, u - v]

noncomputable def raw (m : List K) : R := (m.map x).prod

private theorem raw_append (m n : List K) : raw (m ++ n) = raw m * raw n := by
  simp [raw]

private theorem raw_perm {m n : List K} (h : m.Perm n) : raw m = raw n :=
  (h.map x).prod_eq

noncomputable def F : R →ₗ[K] A := q.toLinearMap.comp P

noncomputable def evalRaw (m : List K) : A := F (raw m)

noncomputable def evalWord (m : Word) : A := evalRaw (m.map digit)

theorem evalWord_perm {m n : Word} (h : m.Perm n) : evalWord m = evalWord n :=
  congrArg F (raw_perm (h.map digit))

theorem source_word_sign (m : Word) :
    raw (m.map digit) = (m.map (fun i => sign (index i))).prod • word m := by
  induction m with
  | nil => simp [raw, word]
  | cons i m ih =>
    change x (digit i) * raw (m.map digit) =
      (sign (index i) *
      (m.map (fun j => sign (index j))).prod) • (X i * word m)
    rw [x_digit, ih, smul_mul_smul_comm]

theorem evalWord_source (m : Word) :
    evalWord m = (m.map (fun i => sign (index i))).prod • q (P (word m)) := by
  unfold evalWord evalRaw
  rw [source_word_sign, map_smul]
  rfl

theorem source_evalWord (m : Word) :
    q (P (word m)) = (m.map (fun i => sign (index i))).prod • evalWord m := by
  rw [evalWord_source, smul_smul]
  have h (i : Fin 9) :
      sign (index i) * sign (index i) = 1 := by
    decide +revert
  have hh :
      (m.map (fun i => sign (index i))).prod *
      (m.map (fun i => sign (index i))).prod = 1 := by
    induction m with
    | nil => simp
    | cons i m ih => simp only [List.map_cons, List.prod_cons, mul_mul_mul_comm _ _ (sign (index i)) _, h, ih, one_mul]
  rw [hh, one_smul]

def coeff (m : List K) : K := (m.map epsilon).prod

def absWord (m : List K) : Word := m.map absIndex

theorem raw_abs (m : List K) : raw m = coeff m • raw ((absWord m).map digit) := by
  induction m with
  | nil => simp [raw, coeff, absWord]
  | cons a m ih =>
    change x a * raw m = (epsilon a * coeff m) •
      (x (digit (absIndex a)) * raw ((absWord m).map digit))
    rw [x_abs, ih, smul_mul_smul_comm]

theorem evalRaw_abs (m : List K) : evalRaw m = coeff m • evalWord (absWord m) := by
  unfold evalRaw evalWord
  rw [raw_abs m, map_smul]
  rfl

theorem coeff_nonzero_entries (m : List K) (h : coeff m ≠ 0) : ∀ a ∈ m, a ≠ 0 := by
  intro a ha he
  subst a
  apply h
  apply List.prod_eq_zero
  exact List.mem_map.mpr ⟨0, ha, by decide⟩

theorem raw_pair_int (u v : ℤ) :
    raw (labels u v) = Z (u + v) * Z (u - v) := by
  change x ((u : K) + (v : K)) * (x ((u : K) - (v : K)) * 1) = _
  rw [mul_one, ← Int.cast_add, ← Int.cast_sub, x_int, x_int,
    mul_mul_mul_comm, ← map_mul, ← sign_add]
  have hs : sign ((u + v) + (u - v)) = 1 := by
    unfold sign;
    rw [ite_eq_left (by omega)]
  rw [hs, map_one, one_mul]

def pairing (u v s t : K) : List K := labels u v ++ labels s t

def row (u v s t : K) (n : Word) : List K :=
  pairing u v s t ++ n.map digit

private theorem theta_raw (u v s t : K) :
    raw (pairing u t v s) - raw (pairing u s v t) + raw (pairing u v s t) =
      theta (u.val, v.val, s.val, t.val) := by
  have hl (a b : K) : raw (labels a b) = Z ((a.val : ℤ) + b.val) * Z ((a.val : ℤ) - b.val) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using raw_pair_int (a.val : ℤ) (b.val : ℤ)
  simp only [pairing, raw_append, hl, theta]

theorem theta_annihilated (u v s t : K) (n : Word) :
    evalRaw (row u t v s n) - evalRaw (row u s v t n) + evalRaw (row u v s t n) = 0 := by
  have h : theta (u.val, v.val, s.val, t.val) * raw (n.map digit) ∈ ITheta :=
    Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, rfl⟩)
  have hz : F (theta (u.val, v.val, s.val, t.val) * raw (n.map digit)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (P_mem h)
  rw [← theta_raw, add_mul, sub_mul, map_add, map_sub] at hz
  simpa only [evalRaw, row, raw_append] using hz


end D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening
