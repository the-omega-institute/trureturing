/- GID: D5/S3/Arith/Partitions/BilgiciThetaStraighteningRank
   generality: I
   mirror-B: D5/B/S3/Arith/Partitions/BilgiciThetaStraighteningRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Re-pairing and a well-founded rank for centered words. -/

import D5.S3.Arith.Partitions.BilgiciThetaGrading

/-! Re-pairing and a well-founded rank for centered words. -/

open D5.S3.Arith.Partitions.BilgiciThetaQuartic MvPolynomial
open scoped BigOperators
open D5.S3.Arith.Partitions.BilgiciThetaQuartic (T Tpow)

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening
open D5.S3.Arith.Partitions.BilgiciThetaStructural

def scaleIndex (k : K) (i : Fin 9) : Fin 9 := absIndex (k * digit i)

def scaleWord (k : K) (m : Word) : Word := m.map (scaleIndex k)

theorem scaleIndex_one (k : K) (i : Fin 9) (h : k * digit i = 1) :
    scaleIndex k i = 0 := by
  rw [scaleIndex, h]
  decide

private theorem scaleIndex_neg (k : K) (i : Fin 9) : scaleIndex (-k) i = scaleIndex k i := by
  decide +revert

theorem scaleIndex_injective {k : K} (hk : k ≠ 0) :
    Function.Injective (scaleIndex k) := by
  intro i j h
  apply digit_square_injective
  have hn (i : Fin 9) : k * digit i ≠ 0 := mul_ne_zero hk (digit_nonzero i)
  have h' := congrArg (fun i => digit i ^ 2) h
  dsimp only [scaleIndex] at h'
  rw [abs_square _ (hn _), abs_square _ (hn _), mul_pow, mul_pow] at h'
  exact mul_left_cancel₀ (pow_ne_zero _ hk) h'

theorem scale_center (k : K) (hk : k ≠ 0) (m : Word) :
    centered (scaleWord k m) = k ^ 2 * centered m := by
  induction m with
  | nil => simp [scaleWord, centered]
  | cons i m ih =>
    change digit (absIndex (k * digit i)) ^ 2 + centered (scaleWord k m) =
      k ^ 2 * (digit i ^ 2 + centered m)
    rw [abs_square _ (mul_ne_zero hk (digit_nonzero i)), mul_pow, ih, mul_add]

theorem T_raw (m : List K) :
    T (raw m) = (-1 : K) ^ m.length • raw (m.map (fun r => 2 * r)) := by
  induction m with
  | nil => simp [raw]
  | cons a m ih =>
    change T (x a * raw m) = (-1 : K) ^ (m.length + 1) •
      (x (2 * a) * raw (m.map (fun r => 2 * r)))
    rw [map_mul, T_x, ih, ← neg_one_smul K (x (2 * a)), smul_mul_smul_comm, pow_succ']

private theorem Tp_raw (j : ℕ) (m : List K) :
    Tpow j (raw m) = ((-1 : K) ^ j) ^ m.length • raw (m.map (fun r => 2 ^ j * r)) := by
  induction j with
  | zero =>
    have h : Tpow 0 (raw m) = raw m := rfl
    rw [h]
    simp
  | succ j ih =>
    rw [← T_Tp, ih, map_smul, T_raw, List.length_map, smul_smul, ← mul_pow, ← pow_succ]
    simp only [List.map_map, Function.comp_def, pow_succ', mul_assoc]

private theorem P_Tp (j : ℕ) (f : R) : P (Tpow j f) = (4 : K)^j • P f := by
  induction j with
  | zero =>
    change P f = (4 : K)^0 • P f
    simp
  | succ j ih =>
    rw [← T_Tp, P_T, ih, smul_smul, pow_succ']

private theorem F_Tp (j : ℕ) (f : R) : F (Tpow j f) = (4 : K)^j • F f := by
  change q (P (Tpow j f)) = (4 : K)^j • q (P f)
  rw [P_Tp, map_smul]

def scaleCoeff (j : ℕ) (m : Word) : K :=
  (5 : K)^j * ((-1 : K)^j)^m.length * coeff (m.map (fun i => 2^j * digit i))

set_option maxHeartbeats 2000000 in
theorem evalWord_power (j : ℕ) (m : Word) :
    evalWord m = scaleCoeff j m • evalWord (scaleWord (2^j) m) := by
  let lifted := m.map (fun i => 2^j * digit i)
  have hMap : ((m.map digit).map (fun r => (2 : K)^j * r)) = lifted := by
    simp only [lifted, List.map_map, Function.comp_def]
  have hAbs : absWord lifted = scaleWord (2^j) m := by
    simp only [lifted, absWord, scaleWord, List.map_map, Function.comp_def]
    rfl
  have h : ((-1 : K)^j)^m.length • evalRaw lifted =
      (4 : K)^j • evalWord m := by
    have hF := F_Tp j (raw (m.map digit))
    rw [Tp_raw, map_smul, List.length_map, hMap] at hF
    exact hF
  rw [evalRaw_abs, hAbs, smul_smul] at h
  have he : (5 : K)^j * 4^j = 1 := by
    rw [← mul_pow, show (5 : K) * 4 = 1 by decide, one_pow]
  calc
    evalWord m = (5 : K)^j • ((4 : K)^j • evalWord m) := by rw [smul_smul, he, one_smul]
    _ = (5 : K)^j • (((-1 : K)^j)^m.length * coeff lifted) • evalWord (scaleWord (2^j) m) :=
      congrArg ((5 : K)^j • ·) h.symm
    _ = _ := by rw [smul_smul, ← mul_assoc]; rfl

private theorem exists_power_or_neg (k : K) (hk : k ≠ 0) :
    ∃ j : Fin 9, k = 2^j.val ∨ k = -(2^j.val) := by
  decide +revert

set_option maxHeartbeats 2000000 in
theorem evalWord_scale (k : K) (hk : k ≠ 0) (m : Word) :
    ∃ c : K, evalWord m = c • evalWord (scaleWord k m) := by
  obtain ⟨j, hj | hj⟩ := exists_power_or_neg k hk
  · exact ⟨scaleCoeff j.val m, by simpa only [hj] using evalWord_power j.val m⟩
  · have hm : scaleWord k m = scaleWord (2^j.val) m := by
      rw [hj]
      exact List.map_congr_left (fun i _ => scaleIndex_neg (2^j.val) i)
    exact ⟨scaleCoeff j.val m, by rw [hm]; exact evalWord_power j.val m⟩

private def squareSum (m : List K) : K := (m.map (fun r => r^2)).sum

private theorem centered_abs (m : List K) (hn : coeff m ≠ 0) :
    centered (absWord m) = squareSum m := by
  induction m with
  | nil => rfl
  | cons a m ih =>
    change epsilon a * coeff m ≠ 0 at hn
    change digit (absIndex a)^2 + centered (absWord m) = a^2 + squareSum m
    rw [abs_square _ (coeff_nonzero_entries (a :: m) hn a (by simp))]
    rw [ih (right_ne_zero_of_mul hn)]

private theorem squareSum_row (u v s t : K) (n : Word) :
    squareSum (row u v s t n) =
      2 * (u^2 + v^2 + s^2 + t^2) + centered n := by
  simp only [squareSum, row, pairing, labels, List.cons_append, List.nil_append, List.map_cons,
    List.sum_cons, List.map_map, Function.comp_def]
  change (u+v)^2 + ((u-v)^2 + ((s+t)^2 + ((s-t)^2 + centered n))) = _
  ring

private def half (r : K) : K := 10 * r

private def rePairLeft (a b c d : Fin 9) (n : Word) : List K :=
  row (half (digit a + digit b)) (half (digit c + digit d))
    (half (digit a - digit b)) (half (digit c - digit d)) n

private def rePairRight (a b c d : Fin 9) (n : Word) : List K :=
  row (half (digit a + digit b)) (half (digit c - digit d))
    (half (digit a - digit b)) (half (digit c + digit d)) n

private theorem row_pivot (a b c d : Fin 9) (n : Word) :
    row (half (digit a + digit b)) (half (digit a - digit b))
      (half (digit c + digit d)) (half (digit c - digit d)) n =
      (a :: b :: c :: d :: n).map digit := by
  simp only [row, pairing, labels, List.cons_append, List.nil_append, List.map_cons]
  have hs (r s : K) : half (r+s) + half (r-s) = r := by
    unfold half
    calc
      _ = (10 + 10 : K) * r := by ring
      _ = r := by rw [show (10 + 10 : K) = 1 by decide, one_mul]
  have hd (r s : K) : half (r+s) - half (r-s) = s := by
    unfold half
    calc
      _ = (10 + 10 : K) * s := by ring
      _ = s := by rw [show (10 + 10 : K) = 1 by decide, one_mul]
  rw [hs, hd, hs, hd]

theorem rePair_identity (a b c d : Fin 9) (n : Word) :
    evalWord (a :: b :: c :: d :: n) =
    evalRaw (rePairLeft a b c d n) - evalRaw (rePairRight a b c d n) := by
  have h := theta_annihilated (half (digit a + digit b)) (half (digit a - digit b))
    (half (digit c + digit d)) (half (digit c - digit d)) n
  rw [row_pivot] at h
  change evalRaw (rePairRight a b c d n) - evalRaw (rePairLeft a b c d n) +
    evalWord (a :: b :: c :: d :: n) = 0 at h
  exact (eq_neg_of_add_eq_zero_right h).trans (neg_sub ..)

theorem rePair_center (a b c d : Fin 9) (n : Word) :
    squareSum (rePairLeft a b c d n) = centered (a :: b :: c :: d :: n) ∧
    squareSum (rePairRight a b c d n) = centered (a :: b :: c :: d :: n) := by
  have h := congrArg squareSum (row_pivot a b c d n)
  have hmap (m : Word) : squareSum (m.map digit) = centered m := by
    simp only [squareSum, List.map_map, Function.comp_def, centered]
    rfl
  rw [hmap] at h
  rw [squareSum_row] at h
  constructor
  · rw [rePairLeft, squareSum_row, ← h]
    ring
  · rw [rePairRight, squareSum_row, ← h]
    ring


end D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening

open scoped BigOperators

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening
open D5.S3.Arith.Partitions.BilgiciThetaStructural

private theorem scaleIndex_comp (k l : K) (i : Fin 9) (hk : k ≠ 0) (hl : l ≠ 0) :
    scaleIndex k (scaleIndex l i) = scaleIndex (k*l) i := by
  apply digit_square_injective
  simp only [scaleIndex]
  rw [abs_square _ (mul_ne_zero hk (digit_nonzero _)),
    abs_square _ (mul_ne_zero (mul_ne_zero hk hl) (digit_nonzero _)),
    mul_pow, abs_square _ (mul_ne_zero hl (digit_nonzero _))]
  simp only [mul_pow, mul_assoc]

private theorem scaleWord_comp (k l : K) (m : Word) (hk : k ≠ 0) (hl : l ≠ 0) :
    scaleWord k (scaleWord l m) = scaleWord (k*l) m := by
  simp only [scaleWord, List.map_map, Function.comp_def]
  exact List.map_congr_left (fun i _ => scaleIndex_comp k l i hk hl)

private def energy (m : Word) : ℕ := ∑ i : Fin 9, 10 ^ m.count i

private theorem energy_perm {m n : Word} (h : m.Perm n) : energy m = energy n := by
  unfold energy
  simp only [h.count_eq]

private theorem energy_scale (k : K) (m : Word) (hk : k ≠ 0) :
    energy (scaleWord k m) = energy m := by
  have hinj := scaleIndex_injective hk
  have hbij := Finite.injective_iff_bijective.mp hinj
  unfold energy
  rw [← hbij.sum_comp (fun i => 10 ^ (scaleWord k m).count i)]
  simp only [scaleWord, List.count_map_of_injective m _ hinj]

def doubled (m : Word) : Word := (List.finRange 9).filter (fun i => m.count i == 2)

private def omittedSquares (m : Word) : List ℕ :=
  (((List.finRange 9).filter (fun i => !(m.contains i))).map
    (fun i => (digit i ^ 2).val)).insertionSort (· ≤ ·)

private def normalizedResidue (m : Word) : ℕ :=
  match doubled m with
  | [0] =>
    let missing := omittedSquares m
    (57 - missing.sum) * 6859 + missing.foldl (fun n r => 19*n+r) 0
  | [0,b] => (digit b ^ 2).val
  | _ => 500000

private def residueAt (m : Word) (k : K) : ℕ :=
  if k = 0 then 500000 else normalizedResidue (scaleWord k m)

private def residueRank (m : Word) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (residueAt m)

private theorem normalizedResidue_perm {m n : Word} (h : m.Perm n) :
    normalizedResidue m = normalizedResidue n := by
  have hb : ∀ i, (m.contains i) = (n.contains i) := by
    intro i
    simp only [List.contains_eq_mem, h.mem_iff]
  simp only [normalizedResidue, doubled, omittedSquares, h.count_eq, hb]

private theorem residueRank_perm {m n : Word} (h : m.Perm n) :
    residueRank m = residueRank n := by
  have he : residueAt m = residueAt n := by
    funext k
    have he := normalizedResidue_perm (show (scaleWord k m).Perm (scaleWord k n) from
      h.map (scaleIndex k))
    simp only [residueAt, he]
  simp only [residueRank, he]

private theorem residueRank_scale (l : K) (m : Word) (hl : l ≠ 0) :
    residueRank (scaleWord l m) = residueRank m := by
  have hc (k : K) : residueAt (scaleWord l m) k = residueAt m (k*l) := by
    by_cases hk : k = 0
    · simp [hk, residueAt]
    · simp only [residueAt, hk, mul_ne_zero hk hl, ite_false, scaleWord_comp k l m hk hl]
  apply le_antisymm
  · unfold residueRank
    rw [Finset.le_inf'_iff]
    intro k _
    have h := Finset.inf'_le (s := Finset.univ) (residueAt (scaleWord l m))
      (Finset.mem_univ (k*l⁻¹))
    rw [hc, inv_mul_cancel_right₀ hl] at h
    exact h
  · unfold residueRank
    rw [Finset.le_inf'_iff]
    intro k _
    rw [hc]
    exact Finset.inf'_le (residueAt m) (Finset.mem_univ (k*l))

def rank (m : Word) : ℕ × ℕ := (energy m, residueRank m)

def precedes (m n : Word) : Prop :=
  energy m < energy n ∨ energy m = energy n ∧ residueRank m < residueRank n

instance (m n : Word) : Decidable (precedes m n) := by
  unfold precedes
  infer_instance

theorem precedes_wf : WellFounded precedes := by
  apply (InvImage.wf rank (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf).mono
  intro a b h
  exact Prod.lex_def.mpr h

private theorem precedes_perm_right {m n p : Word} (h : n.Perm p) :
    precedes m n ↔ precedes m p := by
  simp only [precedes, energy_perm h, residueRank_perm h]

private theorem precedes_scale_right (l : K) (m n : Word) (hl : l ≠ 0) :
    precedes m (scaleWord l n) ↔ precedes m n := by
  simp only [precedes, energy_scale _ _ hl, residueRank_scale _ _ hl]

private def goodTerm (pivot : Word) (term : List K) : Prop :=
  coeff term = 0 ∨ energy (absWord term) < energy pivot

instance (m : Word) (term : List K) : Decidable (goodTerm m term) := by
  unfold goodTerm
  infer_instance

def goodMove (a b c d : Fin 9) (n : Word) : Prop :=
  goodTerm (a :: b :: c :: d :: n) (rePairLeft a b c d n) ∧
  goodTerm (a :: b :: c :: d :: n) (rePairRight a b c d n)

instance (a b c d : Fin 9) (n : Word) : Decidable (goodMove a b c d n) := by
  unfold goodMove
  infer_instance

def smaller (M : Submodule K A) (m : Word) : Prop :=
  ∀ n, precedes n m → n.length = 7 → centered n = 0 → evalWord n ∈ M

theorem smaller_perm {M : Submodule K A} {m n : Word} (h : m.Perm n)
    (hh : smaller M m) : smaller M n :=
  fun p hp => hh p ((precedes_perm_right h).mpr hp)

theorem smaller_scale {M : Submodule K A} {m : Word} (k : K) (hk : k ≠ 0)
    (hh : smaller M m) : smaller M (scaleWord k m) :=
  fun p hp => hh p ((precedes_scale_right k _ _ hk).mp hp)

private theorem goodTerm_mem {M : Submodule K A} {m : Word} {r : List K}
    (h : goodTerm m r) (hs : smaller M m) (hl : r.length = 7)
    (hz : squareSum r = 0) : evalRaw r ∈ M := by
  rw [evalRaw_abs]
  rcases h with hc | he
  · rw [hc, zero_smul]
    exact M.zero_mem
  · by_cases hc : coeff r = 0
    · rw [hc, zero_smul]
      exact M.zero_mem
    · apply M.smul_mem
      apply hs _ (Or.inl he)
      · simpa only [absWord, List.length_map] using hl
      · rw [centered_abs _ hc, hz]

private theorem goodMove_mem {M : Submodule K A} {a b c d : Fin 9} {n : Word}
    (hg : goodMove a b c d n) (hs : smaller M (a :: b :: c :: d :: n))
    (hl : n.length = 3) (hz : centered (a :: b :: c :: d :: n) = 0) :
    evalWord (a :: b :: c :: d :: n) ∈ M := by
  rw [rePair_identity]
  apply M.sub_mem
  · exact goodTerm_mem hg.1 hs (by simp [rePairLeft, row, pairing, labels, hl])
      ((rePair_center a b c d n).1.trans hz)
  · exact goodTerm_mem hg.2 hs (by simp [rePairRight, row, pairing, labels, hl])
      ((rePair_center a b c d n).2.trans hz)

theorem goodMove_from_perm {M : Submodule K A} {m : Word} {a b c d : Fin 9} {n : Word}
    (hp : m.Perm (a :: b :: c :: d :: n)) (hg : goodMove a b c d n)
    (hs : smaller M m) (hl : m.length = 7) (hz : centered m = 0) : evalWord m ∈ M := by
  rw [evalWord_perm hp]
  apply goodMove_mem hg (smaller_perm hp hs)
  · have hl' := hp.length_eq
    simp only [List.length_cons] at hl'
    omega
  · rw [← centered_perm hp, hz]


end D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening
open D5.S3.Arith.Partitions.BilgiciThetaStructural

private def expand (f : Fin 9 → ℕ) (l : Word) : Word :=
  l.flatMap fun i => List.replicate (f i) i

private theorem count_expand (f : Fin 9 → ℕ) (l : Word) (hl : l.Nodup) (a : Fin 9) :
    (expand f l).count a = if a ∈ l then f a else 0 := by
  induction l with
  | nil => simp [expand]
  | cons i l ih =>
    have hn := List.nodup_cons.mp hl
    simp only [expand, List.flatMap_cons, List.count_append]
    change (List.replicate (f i) i).count a + (expand f l).count a = _
    rw [ih hn.2, List.count_replicate]
    by_cases h : a = i
    · subst a
      simp [hn.1]
    · simp [h, Ne.symm h]

private theorem length_expand (f : Fin 9 → ℕ) (l : Word) :
    (expand f l).length = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [expand, List.flatMap_cons, List.length_append, List.length_replicate,
      List.map_cons, List.sum_cons]
    exact congrArg (f i + ·) ih

private def unpack (cs : List ℕ) (ls : Word) : Word :=
  (List.zipWith List.replicate cs ls).flatten

private theorem expand_unpack (f : Fin 9 → ℕ) (l : Word) :
    expand f l = unpack (l.map f) l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change List.replicate (f i) i ++ expand f l = List.replicate (f i) i ++ unpack (l.map f) l
    rw [ih]

private def groupedLabels (m : Word) : Word :=
  m.dedup.insertionSort (fun i j => m.count j ≤ m.count i)

private theorem groupedLabels_perm (m : Word) : (groupedLabels m).Perm m.dedup :=
  List.perm_insertionSort _ _

private theorem groupedLabels_nodup (m : Word) : (groupedLabels m).Nodup :=
  (groupedLabels_perm m).nodup_iff.mpr (List.nodup_dedup _)

private theorem groupedLabels_mem (m : Word) (i : Fin 9) : i ∈ groupedLabels m ↔ i ∈ m :=
  (groupedLabels_perm m).mem_iff.trans List.mem_dedup

private theorem perm_expand (m : Word) : m.Perm (expand (fun i => m.count i) (groupedLabels m)) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [count_expand _ _ (groupedLabels_nodup m) _]
  simp only [groupedLabels_mem]
  by_cases h : i ∈ m
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, List.count_eq_zero_of_not_mem h]

def multiplicities (m : Word) : List ℕ := (groupedLabels m).map (fun i => m.count i)

private theorem multiplicities_sum (m : Word) : (multiplicities m).sum = m.length := by
  unfold multiplicities
  rw [← length_expand]
  exact (perm_expand m).length_eq.symm

private theorem multiplicities_positive (m : Word) : ∀ k ∈ multiplicities m, 0 < k := by
  intro k hk
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
  exact List.count_pos_iff.mpr ((groupedLabels_mem m i).mp hi)

private theorem multiplicities_sorted (m : Word) : (multiplicities m).Pairwise (· ≥ ·) := by
  rw [multiplicities, List.pairwise_map]
  exact List.pairwise_insertionSort (fun i j : Fin 9 => m.count j ≤ m.count i) _

private def compositions : ℕ → ℕ → List (List ℕ)
  | 0, n => if n = 0 then [[]] else []
  | _+1, 0 => [[]]
  | f+1, n+1 =>
    (List.range (n+1)).flatMap fun j => (compositions f (n-j)).map ((j+1) :: ·)

private theorem mem_compositions (l : List ℕ) (f : ℕ) (hf : l.length ≤ f)
    (hp : ∀ k ∈ l, 0 < k) : l ∈ compositions f l.sum := by
  induction l generalizing f with
  | nil => cases f <;> simp [compositions]
  | cons a l ih =>
    have hapos := hp a (by simp)
    cases a with
    | zero => omega
    | succ a =>
      cases f with
      | zero => simp at hf
      | succ f =>
        have h := ih f (by simpa using hf) (fun k hk => hp k (by simp [hk]))
        have he : (a+1) + l.sum = (a+l.sum)+1 := by omega
        change (a+1) :: l ∈ compositions (f+1) ((a+1) + l.sum)
        rw [he, compositions]
        apply List.mem_flatMap.mpr
        refine ⟨a, List.mem_range.mpr (by omega), List.mem_map.mpr ?_⟩
        exact ⟨l, by simpa using h, rfl⟩

private theorem length_le_sum_positive (l : List ℕ) (h : ∀ k ∈ l, 0 < k) : l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons k l ih =>
    have hk := h k (by simp)
    have hl := ih (fun j hj => h j (by simp [hj]))
    simp only [List.length_cons, List.sum_cons]
    omega

private def profiles7 : List (List ℕ) :=
  (compositions 7 7).filter fun l => decide (l.Pairwise (· ≥ ·))

private theorem multiplicities_cases (m : Word) (hm : m.length = 7) :
    multiplicities m ∈ profiles7 := by
  have hsum : (multiplicities m).sum = 7 := (multiplicities_sum m).trans hm
  have hpos := multiplicities_positive m
  have hlen := length_le_sum_positive _ hpos
  rw [hsum] at hlen
  have h := mem_compositions _ 7 hlen hpos
  rw [hsum] at h
  exact List.mem_filter.mpr ⟨h, decide_eq_true (multiplicities_sorted m)⟩

private theorem profiles7_explicit : profiles7 =
    [[1, 1, 1, 1, 1, 1, 1], [2, 1, 1, 1, 1, 1], [2, 2, 1, 1, 1], [2, 2, 2, 1], [3, 1, 1, 1, 1], [3, 2, 1, 1], [3, 2, 2], [3, 3, 1], [4, 1, 1, 1], [4, 2, 1], [4, 3], [5, 1, 1], [5, 2], [6, 1], [7]] := by decide

inductive Profile : Word → Prop where
  | p1111111 (a b c d e f g : Fin 9) (distinct : [a, b, c, d, e, f, g].Nodup) : Profile [a, b, c, d, e, f, g]
  | p211111 (a b c d e f : Fin 9) (distinct : [a, b, c, d, e, f].Nodup) : Profile [a, a, b, c, d, e, f]
  | p22111 (a b c d e : Fin 9) (distinct : [a, b, c, d, e].Nodup) : Profile [a, a, b, b, c, d, e]
  | p2221 (a b c d : Fin 9) (distinct : [a, b, c, d].Nodup) : Profile [a, a, b, b, c, c, d]
  | p31111 (a b c d e : Fin 9) (distinct : [a, b, c, d, e].Nodup) : Profile [a, a, a, b, c, d, e]
  | p3211 (a b c d : Fin 9) (distinct : [a, b, c, d].Nodup) : Profile [a, a, a, b, b, c, d]
  | p322 (a b c : Fin 9) (distinct : [a, b, c].Nodup) : Profile [a, a, a, b, b, c, c]
  | p331 (a b c : Fin 9) (distinct : [a, b, c].Nodup) : Profile [a, a, a, b, b, b, c]
  | p4111 (a b c d : Fin 9) (distinct : [a, b, c, d].Nodup) : Profile [a, a, a, a, b, c, d]
  | p421 (a b c : Fin 9) (distinct : [a, b, c].Nodup) : Profile [a, a, a, a, b, b, c]
  | p43 (a b : Fin 9) (distinct : [a, b].Nodup) : Profile [a, a, a, a, b, b, b]
  | p511 (a b c : Fin 9) (distinct : [a, b, c].Nodup) : Profile [a, a, a, a, a, b, c]
  | p52 (a b : Fin 9) (distinct : [a, b].Nodup) : Profile [a, a, a, a, a, b, b]
  | p61 (a b : Fin 9) (distinct : [a, b].Nodup) : Profile [a, a, a, a, a, a, b]
  | p7 (a : Fin 9) (distinct : [a].Nodup) : Profile [a, a, a, a, a, a, a]

theorem classify_profile (m : Word) (hm : m.length = 7) :
    ∃ n, m.Perm n ∧ Profile n := by
  have hc := multiplicities_cases m hm
  rw [profiles7_explicit] at hc
  have hd := groupedLabels_nodup m
  have hp := perm_expand m
  rw [expand_unpack] at hp
  change m.Perm (unpack (multiplicities m) (groupedLabels m)) at hp
  have hlen : (groupedLabels m).length = (multiplicities m).length := (List.length_map _).symm
  generalize hl : groupedLabels m = l at hd hp hlen
  generalize he : multiplicities m = cs at hc hp hlen
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, l⟩⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, b, c, d, e, f, g], hp, Profile.p1111111 a b c d e f g hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, l⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, b, c, d, e, f], hp, Profile.p211111 a b c d e f hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, b, b, c, d, e], hp, Profile.p22111 a b c d e hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, b, b, c, c, d], hp, Profile.p2221 a b c d hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, a, b, c, d, e], hp, Profile.p31111 a b c d e hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, a, b, b, c, d], hp, Profile.p3211 a b c d hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, a, b, b, c, c], hp, Profile.p322 a b c hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, a, b, b, b, c], hp, Profile.p331 a b c hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, a, a, b, c, d], hp, Profile.p4111 a b c d hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, a, a, b, b, c], hp, Profile.p421 a b c hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, a, a, b, b, b], hp, Profile.p43 a b hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, a, a, a, b, c], hp, Profile.p511 a b c hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, a, a, a, b, b], hp, Profile.p52 a b hd⟩
  · rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, a, a, a, a, b], hp, Profile.p61 a b hd⟩
  · rcases l with _ | ⟨a, l⟩ <;> simp only [List.length_cons, List.length_nil] at hlen <;> try omega
    have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[a, a, a, a, a, a, a], hp, Profile.p7 a hd⟩


end D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening
