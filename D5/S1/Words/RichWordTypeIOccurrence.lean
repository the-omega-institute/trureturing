/- GID: D5/S1/Words/RichWordTypeIOccurrence
   generality: I
   mirror-B: D5/B/S1/Words/RichWordTypeIOccurrence
   mirror-E: none(waiver:source-word-combinatorics)
   anchors: []
   utility: none
   digest: Native seven-letter fixed word, exact boundaries and Type-I return endpoint cancellation. -/
import D5.S1.Words.MBonacciSentinelDesubstitution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RichWordTypeIOccurrence

open RankOneMorphismIterationBound (subst image subst_append image_add)
open AbelianBorders.AbelianBorderQuestionDefs (factor letterCount)
open MBonacciSentinelDesubstitution (factor_len factor_add factor_get)

abbrev Letter := Fin 7
abbrev Word := List Letter

/-- Literal source substitution; in particular the last image is 066. -/
def phi (a : Letter) : Word :=
  if h : a.val < 6 then [0, ⟨a.val + 1, by omega⟩] else [0, 6, 6]

private theorem phi_pos (a : Letter) : 0 < (phi a).length := by
  unfold phi; split <;> simp

private theorem subst_length_ge (s : Word) : 2 * s.length ≤ (subst phi s).length := by
  induction s with
  | nil => simp
  | cons a s ih =>
    have h : 2 ≤ (phi a).length := by unfold phi; split <;> simp
    simp only [RankOneMorphismIterationBound.subst_cons, List.length_append, List.length_cons]
    omega

private theorem image_pos (k : ℕ) (a : Letter) : 0 < (image phi k a).length := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := subst_length_ge (image phi k a)
    simp only [RankOneMorphismIterationBound.image_succ]
    omega

private theorem image_step (k : ℕ) :
    image phi (k + 1) 0 = image phi k 0 ++ image phi k 1 := by
  rw [image_add phi k 1]
  simp [phi, subst]

private theorem iterate_prefix_succ (k : ℕ) : image phi k 0 <+: image phi (k+1) 0 := by
  rw [image_step]; exact List.prefix_append _ _

private theorem iterate_prefix {k t : ℕ} (h : k ≤ t) : image phi k 0 <+: image phi t 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
  induction s with
  | zero => simp
  | succ s ih => exact (ih (by omega)).trans (iterate_prefix_succ (k+s))

private theorem iterate_growth (k : ℕ) : k+1 ≤ (image phi k 0).length := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [image_step, List.length_append]
    have := image_pos k 1
    omega

/-- Direct reading of the nested iterates of zero, with no recurrence premise. -/
def word (n : ℕ) : Letter :=
  (image phi (n+1) 0)[n]'(by have := iterate_growth (n+1); omega)

private theorem word_eq_iterate (k n : ℕ) (hn : n < (image phi k 0).length) :
    word n = (image phi k 0)[n] := by
  have hk := iterate_prefix (Nat.le_max_left k (n+1))
  have hn' := iterate_prefix (Nat.le_max_right k (n+1))
  exact (hn'.getElem (by have := iterate_growth (n+1); omega)).trans
    (hk.getElem hn).symm

private theorem factor_take (x : ℕ → Letter) (i n t : ℕ) (h : t ≤ n) :
    (factor x i n).take t = factor x i t := by
  simp [factor, ← List.map_take, List.take_range, Nat.min_eq_left h]

private theorem iterate_factor (k : ℕ) :
    factor word 0 (image phi k 0).length = image phi k 0 := by
  apply List.ext_getElem
  · exact factor_len _ _ _
  · intro i hi hj
    rw [factor_get _ _ _ _ (by simpa [factor_len] using hi)]
    simpa using word_eq_iterate k i hj

private theorem factor_of_prefix {s : Word} {k : ℕ} (h : s <+: image phi k 0) :
    factor word 0 s.length = s := by
  have hlen := h.length_le
  rw [← iterate_factor k] at h
  have ht := List.prefix_iff_eq_take.mp h
  rw [factor_take _ _ _ _ hlen] at ht
  exact ht.symm

/-- Boundary after the first i source letters, rather than an arbitrary coding. -/
def boundary (i : ℕ) : ℕ := (subst phi (factor word 0 i)).length

private theorem substituted_prefix (i : ℕ) :
    factor word 0 (boundary i) = subst phi (factor word 0 i) := by
  have hg : i ≤ (image phi (i+1) 0).length := by have := iterate_growth (i+1); omega
  have hp : factor word 0 i <+: image phi (i+1) 0 := by
    rw [← iterate_factor (i+1), ← factor_take _ _ _ _ hg]
    exact List.take_prefix _ _
  exact factor_of_prefix (show subst phi (factor word 0 i) <+: image phi (i+2) 0 from
    hp.flatMap phi)

private theorem boundary_zero : boundary 0 = 0 := by simp [boundary, factor, subst]

private theorem boundary_succ (i : ℕ) :
    boundary (i+1) = boundary i + (phi (word i)).length := by
  simp only [boundary, factor_add, subst_append, List.length_append]
  simp [factor, subst]

private theorem boundary_strict : StrictMono boundary := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [boundary_succ]
  have := phi_pos (word i)
  omega

private theorem block_factor (i : ℕ) :
    factor word (boundary i) (phi (word i)).length = phi (word i) := by
  have h := substituted_prefix (i+1)
  rw [boundary_succ, factor_add, substituted_prefix i] at h
  rw [factor_add, subst_append] at h
  simpa [factor, subst] using List.append_cancel_left h

private theorem block_letter (i j : ℕ) (hj : j < (phi (word i)).length) :
    word (boundary i+j) = (phi (word i))[j] := by
  have h := congrArg (fun s : Word => s[j]?) (block_factor i)
  simpa [List.getElem?_eq_getElem, factor_get, factor_len, hj] using h

private theorem at_boundary (i : ℕ) : word (boundary i) = 0 := by
  have h := block_letter i 0 (phi_pos _)
  unfold phi at h
  split_ifs at h <;> simpa using h

private theorem boundary_window (q : ℕ) : ∃ i, boundary i ≤ q ∧ q < boundary (i+1) := by
  induction q with
  | zero =>
    refine ⟨0, by rw [boundary_zero], ?_⟩
    have := boundary_strict (show 0 < 1 by omega)
    rw [boundary_zero] at this
    exact this
  | succ q ih =>
    obtain ⟨i, hi, hj⟩ := ih
    by_cases h : q+1 < boundary (i+1)
    · exact ⟨i, by omega, h⟩
    · have := boundary_strict (show i+1 < i+1+1 by omega)
      exact ⟨i+1, by omega, by omega⟩

private theorem zero_boundary (q : ℕ) : word q = 0 ↔ ∃ i, q = boundary i := by
  constructor
  · intro hz
    obtain ⟨i, hi, hj⟩ := boundary_window q
    refine ⟨i, ?_⟩
    by_contra hne
    have hlt : boundary i < q := by omega
    rw [boundary_succ] at hj
    by_cases ha : (word i).val < 6
    · have hq : q = boundary i+1 := by simp [phi, ha] at hj; omega
      have hb := block_letter i 1 (by simp [phi, ha])
      rw [hq, hb] at hz
      have hv := congrArg Fin.val hz
      simp [phi, ha] at hv
    · have hq : q = boundary i+1 ∨ q = boundary i+2 := by
        simp [phi, ha] at hj; omega
      rcases hq with hq | hq
      · have hb := block_letter i 1 (by simp [phi, ha])
        rw [hq, hb] at hz
        norm_num [phi, ha] at hz
      · have hb := block_letter i 2 (by simp [phi, ha])
        rw [hq, hb] at hz
        norm_num [phi, ha] at hz
  · rintro ⟨i, rfl⟩; exact at_boundary i

private theorem boundary_add (i n : ℕ) :
    boundary (i+n) = boundary i + (subst phi (factor word i n)).length := by
  simp only [boundary, factor_add, zero_add, subst_append, List.length_append]

private theorem factor_subst (i n : ℕ) :
    factor word (boundary i) (subst phi (factor word i n)).length =
      subst phi (factor word i n) := by
  have h := substituted_prefix (i+n)
  rw [boundary_add, factor_add, substituted_prefix i] at h
  rw [factor_add, subst_append] at h
  simp only [zero_add] at h
  exact List.append_cancel_left h

/-- Actual occurrence, including position zero and overlapping windows. -/
def Occ (s : Word) (q : ℕ) : Prop := factor word q s.length = s

/-- Consecutive starts; no nonoverlap condition is imposed. -/
def Consecutive (s : Word) (a b : ℕ) : Prop :=
  a < b ∧ Occ s a ∧ Occ s b ∧ ∀ c, a < c → c < b → ¬ Occ s c

/-- Return interval cut at the actual natural positions. -/
def returnWord (a b : ℕ) : Word := factor word a (b-a)

/-- The Type-I factors with the terminal cyclic branch kept literal. -/
def typeI : ℕ → Word
  | 0 => [6]
  | n+1 => if n % 6 = 5 then [6] ++ subst phi (typeI n) ++ [0,6]
      else subst phi (typeI n) ++ [0]

/-- Actual left and right extensions. -/
def Lext (s : Word) : Set Letter := {c | ∃ q, Occ (c :: s) q}
def Rext (s : Word) : Set Letter := {c | ∃ q, Occ (s ++ [c]) q}

private theorem occ_append (s t : Word) (q : ℕ) :
    Occ (s++t) q ↔ Occ s q ∧ Occ t (q+s.length) := by
  unfold Occ
  rw [List.length_append, factor_add]
  constructor
  · intro h
    have ht := congrArg (List.take s.length) h
    have hd := congrArg (List.drop s.length) h
    exact ⟨by simpa [factor_len] using ht, by simpa [factor_len] using hd⟩
  · rintro ⟨h,h'⟩; rw [h,h']

private theorem occ_singleton (a : Letter) (q : ℕ) : Occ [a] q ↔ word q = a := by
  simp [Occ, factor]

private theorem occ_cons (a : Letter) (s : Word) (q : ℕ) :
    Occ (a::s) q ↔ word q = a ∧ Occ s (q+1) := by
  simpa [occ_singleton] using occ_append [a] s q

private theorem word_zero : word 0 = 0 := by
  simpa using word_eq_iterate 0 0 (by simp)

/-- The native limit and exact fixed-point block law; zeros are precisely its boundaries. -/
theorem actual_fixed_point :
    (∀ k, factor word 0 (image phi k 0).length = image phi k 0) ∧
    StrictMono boundary ∧ boundary 0 = 0 ∧
    (∀ i, boundary i = ∑ j ∈ Finset.range i, (phi (word j)).length) ∧
    (∀ i n, factor word (boundary i) (subst phi (factor word i n)).length =
      subst phi (factor word i n)) ∧
    (∀ q, word q = 0 ↔ ∃! i, q = boundary i) := by
  refine ⟨iterate_factor, boundary_strict, boundary_zero, ?_, factor_subst, ?_⟩
  · intro i
    induction i with
    | zero => simp [boundary_zero]
    | succ i ih => rw [boundary_succ, Finset.sum_range_succ, ih]
  · intro q
    rw [zero_boundary]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, hi, fun j hj => boundary_strict.injective (hj.symm.trans hi)⟩
    · rintro ⟨i,hi,_⟩; exact ⟨i,hi⟩

private theorem boundary_preceding_six {i : ℕ} (hi : 0 < i)
    (hc : word (i-1) = 5 ∨ word (i-1) = 6) : word (boundary i-1) = 6 := by
  have he : i-1+1 = i := by omega
  have hb := boundary_succ (i-1)
  rw [he] at hb
  rcases hc with hc | hc
  · have hh := block_letter (i-1) 1 (by simp [hc, phi])
    simpa [hb, hc, phi] using hh
  · have hh := block_letter (i-1) 2 (by simp [hc, phi])
    simpa [hb, hc, phi] using hh

/-- The terminal interval is 6 followed by the substituted return with its FINAL
6 deleted. Both endpoints are actual boundaries; overlapping source windows are allowed. -/
theorem terminal_interval_cancellation {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hleft : word (a-1) = 5 ∨ word (a-1) = 6)
    (hright : word (b-1) = 5 ∨ word (b-1) = 6) :
    returnWord (boundary a-1) (boundary b-1) =
      [6] ++ (subst phi (returnWord a b)).dropLast := by
  have hA : 0 < boundary a := by
    have := boundary_strict ha
    rw [boundary_zero] at this
    exact this
  have hAB : boundary a < boundary b := boundary_strict hab
  have hB : 0 < boundary b := by omega
  have hlen : (subst phi (returnWord a b)).length = boundary b-boundary a := by
    have h := boundary_add a (b-a)
    rw [Nat.add_sub_of_le (Nat.le_of_lt hab)] at h
    dsimp [returnWord]
    omega
  have hs : factor word (boundary a) (boundary b-boundary a) =
      subst phi (returnWord a b) := by
    rw [← hlen]; exact factor_subst a (b-a)
  have hdecomp : subst phi (returnWord a b) =
      factor word (boundary a) (boundary b-boundary a-1) ++ [6] := by
    rw [← hs, show boundary b-boundary a = (boundary b-boundary a-1)+1 by omega,
      factor_add]
    congr 1
    have he : boundary a+(boundary b-boundary a-1) = boundary b-1 := by omega
    simp [factor, he, boundary_preceding_six (by omega : 0 < b) hright]
  rw [hdecomp]
  simp only [List.dropLast_concat]
  dsimp [returnWord]
  have he : boundary b-1-(boundary a-1) = 1+(boundary b-boundary a-1) := by omega
  rw [he, factor_add]
  have he' : boundary a-1+1 = boundary a := by omega
  simp [factor, he', boundary_preceding_six ha hleft]

/-- The trailing zero reserves the next true boundary. -/
def sentinel (s : Word) : Word := subst phi s ++ [0]

private theorem sentinel_cons (a : Letter) (s : Word) :
    sentinel (a::s) = phi a ++ sentinel s := by simp [sentinel, List.append_assoc]

private theorem sentinel_head (s : Word) : ∃ v, sentinel s = 0::v := by
  cases s with
  | nil => exact ⟨[], rfl⟩
  | cons a s =>
    rw [sentinel_cons]
    unfold phi
    split <;> exact ⟨_,rfl⟩

private theorem occ_prefix {s t : Word} {q : ℕ} (hp : s <+: t) (ho : Occ t q) :
    Occ s q := by
  have ht := congrArg (List.take s.length) ho
  rw [factor_take _ _ _ _ hp.length_le, ← List.prefix_iff_eq_take.mp hp] at ht
  exact ht

private theorem boundary_occ {s : Word} {a : ℕ} (h : Occ s a) :
    boundary (a+s.length) = boundary a+(subst phi s).length := by
  rw [boundary_add,h]

private theorem sentinel_transport {s : Word} {a : ℕ} (h : Occ s a) :
    Occ (sentinel s) (boundary a) := by
  apply (occ_append _ _ _).mpr
  constructor
  · have hf := factor_subst a s.length
    rw [h] at hf
    exact hf
  · apply (occ_singleton _ _).mpr
    rw [← boundary_occ h]
    exact at_boundary _

private def code (a : Letter) : Word := (phi a++[0]).take 3

private theorem code_length (a : Letter) : (code a).length = 3 := by
  unfold code phi
  split <;> simp

private theorem code_injective : Function.Injective code := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [code,phi]

private theorem sentinel_code_prefix (a : Letter) (s : Word) :
    code a <+: sentinel (a::s) := by
  apply (List.take_prefix 3 (phi a++[0])).trans
  obtain ⟨v,hv⟩ := sentinel_head s
  rw [sentinel_cons,hv]
  exact ⟨v,by simp [List.append_assoc]⟩

private theorem sentinel_decode {a : Letter} {s : Word} {i : ℕ}
    (h : Occ (sentinel (a::s)) (boundary i)) : word i = a := by
  have ho : Occ [word i] i := (occ_singleton _ _).mpr rfl
  have hc := occ_prefix (sentinel_code_prefix (word i) []) (sentinel_transport ho)
  have ha := occ_prefix (sentinel_code_prefix a s) h
  apply code_injective
  unfold Occ at hc ha
  rw [code_length] at hc ha
  exact hc.symm.trans ha

private theorem sentinel_boundary (s : Word) (i : ℕ) :
    Occ (sentinel s) (boundary i) ↔ Occ s i := by
  constructor
  · induction s generalizing i with
    | nil => intro _; simp [Occ,factor]
    | cons a s ih =>
      intro h
      have ha := sentinel_decode h
      rw [sentinel_cons] at h
      have ht := ((occ_append _ _ _).mp h).2
      rw [← ha, ← boundary_succ] at ht
      exact (occ_cons _ _ _).mpr ⟨ha, ih (i+1) ht⟩
  · exact sentinel_transport

/-- Every occurrence, at every natural position, parses to exactly one
preimage occurrence. The third letter distinguishes 06 from 066. -/
theorem ordinary_occurrence_iff (s : Word) (q : ℕ) :
    Occ (sentinel s) q ↔ ∃ i, q = boundary i ∧ Occ s i := by
  constructor
  · intro h
    obtain ⟨v,hv⟩ := sentinel_head s
    have hz : word q = 0 := by
      rw [hv] at h
      exact ((occ_cons _ _ _).mp h).1
    obtain ⟨i,hi⟩ := (zero_boundary q).mp hz
    exact ⟨i,hi,(sentinel_boundary s i).mp (hi ▸ h)⟩
  · rintro ⟨i,rfl,hi⟩
    exact sentinel_transport hi

/-- No Type-I occurrence is at the one-sided origin. -/
theorem typeI_not_at_origin (n : ℕ) : ¬ Occ (typeI n) 0 := by
  induction n with
  | zero => simp [typeI,occ_singleton,word_zero]
  | succ n ih =>
    intro h
    by_cases hn : n % 6 = 5
    · simp only [typeI,if_pos hn,List.singleton_append] at h
      have hh := ((occ_cons _ _ _).mp h).1
      rw [word_zero] at hh
      norm_num at hh
    · simp only [typeI,if_neg hn] at h
      change Occ (sentinel (typeI n)) 0 at h
      obtain ⟨i,hi,ho⟩ := (ordinary_occurrence_iff _ _).mp h
      have he : i = 0 := boundary_strict.injective (hi.symm.trans boundary_zero.symm)
      exact ih (he ▸ ho)

end D5.S1.Words.RichWordTypeIOccurrence
