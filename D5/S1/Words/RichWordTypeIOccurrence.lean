/- GID: D5/S1/Words/RichWordTypeIOccurrence
   generality: I
   mirror-B: D5/B/S1/Words/RichWordTypeIOccurrence
   mirror-E: none(waiver:source-word-combinatorics)
   anchors: []
   utility: none
   digest: Native seven-letter occurrences and Type-I return transport. -/
import D5.S1.Words.MBonacciSentinelDesubstitution
import Mathlib.Data.Matrix.Mul

/-! Native positions, exact cyclic extensions and componentwise return minima
for the fixed point of the seven-letter substitution with terminal image 066. -/

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

theorem word_eq_iterate (k n : ℕ) (hn : n < (image phi k 0).length) :
    word n = (image phi k 0)[n] := by
  have hk := iterate_prefix (Nat.le_max_left k (n+1))
  have hn' := iterate_prefix (Nat.le_max_right k (n+1))
  exact (hn'.getElem (by have := iterate_growth (n+1); omega)).trans
    (hk.getElem hn).symm

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
  simpa [factor, ← List.map_take, List.take_range, Nat.min_eq_left hlen] using ht.symm

/-- Boundary after the first i source letters, rather than an arbitrary coding. -/
def boundary (i : ℕ) : ℕ := (subst phi (factor word 0 i)).length

private theorem substituted_prefix (i : ℕ) :
    factor word 0 (boundary i) = subst phi (factor word 0 i) := by
  have hg : i ≤ (image phi (i+1) 0).length := by have := iterate_growth (i+1); omega
  have hp : factor word 0 i <+: image phi (i+1) 0 := by
    rw [← iterate_factor (i+1)]
    apply List.prefix_iff_eq_take.mpr
    simp only [factor, List.length_map, List.length_range, ← List.map_take,
      List.take_range, Nat.min_eq_left hg]
  exact factor_of_prefix (show subst phi (factor word 0 i) <+: image phi (i+2) 0 from
    hp.flatMap phi)
private theorem boundary_zero : boundary 0 = 0 := by simp [boundary, factor, subst]
theorem boundary_succ (i : ℕ) :
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
    (hc : word (i - 1) = 5 ∨ word (i - 1) = 6) : word (boundary i-1) = 6 := by
  have he : i-1+1 = i := by omega
  have hb := boundary_succ (i - 1)
  rw [he] at hb
  rcases hc with hc | hc
  · have hh := block_letter (i - 1) 1 (by simp [hc, phi])
    simpa [hb, hc, phi] using hh
  · have hh := block_letter (i - 1) 2 (by simp [hc, phi])
    simpa [hb, hc, phi] using hh

/-- The terminal interval is 6 followed by the substituted return with its FINAL
6 deleted. Both endpoints are actual boundaries; overlapping source windows are allowed. -/
theorem terminal_interval_cancellation {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hleft : word (a - 1) = 5 ∨ word (a - 1) = 6)
    (hright : word (b - 1) = 5 ∨ word (b - 1) = 6) :
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
  have he : (factor word q t.length).take s.length = factor word q s.length := by
    simp [factor, ← List.map_take, List.take_range, Nat.min_eq_left hp.length_le]
  rw [he, ← List.prefix_iff_eq_take.mp hp] at ht
  exact ht

theorem boundary_occ {s : Word} {a : ℕ} (h : Occ s a) :
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

def next (a : Letter) : Letter :=
  if h : a.val < 6 then ⟨a.val+1,by omega⟩ else 6

private theorem next_eq_six (a : Letter) : next a = 6 ↔ a = 5 ∨ a = 6 := by
  fin_cases a <;> norm_num [next]

theorem after_boundary (i : ℕ) : word (boundary i+1) = next (word i) := by
  have h := block_letter i 1 (by unfold phi; split <;> simp)
  unfold phi next at *
  split_ifs at * <;> simpa using h

theorem before_boundary {i : ℕ} (hi : 0 < i) :
    word (boundary i-1) = next (word (i - 1)) := by
  have he : i-1+1 = i := by omega
  have hb := boundary_succ (i - 1)
  rw [he] at hb
  by_cases hc : (word (i - 1)).val < 6
  · have h := block_letter (i - 1) 1 (by simp [phi,hc])
    simpa [hb,phi,next,hc] using h
  · have h := block_letter (i - 1) 2 (by simp [phi,hc])
    simpa [hb,phi,next,hc] using h

/-- Literal terminal extension of a finite source word. -/
def terminal (s : Word) : Word := [6] ++ subst phi s ++ [0,6]

private theorem terminal_eq (s : Word) : terminal s = 6::(sentinel s++[6]) := by
  simp [terminal,sentinel,List.append_assoc]

/-- Native terminal recognizability at unrestricted natural starts. The source
contexts are part of the equivalence, rather than a recurrence assumption. -/
theorem terminal_occurrence_iff (s : Word) (q : ℕ) :
    Occ (terminal s) q ↔ ∃ a, 0 < a ∧ q = boundary a-1 ∧ Occ s a ∧
      (word (a - 1) = 5 ∨ word (a - 1) = 6) ∧
      (word (a+s.length) = 5 ∨ word (a+s.length) = 6) := by
  rw [terminal_eq,occ_cons,occ_append]
  constructor
  · rintro ⟨hfirst,hs,hlast⟩
    obtain ⟨a,ha,ho⟩ := (ordinary_occurrence_iff _ _).mp hs
    have hapos : 0 < a := by
      by_contra h
      have hzero : a = 0 := by omega
      rw [hzero,boundary_zero] at ha
      omega
    have hq : q = boundary a-1 := by omega
    have hleft : next (word (a - 1)) = 6 := by
      rw [← before_boundary hapos, ← hq]
      exact hfirst
    have hpos : q+1+(sentinel s).length = boundary (a+s.length)+1 := by
      rw [ha,boundary_occ ho]
      simp [sentinel]
      omega
    have hright : next (word (a+s.length)) = 6 := by
      rw [occ_singleton,hpos,after_boundary] at hlast
      exact hlast
    exact ⟨a,hapos,hq,ho,(next_eq_six _).mp hleft,(next_eq_six _).mp hright⟩
  · rintro ⟨a,hapos,rfl,ho,hleft,hright⟩
    have hB : 0 < boundary a := by
      have h := boundary_strict hapos
      rw [boundary_zero] at h
      exact h
    have he : boundary a-1+1 = boundary a := by omega
    refine ⟨boundary_preceding_six hapos hleft, ?_, ?_⟩
    · rw [he]
      exact sentinel_transport ho
    · rw [occ_singleton,he]
      have hpos : boundary a+(sentinel s).length = boundary (a+s.length)+1 := by
        rw [boundary_occ ho]
        simp [sentinel]
        omega
      rw [hpos,after_boundary]
      exact (next_eq_six _).mpr hright

/-- Exact ordinary transfer of consecutive returns, including overlapping factors. -/
theorem ordinary_consecutive_iff (s : Word) (a b : ℕ) :
    Consecutive (sentinel s) (boundary a) (boundary b) ↔ Consecutive s a b := by
  constructor
  · rintro ⟨hab,ha,hb,hgap⟩
    have hab' : a < b := (boundary_strict.lt_iff_lt).mp hab
    refine ⟨hab',(sentinel_boundary s a).mp ha,(sentinel_boundary s b).mp hb,?_⟩
    intro c hac hcb hc
    exact hgap (boundary c) (boundary_strict hac) (boundary_strict hcb)
      (sentinel_transport hc)
  · rintro ⟨hab,ha,hb,hgap⟩
    refine ⟨boundary_strict hab,sentinel_transport ha,sentinel_transport hb,?_⟩
    intro q haq hqb hq
    obtain ⟨c,rfl,hc⟩ := (ordinary_occurrence_iff _ _).mp hq
    exact hgap c ((boundary_strict.lt_iff_lt).mp haq)
      ((boundary_strict.lt_iff_lt).mp hqb) hc

/-- Incidence columns are the actual seven-letter image counts. -/
def M : Matrix Letter Letter ℕ := fun a b => letterCount (phi b) a
def parikh (s : Word) : Letter → ℕ := letterCount s
def unit (c : Letter) : Letter → ℕ := Pi.single c 1

theorem parikh_append (s t : Word) : parikh (s++t) = parikh s+parikh t := by
  ext c
  simp [parikh,letterCount]

theorem parikh_singleton (c : Letter) : parikh [c] = unit c := by
  ext a
  fin_cases a <;> fin_cases c <;> rfl

theorem parikh_cons (c : Letter) (s : Word) :
    parikh (c::s) = unit c+parikh s := by
  simpa only [List.singleton_append,parikh_singleton] using parikh_append [c] s

theorem parikh_subst (s : Word) : parikh (subst phi s) = M.mulVec (parikh s) := by
  induction s with
  | nil =>
    ext c
    simp [parikh,letterCount,Matrix.mulVec,dotProduct]
  | cons c s ih =>
    rw [RankOneMorphismIterationBound.subst_cons,parikh_append,parikh_cons,Matrix.mulVec_add,← ih]
    congr 1
    ext a
    simp [unit,Matrix.mulVec_single_one,M,parikh]

/-- Terminal endpoint cancellation conserves the COMPLETE Parikh vector of
the substituted native return interval. -/
theorem terminal_return_parikh {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hleft : word (a - 1) = 5 ∨ word (a - 1) = 6)
    (hright : word (b - 1) = 5 ∨ word (b - 1) = 6) :
    parikh (returnWord (boundary a-1) (boundary b-1)) =
      M.mulVec (parikh (returnWord a b)) := by
  have hA : 0 < boundary a := by
    have h := boundary_strict ha
    rw [boundary_zero] at h
    exact h
  have hAB := boundary_strict hab
  have hlen : (subst phi (returnWord a b)).length = boundary b-boundary a := by
    have h := boundary_add a (b-a)
    rw [Nat.add_sub_of_le (Nat.le_of_lt hab)] at h
    dsimp [returnWord]
    omega
  have hs : factor word (boundary a) (boundary b-boundary a) =
      subst phi (returnWord a b) := by
    rw [← hlen]
    exact factor_subst a (b-a)
  have hdecomp : subst phi (returnWord a b) =
      factor word (boundary a) (boundary b-boundary a-1) ++ [6] := by
    rw [← hs,show boundary b-boundary a = (boundary b-boundary a-1)+1 by omega,factor_add]
    congr 1
    have he : boundary a+(boundary b-boundary a-1) = boundary b-1 := by omega
    simp [factor,he,boundary_preceding_six (by omega : 0 < b) hright]
  rw [terminal_interval_cancellation ha hab hleft hright,← parikh_subst,hdecomp]
  simp only [List.dropLast_concat,parikh_append]
  exact add_comm _ _

private theorem first_six : word 63 = 6 := by
  exact (word_eq_iterate 6 63 (by decide)).trans (by decide)

/-- A concrete native 0660 occurrence, with no primitivity or recurrence premise. -/
private theorem base_window :
    Occ [0,6,6,0] (boundary 63) := by
  have hb : Occ [0,6,6] (boundary 63) := by
    simpa [Occ,first_six,phi] using block_factor 63
  have he : boundary 63+3 = boundary 64 := by
    simpa [first_six,phi] using (boundary_succ 63).symm
  exact (occ_append [0,6,6] [0] _).mpr
    ⟨hb,(occ_singleton _ _).mpr (by simpa [he] using at_boundary 64)⟩

/-- An actual adjacent-six return realizes the base vector. EVERY actual base
return begins in 6 and hence dominates that vector componentwise. -/
theorem base_return_minimum :
    (∃ a b, Consecutive (typeI 0) a b ∧ returnWord a b = [6]) ∧
    ∀ a b, Consecutive (typeI 0) a b → unit 6 ≤ parikh (returnWord a b) := by
  have hwindow := base_window
  have h6 (j : ℕ) (hj : j = 1 ∨ j = 2) : word (boundary 63+j) = 6 := by
    have hh := congrArg (fun s : Word => s[j]?) hwindow
    rcases hj with rfl | rfl <;>
      simpa [Occ,factor] using hh
  constructor
  · refine ⟨boundary 63+1,boundary 63+2,?_,?_⟩
    · refine ⟨by omega,?_,?_,?_⟩
      · exact (occ_singleton _ _).mpr (h6 1 (Or.inl rfl))
      · exact (occ_singleton _ _).mpr (h6 2 (Or.inr rfl))
      · intro c hc hd
        omega
    · have he : boundary 63+2-(boundary 63+1) = 1 := by omega
      simp [returnWord,he,factor,h6 1 (Or.inl rfl)]
  · intro a b hab c
    have hstart : word a = 6 := (occ_singleton _ _).mp hab.2.1
    have hl : b-a = 1+(b-a-1) := by have := hab.1; omega
    have heq : returnWord a b = [6]++factor word (a+1) (b-a-1) := by
      dsimp [returnWord]
      rw [hl,factor_add]
      simp [factor,hstart]
    rw [heq,parikh_append,parikh_singleton]
    exact Nat.le_add_right _ _

/-- The literal extra letters at each phase, counted in all seven coordinates. -/
def increment (n : ℕ) : Letter → ℕ :=
  if n % 6 = 5 then unit 0+2 • unit 6 else unit 0

private theorem typeI_parikh_step (n : ℕ) :
    parikh (typeI (n+1)) = M.mulVec (parikh (typeI n))+increment n := by
  by_cases hn : n % 6 = 5
  · rw [typeI,if_pos hn,increment,if_pos hn]
    simp only [parikh_append,parikh_singleton,parikh_subst]
    rw [parikh_cons,parikh_singleton]
    simp only [two_nsmul]
    abel
  · rw [typeI,if_neg hn,increment,if_neg hn,parikh_append,parikh_singleton,parikh_subst]

private theorem image_parikh (n : ℕ) (c : Letter) :
    parikh (image phi n c) = (M^n).mulVec (unit c) := by
  induction n with
  | zero => simp [parikh_singleton]
  | succ n ih =>
    rw [RankOneMorphismIterationBound.image_succ,parikh_subst,ih,Matrix.mulVec_mulVec,
      ← pow_succ']

/-- Full actual-factor Parikh recurrence, its finite unrolling, and the exact
matrix vector of every iterated letter image. -/
theorem typeI_parikh_formula :
    (∀ n, parikh (typeI (n+1)) = M.mulVec (parikh (typeI n))+increment n) ∧
    (∀ n, parikh (typeI n) = (M^n).mulVec (unit 6) +
      ∑ k ∈ Finset.range n, (M^(n-1-k)).mulVec (increment k)) ∧
    (∀ n c, parikh (image phi n c) = (M^n).mulVec (unit c)) := by
  refine ⟨typeI_parikh_step,?_,image_parikh⟩
  intro n
  induction n with
  | zero => simp [typeI,parikh_singleton]
  | succ n ih =>
    rw [typeI_parikh_step,ih,Matrix.mulVec_add,Finset.sum_range_succ]
    have hsum (s : Finset ℕ) (f : ℕ → Letter → ℕ) :
        M.mulVec (∑ k ∈ s, f k) = ∑ k ∈ s, M.mulVec (f k) := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert k s hk ih => simp [hk,Matrix.mulVec_add,ih]
    rw [hsum]
    have hp : M.mulVec ((M^n).mulVec (unit 6)) = (M^(n+1)).mulVec (unit 6) := by
      rw [Matrix.mulVec_mulVec,← pow_succ']
    rw [hp]
    have he : (∑ k ∈ Finset.range n, M.mulVec ((M^(n-1-k)).mulVec (increment k))) =
        ∑ k ∈ Finset.range n, (M^(n+1-1-k)).mulVec (increment k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hexp : n+1-1-k = (n-1-k)+1 := by omega
      rw [hexp,Matrix.mulVec_mulVec,← pow_succ']
    rw [he]
    simp only [show n+1-1-n = 0 by omega,pow_zero,Matrix.one_mulVec]
    abel

theorem lext_iff (s : Word) (c : Letter) :
    c ∈ Lext s ↔ ∃ a, 0 < a ∧ Occ s a ∧ word (a - 1) = c := by
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨hc,hs⟩ := (occ_cons _ _ _).mp hq
    exact ⟨q+1,by omega,hs,by simpa using hc⟩
  · rintro ⟨a,ha,hs,hc⟩
    exact ⟨a-1,(occ_cons _ _ _).mpr ⟨hc,by simpa [Nat.sub_add_cancel ha] using hs⟩⟩

theorem rext_iff (s : Word) (c : Letter) :
    c ∈ Rext s ↔ ∃ a, Occ s a ∧ word (a+s.length) = c := by
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨hs,hc⟩ := (occ_append _ _ _).mp ha
    exact ⟨a,hs,(occ_singleton _ _).mp hc⟩
  · rintro ⟨a,hs,hc⟩
    exact ⟨a,(occ_append _ _ _).mpr ⟨hs,(occ_singleton _ _).mpr hc⟩⟩

private theorem sentinel_lext (s : Word) : Lext (sentinel s) = next '' Lext s := by
  ext d
  rw [lext_iff]
  constructor
  · rintro ⟨q,hq,ho,hd⟩
    obtain ⟨a,rfl,ha⟩ := (ordinary_occurrence_iff _ _).mp ho
    have hapos : 0 < a := by
      by_contra h
      have he : a = 0 := by omega
      simpa [he,boundary_zero] using hq
    exact ⟨word (a - 1),(lext_iff s _).mpr ⟨a,hapos,ha,rfl⟩,
      (before_boundary hapos).symm.trans hd⟩
  · rintro ⟨c,hc,rfl⟩
    obtain ⟨a,ha,ho,hc⟩ := (lext_iff s c).mp hc
    have hB : 0 < boundary a := by simpa [boundary_zero] using boundary_strict ha
    exact ⟨boundary a,hB,sentinel_transport ho,by rw [before_boundary ha,hc]⟩

private theorem sentinel_rext (s : Word) : Rext (sentinel s) = next '' Rext s := by
  ext d
  rw [rext_iff]
  constructor
  · rintro ⟨q,ho,hd⟩
    obtain ⟨a,rfl,ha⟩ := (ordinary_occurrence_iff _ _).mp ho
    have he : boundary a+(sentinel s).length = boundary (a+s.length)+1 := by
      rw [boundary_occ ha]; simp [sentinel]; omega
    exact ⟨word (a+s.length),(rext_iff s _).mpr ⟨a,ha,rfl⟩,
      by rw [he,after_boundary] at hd; exact hd⟩
  · rintro ⟨c,hc,rfl⟩
    obtain ⟨a,ho,hc⟩ := (rext_iff s c).mp hc
    have he : boundary a+(sentinel s).length = boundary (a+s.length)+1 := by
      rw [boundary_occ ho]; simp [sentinel]; omega
    exact ⟨boundary a,sentinel_transport ho,by rw [he,after_boundary,hc]⟩

def wrap (c : Letter) : Letter := if c = 6 then 6 else 0

theorem two_before_boundary {a : ℕ} (ha : 0 < a)
    (hc : word (a - 1) = 5 ∨ word (a - 1) = 6) :
    word (boundary a-2) = wrap (word (a - 1)) := by
  have hb := boundary_succ (a - 1)
  have he : a-1+1 = a := by omega
  rw [he] at hb
  rcases hc with hc | hc
  · simpa [hb,hc,phi,wrap] using at_boundary (a - 1)
  · have hh := block_letter (a - 1) 1 (by simp [hc,phi])
    simpa [hb,hc,phi,wrap] using hh

theorem two_after_boundary {a : ℕ}
    (hc : word a = 5 ∨ word a = 6) :
    word (boundary a+2) = wrap (word a) := by
  rcases hc with hc | hc
  · have h := at_boundary (a+1)
    simpa [boundary_succ,hc,phi,wrap] using h
  · have h := block_letter a 2 (by simp [hc,phi])
    simpa [hc,phi,wrap] using h

private def TerminalContexts (s : Word) : Prop :=
  ∀ a, Occ s a → 0 < a ∧
    (word (a - 1) = 5 ∨ word (a - 1) = 6) ∧
    (word (a+s.length) = 5 ∨ word (a+s.length) = 6)

private theorem terminal_lext (s : Word) (hs : TerminalContexts s) :
    Lext (terminal s) = wrap '' Lext s := by
  ext d
  rw [lext_iff]
  constructor
  · rintro ⟨q,hq,ho,hd⟩
    obtain ⟨a,ha,hqa,hoa,hleft,hright⟩ := (terminal_occurrence_iff _ _).mp ho
    refine ⟨word (a - 1),(lext_iff s _).mpr ⟨a,ha,hoa,rfl⟩,?_⟩
    have he : q-1 = boundary a-2 := by omega
    rw [he,two_before_boundary ha hleft] at hd
    exact hd
  · rintro ⟨c,hc,rfl⟩
    obtain ⟨a,ha,ho,hc⟩ := (lext_iff s c).mp hc
    obtain ⟨_,hleft,hright⟩ := hs a ho
    have hB : 2 ≤ boundary a := by
      have h := subst_length_ge (factor word 0 a)
      simp only [factor_len] at h
      change 2 ≤ (subst phi (factor word 0 a)).length
      omega
    refine ⟨boundary a-1,by omega,?_,?_⟩
    · exact (terminal_occurrence_iff _ _).mpr ⟨a,ha,rfl,ho,hleft,hright⟩
    · have he : boundary a-1-1 = boundary a-2 := by omega
      rw [he,two_before_boundary ha hleft,hc]

private theorem terminal_rext (s : Word) (hs : TerminalContexts s) :
    Rext (terminal s) = wrap '' Rext s := by
  ext d
  rw [rext_iff]
  constructor
  · rintro ⟨q,ho,hd⟩
    obtain ⟨a,ha,rfl,hoa,hleft,hright⟩ := (terminal_occurrence_iff _ _).mp ho
    have hB : 0 < boundary a := by simpa [boundary_zero] using boundary_strict ha
    have he : boundary a-1+(terminal s).length = boundary (a+s.length)+2 := by
      rw [boundary_occ hoa]
      simp [terminal]
      omega
    refine ⟨word (a+s.length),(rext_iff s _).mpr ⟨a,hoa,rfl⟩,?_⟩
    rw [he,two_after_boundary hright] at hd
    exact hd
  · rintro ⟨c,hc,rfl⟩
    obtain ⟨a,ho,hc⟩ := (rext_iff s c).mp hc
    obtain ⟨ha,hleft,hright⟩ := hs a ho
    have hB : 0 < boundary a := by simpa [boundary_zero] using boundary_strict ha
    have he : boundary a-1+(terminal s).length = boundary (a+s.length)+2 := by
      rw [boundary_occ ho]
      simp [terminal]
      omega
    refine ⟨boundary a-1,?_,?_⟩
    · exact (terminal_occurrence_iff _ _).mpr ⟨a,ha,rfl,ho,hleft,hright⟩
    · rw [he,two_after_boundary hright,hc]

private theorem six_neighbors {q : ℕ} (h : word q = 6) :
    0 < q ∧ (word (q-1) = 0 ∨ word (q-1) = 6) ∧
      (word (q+1) = 0 ∨ word (q+1) = 6) := by
  obtain ⟨i,hi,hj⟩ := boundary_window q
  have hne : q ≠ boundary i := by
    intro he
    rw [he,at_boundary] at h
    norm_num at h
  have hqpos : 0 < q := by omega
  rw [boundary_succ] at hj
  by_cases hc : (word i).val < 6
  · have hq : q = boundary i+1 := by simp [phi,hc] at hj; omega
    have hnext : word (q+1) = 0 := by
      have he : q+1 = boundary (i+1) := by rw [boundary_succ]; simp [phi,hc]; omega
      rw [he,at_boundary]
    exact ⟨hqpos,Or.inl (by simpa [hq] using at_boundary i),Or.inl hnext⟩
  · have hq : q = boundary i+1 ∨ q = boundary i+2 := by simp [phi,hc] at hj; omega
    have h6 : word (boundary i+1) = 6 := by
      simpa [phi,hc] using block_letter i 1 (by simp [phi,hc])
    have h6' : word (boundary i+2) = 6 := by
      simpa [phi,hc] using block_letter i 2 (by simp [phi,hc])
    rcases hq with hq | hq
    · exact ⟨hqpos,Or.inl (by simpa [hq] using at_boundary i),
        Or.inr (by simpa [hq,Nat.add_assoc] using h6')⟩
    · have hnext : word (q+1) = 0 := by
        have he : q+1 = boundary (i+1) := by
          rw [boundary_succ]; simp [phi,hc]; omega
        rw [he,at_boundary]
      exact ⟨hqpos,Or.inr (by simpa [hq,Nat.add_sub_assoc] using h6),Or.inl hnext⟩

private theorem base_extensions :
    Lext [6] = ({0,6} : Set Letter) ∧ Rext [6] = ({0,6} : Set Letter) := by
  have h06 : Occ [0,6] (boundary 63) := occ_prefix (by decide) base_window
  have ht : Occ [6,6,0] (boundary 63+1) := ((occ_cons _ _ _).mp base_window).2
  have h66 : Occ [6,6] (boundary 63+1) := occ_prefix (by decide) ht
  have h60 : Occ [6,0] (boundary 63+2) := by
    simpa [Nat.add_assoc] using ((occ_cons _ _ _).mp ht).2
  constructor
  · ext c
    constructor
    · rintro ⟨q,hq⟩
      obtain ⟨hc,hs⟩ := (occ_cons _ _ _).mp hq
      have h6 := (occ_singleton _ _).mp hs
      have hn := (six_neighbors h6).2.1
      simpa [hc] using hn
    · intro hc
      change c = 0 ∨ c = 6 at hc
      rcases hc with rfl | rfl
      · exact ⟨boundary 63,h06⟩
      · exact ⟨boundary 63+1,h66⟩
  · ext c
    constructor
    · rintro ⟨q,hq⟩
      obtain ⟨hs,hc⟩ := (occ_append _ _ _).mp hq
      have h6 := (occ_singleton _ _).mp hs
      have hn := (six_neighbors h6).2.2
      have hletter : word (q+1) = c := by simpa using (occ_singleton _ _).mp hc
      change c = 0 ∨ c = 6
      simpa only [hletter] using hn
    · intro hc
      change c = 0 ∨ c = 6 at hc
      rcases hc with rfl | rfl
      · exact ⟨boundary 63+2,h60⟩
      · exact ⟨boundary 63+1,h66⟩

def phase (n : ℕ) : Letter := ⟨n % 6,by omega⟩

private theorem terminal_contexts_of_extensions (n : ℕ) (hn : n % 6 = 5)
    (hL : Lext (typeI n) = {phase n,6}) (hR : Rext (typeI n) = {phase n,6}) :
    TerminalContexts (typeI n) := by
  intro a ha
  have hapos : 0 < a := by
    by_contra h
    have he : a = 0 := by omega
    exact typeI_not_at_origin n (he ▸ ha)
  have hl : word (a - 1) ∈ Lext (typeI n) :=
    (lext_iff _ _).mpr ⟨a,hapos,ha,rfl⟩
  have hr : word (a+(typeI n).length) ∈ Rext (typeI n) :=
    (rext_iff _ _).mpr ⟨a,ha,rfl⟩
  rw [hL] at hl
  rw [hR] at hr
  simpa [phase,hn] using And.intro hapos (And.intro hl hr)

/-- Both extension sets are exactly the cyclic index and 6, with membership
defined by actual occurrence witnesses. -/
theorem typeI_extensions (n : ℕ) :
    Lext (typeI n) = {phase n,6} ∧ Rext (typeI n) = {phase n,6} := by
  induction n with
  | zero => simpa [typeI,phase] using base_extensions
  | succ n ih =>
    by_cases hn : n % 6 = 5
    · have hc := terminal_contexts_of_extensions n hn ih.1 ih.2
      have he : typeI (n+1) = terminal (typeI n) := by simp [typeI,hn,terminal]
      have hp : phase (n+1) = 0 := by apply Fin.ext; simp [phase]; omega
      rw [hp,he,terminal_lext _ hc,terminal_rext _ hc,ih.1,ih.2]
      simp [Set.image_insert_eq,phase,hn,wrap]
    · have he : typeI (n+1) = sentinel (typeI n) := by simp [typeI,hn,sentinel]
      have hp : next (phase n) = phase (n+1) := by
        have hphase : (phase n).val < 6 := by dsimp [phase]; omega
        have hmod : n % 6 < 5 := by omega
        rw [next,dif_pos hphase]
        apply Fin.ext
        change n % 6+1 = (n+1) % 6
        omega
      rw [he,sentinel_lext,sentinel_rext,ih.1,ih.2]
      simp only [Set.image_insert_eq,Set.image_singleton,hp,show next 6 = 6 by decide]
      exact ⟨True.intro,True.intro⟩

/-- The source position map includes the terminal left shift. -/
def occurrenceMap (n a : ℕ) : ℕ :=
  if n % 6 = 5 then boundary a-1 else boundary a

theorem occurrenceMap_strict (n : ℕ) : StrictMono (occurrenceMap n) := by
  unfold occurrenceMap
  split
  · apply strictMono_nat_of_lt_succ
    intro a
    have hb := boundary_succ a
    have hl : 2 ≤ (phi (word a)).length := by unfold phi; split <;> simp
    omega
  · exact boundary_strict

/-- All-n, bidirectional native occurrence transfer. No context or return
assumption is left in the statement. -/
theorem typeI_occurrence_iff (n q : ℕ) :
    Occ (typeI (n+1)) q ↔ ∃ a, q = occurrenceMap n a ∧ Occ (typeI n) a := by
  by_cases hn : n % 6 = 5
  · have hc := terminal_contexts_of_extensions n hn
      (typeI_extensions n).1 (typeI_extensions n).2
    have he : typeI (n+1) = terminal (typeI n) := by simp [typeI,hn,terminal]
    rw [he,terminal_occurrence_iff]
    constructor
    · rintro ⟨a,ha,hq,ho,hleft,hright⟩
      exact ⟨a,by simpa [occurrenceMap,hn] using hq,ho⟩
    · rintro ⟨a,hq,ho⟩
      obtain ⟨ha,hleft,hright⟩ := hc a ho
      exact ⟨a,ha,by simpa [occurrenceMap,hn] using hq,ho,hleft,hright⟩
  · simpa [typeI,hn,sentinel,occurrenceMap] using ordinary_occurrence_iff (typeI n) q

private theorem consecutive_transport (s t : Word) (f : ℕ → ℕ) (hf : StrictMono f)
    (ho : ∀ q, Occ t q ↔ ∃ a, q = f a ∧ Occ s a) (a b : ℕ) :
    Consecutive t (f a) (f b) ↔ Consecutive s a b := by
  have hat (i : ℕ) : Occ t (f i) ↔ Occ s i := by
    rw [ho]
    constructor
    · rintro ⟨j,hj,hocc⟩
      have he : i = j := hf.injective hj
      simpa [he] using hocc
    · intro hi
      exact ⟨i,rfl,hi⟩
  constructor
  · rintro ⟨hab,ha,hb,hgap⟩
    refine ⟨hf.lt_iff_lt.mp hab,(hat a).mp ha,(hat b).mp hb,?_⟩
    intro c hac hcb hc
    exact hgap (f c) (hf hac) (hf hcb) ((hat c).mpr hc)
  · rintro ⟨hab,ha,hb,hgap⟩
    refine ⟨hf hab,(hat a).mpr ha,(hat b).mpr hb,?_⟩
    intro q haq hqb hq
    obtain ⟨c,rfl,hc⟩ := (ho q).mp hq
    exact hgap c (hf.lt_iff_lt.mp haq) (hf.lt_iff_lt.mp hqb) hc

/-- Every actual consecutive return is transferred in both directions. -/
theorem typeI_consecutive_iff (n a b : ℕ) :
    Consecutive (typeI (n+1)) (occurrenceMap n a) (occurrenceMap n b) ↔
      Consecutive (typeI n) a b :=
  consecutive_transport _ _ _ (occurrenceMap_strict n) (typeI_occurrence_iff n) a b

theorem ordinary_return_word {a b : ℕ} (hab : a < b) :
    returnWord (boundary a) (boundary b) = subst phi (returnWord a b) := by
  have h := boundary_add a (b-a)
  rw [Nat.add_sub_of_le (Nat.le_of_lt hab)] at h
  have he : boundary b-boundary a = (subst phi (returnWord a b)).length := by
    dsimp [returnWord]
    omega
  dsimp [returnWord]
  rw [he]
  exact factor_subst a (b-a)

/-- The COMPLETE count vector is multiplied by the actual incidence matrix at
every step, including the terminal endpoint cancellation. -/
theorem typeI_return_parikh (n a b : ℕ) (h : Consecutive (typeI n) a b) :
    parikh (returnWord (occurrenceMap n a) (occurrenceMap n b)) =
      M.mulVec (parikh (returnWord a b)) := by
  by_cases hn : n % 6 = 5
  · have hc := terminal_contexts_of_extensions n hn
      (typeI_extensions n).1 (typeI_extensions n).2
    obtain ⟨ha,hal,har⟩ := hc a h.2.1
    obtain ⟨hb,hbl,hbr⟩ := hc b h.2.2.1
    simpa [occurrenceMap,hn] using terminal_return_parikh ha h.1 hal hbl
  · simp only [occurrenceMap,if_neg hn,ordinary_return_word h.1,parikh_subst]

private theorem mulVec_mono {v w : Letter → ℕ} (h : v ≤ w) :
    M.mulVec v ≤ M.mulVec w := by
  intro a
  change (∑ c : Letter, M a c * v c) ≤ ∑ c : Letter, M a c * w c
  exact Finset.sum_le_sum (fun c _ => Nat.mul_le_mul_left (M a c) (h c))

/-- At every index an ACTUAL consecutive return attains M^n e6, and EVERY
actual consecutive return dominates it in all seven coordinates. -/
theorem typeI_return_minimum (n : ℕ) :
    (∃ a b, Consecutive (typeI n) a b ∧
      parikh (returnWord a b) = (M^n).mulVec (unit 6)) ∧
    ∀ a b, Consecutive (typeI n) a b →
      (M^n).mulVec (unit 6) ≤ parikh (returnWord a b) := by
  induction n with
  | zero =>
    constructor
    · obtain ⟨a,b,hc,hr⟩ := base_return_minimum.1
      exact ⟨a,b,hc,by simp [hr,parikh_singleton]⟩
    · simpa using base_return_minimum.2
  | succ n ih =>
    constructor
    · obtain ⟨a,b,hc,hr⟩ := ih.1
      refine ⟨occurrenceMap n a,occurrenceMap n b,
        (typeI_consecutive_iff n a b).mpr hc,?_⟩
      rw [typeI_return_parikh n a b hc,hr,Matrix.mulVec_mulVec,← pow_succ']
    · intro q r hqr
      obtain ⟨a,ha,hoa⟩ := (typeI_occurrence_iff n q).mp hqr.2.1
      obtain ⟨b,hb,hob⟩ := (typeI_occurrence_iff n r).mp hqr.2.2.1
      rw [ha,hb] at hqr ⊢
      have hc := (typeI_consecutive_iff n a b).mp hqr
      rw [typeI_return_parikh n a b hc,pow_succ',← Matrix.mulVec_mulVec]
      exact mulVec_mono (ih.2 a b hc)

end D5.S1.Words.RichWordTypeIOccurrence
