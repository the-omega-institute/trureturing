/- GID: D5/S1/Words/TribonacciPrefixRefutation
   generality: I
   mirror-B: D5/B/S1/Words/TribonacciPrefixRefutation
   mirror-E: none(waiver:exact-logarithmic-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/TribonacciPrefixRefutation.claim; result=D5/S1/Words/TribonacciPrefixRefutation.result; claim=D5/S1/Words/TribonacciPrefixRefutation.claim
   digest: The literal Tribonacci recursive prefixes have quadratic alternating charge and refute the uniform logarithmic interval estimate. -/

import D5.S1.Words.TribonacciAlignedWindows
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.TribonacciPrefixRefutation

open RankOneMorphismIterationBound (subst image image_add subst_append)
open MBonacciSentinelDesubstitution (word)
open AbelianBorders.AbelianBorderQuestionDefs (factor)
open TribonacciAlignedWindows

abbrev Letter := Fin 3

/-- The fourth substitution iterate, used as the renormalized substitution. -/
def tau (a : Letter) : List Letter := image sigma 4 a

private theorem tau_A : tau 0 = [0,1,0,2,0,1,0,0,1,0,2,0,1] := by decide
private theorem tau_B : tau 1 = [0,1,0,2,0,1,0,0,1,0,2] := by decide
private theorem tau_C : tau 2 = [0,1,0,2,0,1,0] := by decide

def weight (a : Letter) : ℤ := if a = 0 then 2 else if a = 1 then 1 else 0

def signedWordSum (v : List Letter) : ℤ := (v.map weight).alternatingSum

@[simp] private theorem signedWordSum_nil : signedWordSum [] = 0 := by simp [signedWordSum]

private theorem signedWordSum_append_odd (u v : List Letter) (hu : Odd u.length) :
    signedWordSum (u ++ v) = signedWordSum u - signedWordSum v := by
  simp only [signedWordSum, List.map_append, List.alternatingSum_append]
  rw [List.length_map, hu.neg_one_pow, neg_one_smul]
  simp [sub_eq_add_neg]

private theorem signed_subst_odd (n : ℕ) (hodd : ∀ a : Letter,
    Odd (image sigma (4*n) a).length) (v : List Letter) :
    signedWordSum (subst (image sigma (4*n)) v) =
      (v.map (fun a => signedWordSum (image sigma (4*n) a))).alternatingSum := by
  induction v with
  | nil => simp [signedWordSum]
  | cons a v ih =>
    rw [RankOneMorphismIterationBound.subst_cons,
      signedWordSum_append_odd _ _ (hodd a), ih]
    simp [List.alternatingSum_cons]

def a (n : ℕ) : ℤ := signedWordSum (image sigma (4*n) 0)
def b (n : ℕ) : ℤ := signedWordSum (image sigma (4*n) 1)
def c (n : ℕ) : ℤ := signedWordSum (image sigma (4*n) 2)

private theorem four_odd (n : ℕ) (x : Letter) : Odd (image sigma (4*n) x).length := by
  rw [Nat.odd_iff]
  exact D5.S1.Words.TribonacciAlignedWindows.four_parity n x

private theorem abc_zero : a 0 = 2 ∧ b 0 = 1 ∧ c 0 = 0 := by
  norm_num [a, b, c, signedWordSum, image, weight]

private theorem abc_step (n : ℕ) :
    a (n+1) = a n ∧ b (n+1) = 2*a n-b n ∧ c (n+1) = 4*a n-2*b n-c n := by
  have ho : ∀ x : Letter, Odd (image sigma (4*n) x).length := four_odd n
  have hA : image sigma 4 0 = [0,1,0,2,0,1,0,0,1,0,2,0,1] := tau_A
  have hB : image sigma 4 1 = [0,1,0,2,0,1,0,0,1,0,2] := tau_B
  have hC : image sigma 4 2 = [0,1,0,2,0,1,0] := tau_C
  change signedWordSum (image sigma (4*(n+1)) 0) = a n ∧
    signedWordSum (image sigma (4*(n+1)) 1) = 2*a n-b n ∧
    signedWordSum (image sigma (4*(n+1)) 2) = 4*a n-2*b n-c n
  rw [show 4*(n+1) = 4*n+4 by omega, image_add, image_add, image_add]
  rw [hA, hB, hC]
  rw [signed_subst_odd n ho, signed_subst_odd n ho, signed_subst_odd n ho]
  simp only [List.map_cons, List.map_nil, List.alternatingSum_cons, a, b, c]
  norm_num
  constructor <;> ring_nf

private theorem abc_closed (n : ℕ) :
    a n = 2 ∧ b n = 2 - (-1 : ℤ)^n ∧ c n = 2 - (2*(n:ℤ)+2)*(-1 : ℤ)^n := by
  induction n with
  | zero => exact abc_zero
  | succ n ih =>
    rcases abc_step n with ⟨hsa,hsb,hsc⟩
    rcases ih with ⟨ha,hb,hc⟩
    constructor
    · rw [hsa, ha]
    constructor
    · rw [hsb, ha, hb, pow_succ]
      ring
    · rw [hsc, ha, hb, hc, pow_succ]
      push_cast
      ring

def prefixWord : ℕ → List Letter
  | 0 => []
  | n+1 => image sigma (4*(n+1)) 2 ++ prefixWord n

private theorem tau_A_decomposition (n : ℕ) :
    image sigma (4*(n+1)) 0 =
      image sigma (4*(n+1)) 2 ++ image sigma (4*n) 0 ++ image sigma (4*n) 1 ++
      image sigma (4*n) 0 ++ image sigma (4*n) 2 ++ image sigma (4*n) 0 ++
      image sigma (4*n) 1 := by
  have hA : image sigma 4 0 = [0,1,0,2,0,1,0,0,1,0,2,0,1] := tau_A
  have hC0 : image sigma 4 2 = [0,1,0,2,0,1,0] := tau_C
  have hc : image sigma (4*(n+1)) 2 =
      image sigma (4*n) 0 ++ image sigma (4*n) 1 ++ image sigma (4*n) 0 ++
      image sigma (4*n) 2 ++ image sigma (4*n) 0 ++ image sigma (4*n) 1 ++
      image sigma (4*n) 0 := by
    rw [show 4*(n+1) = 4*n+4 by omega, image_add, hC0]
    simp only [RankOneMorphismIterationBound.subst_cons,
      RankOneMorphismIterationBound.subst_nil, List.append_nil]
    simp [List.append_assoc]
  rw [show 4*(n+1) = 4*n+4 by omega, image_add]
  have hc' : image sigma (4*n+4) 2 =
      image sigma (4*n) 0 ++ image sigma (4*n) 1 ++ image sigma (4*n) 0 ++
      image sigma (4*n) 2 ++ image sigma (4*n) 0 ++ image sigma (4*n) 1 ++
      image sigma (4*n) 0 := by simpa [show 4*(n+1) = 4*n+4 by omega] using hc
  rw [hc'] -- expose the first block before normalizing the left side
  rw [hA]
  simp only [RankOneMorphismIterationBound.subst_cons,
    RankOneMorphismIterationBound.subst_nil, List.append_nil]
  simp [List.append_assoc]

private theorem prefixWord_embed (n : ℕ) : ∃ r, image sigma (4*n) 0 = prefixWord n ++ r := by
  induction n with
  | zero => exact ⟨image sigma 0 0, by simp [prefixWord, image]⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨r ++ image sigma (4*n) 1 ++ image sigma (4*n) 0 ++ image sigma (4*n) 2 ++
      image sigma (4*n) 0 ++ image sigma (4*n) 1, ?_⟩
    change image sigma (4*(n+1)) 0 =
      (image sigma (4*(n+1)) 2 ++ prefixWord n) ++ _
    rw [tau_A_decomposition n, ← List.append_assoc, hr]
    simp [List.append_assoc]

private theorem prefixWord_prefix (n : ℕ) : prefixWord n <+: image sigma (4*n) 0 := by
  rw [List.prefix_iff_eq_append]
  obtain ⟨r, hr⟩ := prefixWord_embed n
  rw [hr]
  simp

def prefixLength (n : ℕ) : ℕ := (prefixWord n).length

private theorem image_length_bound (n : ℕ) : (image sigma (4*n) 0).length ≤ 13^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 4*(n+1) = 4+4*n by omega, image_add]
    have h : ∀ w : List Letter, (subst (image sigma 4) w).length ≤ 13*w.length := by
      intro w
      induction w with
      | nil => simp [RankOneMorphismIterationBound.subst]
      | cons x w ihw =>
        simp only [RankOneMorphismIterationBound.subst_cons, List.length_append]
        have hx : (image sigma 4 x).length ≤ 13 := by
          fin_cases x <;> decide
        simp only [List.length_cons]
        omega
    have hh := h (image sigma (4*n) 0)
    calc
      (subst (image sigma 4) (image sigma (4*n) 0)).length ≤
          13 * (image sigma (4*n) 0).length := hh
      _ ≤ 13 * 13^n := by omega
      _ = 13^(n+1) := by rw [pow_succ]; ring

private theorem prefixWord_length_bound (n : ℕ) :
    0 < prefixLength (n+1) ∧ prefixLength (n+1) ≤ 13^(n+1) := by
  constructor
  · simp [prefixLength, prefixWord, MBonacciSentinelDesubstitution.image_pos]
  · exact (prefixWord_prefix (n+1)).length_le.trans (image_length_bound (n+1))

def prefixCharge (n : ℕ) : ℤ := signedWordSum (prefixWord n)

private theorem prefixCharge_step (n : ℕ) : prefixCharge (n+1) = c (n+1) - prefixCharge n := by
  change signedWordSum (image sigma (4*(n+1)) 2 ++ prefixWord n) = _
  rw [signedWordSum_append_odd _ _ (four_odd (n+1) 2)]
  rfl

private theorem prefixCharge_closed (n : ℕ) :
    prefixCharge n = 1 - (-1 : ℤ)^n * ((n:ℤ)^2 + 3*(n:ℤ) + 1) := by
  induction n with
  | zero => simp [prefixCharge, prefixWord]
  | succ n ih =>
    have hc := (abc_closed (n+1)).2.2
    rw [prefixCharge_step, hc, ih, pow_succ]
    push_cast
    ring

private theorem prefixWord_actual (n : ℕ) :
    factor W 0 (prefixLength n) = prefixWord n := by
  exact MBonacciSentinelDesubstitution.factor_of_prefix (by omega : 2 ≤ 3)
    (k := 4*n) (s := prefixWord n) (prefixWord_prefix n)

private theorem prefixCharge_abs_lower_succ (n : ℕ) :
    (n+1 : ℤ)^2 ≤ |prefixCharge (n+1)| := by
  rw [prefixCharge_closed]
  by_cases h : Even (n+1)
  · rw [h.neg_one_pow]
    simp only [one_mul]
    have hnonpos : 1 - (((n+1 : ℕ) : ℤ)^2 + 3*((n+1 : ℕ) : ℤ) + 1) ≤ 0 := by
      nlinarith [sq_nonneg (n+1 : ℤ)]
    have hcast : ((n+1 : ℕ) : ℤ) = (n : ℤ) + 1 := by norm_num
    rw [hcast] at hnonpos ⊢
    rw [abs_of_nonpos hnonpos]
    nlinarith [sq_nonneg (n+1 : ℤ)]
  · have ho : Odd (n+1) := (Nat.even_or_odd (n+1)).resolve_left h
    rw [ho.neg_one_pow]
    have hnonneg : 0 ≤ 1 - (-1 : ℤ) * (((n+1 : ℕ) : ℤ)^2 +
        3*((n+1 : ℕ) : ℤ) + 1) := by
      nlinarith [sq_nonneg (n+1 : ℤ)]
    have hcast : ((n+1 : ℕ) : ℤ) = (n : ℤ) + 1 := by norm_num
    rw [hcast] at hnonneg ⊢
    rw [abs_of_nonneg hnonneg]
    nlinarith [sq_nonneg (n+1 : ℤ)]

private theorem prefixCharge_abs_lower (n : ℕ) :
    (n : ℤ)^2 ≤ |prefixCharge n| := by
  cases n with
  | zero => simp [prefixCharge, prefixWord]
  | succ n => simpa using prefixCharge_abs_lower_succ n

def claim : Prop := ∃ K : ℝ, 0 < K ∧
  ∀ s m : ℕ, |(signedWordSum (factor W s m) : ℝ)| ≤ K * Real.log (m + 2)

private theorem prefix_log_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log (prefixLength n + 2) ≤ (n : ℝ) * Real.log 39 := by
  have hpow : ∀ k : ℕ, 1 ≤ k → 13^k + 2 ≤ 39^k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      simp only [pow_succ]
      by_cases hk0 : k = 0
      · subst k; norm_num
      · have hi := ih (by omega)
        have h39 : 1 ≤ 39^k := Nat.one_le_pow k 39 (by norm_num)
        have h13 : 0 ≤ 13^k := Nat.zero_le _
        nlinarith
  have hm : prefixLength n + 2 ≤ 39^n := by
    have hp := (prefixWord_length_bound (n-1)).2
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hp' : prefixLength n ≤ 13^n := by simpa [hn'] using hp
    have hpow' := hpow n hn
    omega
  have hmR : ((prefixLength n + 2 : ℕ) : ℝ) ≤ ((39^n : ℕ) : ℝ) := by
    exact_mod_cast hm
  have hmR' : (prefixLength n : ℝ) + 2 ≤ ((39^n : ℕ) : ℝ) := by
    simpa [Nat.cast_add] using hmR
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < prefixLength n + 2) hmR'
  simpa [Nat.cast_add, Nat.cast_pow, Real.log_pow] using hlog

theorem result : ¬ claim := by
  rintro ⟨K, hK, hclaim⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (K * Real.log 39)
  have hlog39 : 0 < Real.log 39 := Real.log_pos (by norm_num)
  have hn1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst n
    norm_num at hn ⊢
    exact (not_lt_of_ge (le_of_lt (mul_pos hK hlog39))) hn
  have hprefix := prefixWord_actual n
  have hbound := hclaim 0 (prefixLength n)
  rw [hprefix] at hbound
  have hlog := prefix_log_bound n hn1
  have hnreal : (n:ℝ) > K * Real.log 39 := by exact_mod_cast hn
  have hcontra : (n:ℝ)^2 > K * Real.log (prefixLength n + 2) := by
    have hnnonneg : (0:ℝ) ≤ n := by positivity
    have hnn : (1:ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith [hlog, hnreal, hK, hlog39]
  have habs : ((n:ℝ)^2 : ℝ) ≤ |(signedWordSum (prefixWord n) : ℝ)| := by
    have hlow' : (n:ℤ)^2 ≤ |prefixCharge n| := prefixCharge_abs_lower n
    simpa [prefixCharge] using (show ((n:ℝ)^2 : ℝ) ≤ (|prefixCharge n| : ℝ) by exact_mod_cast hlow')
  linarith

end D5.S1.Words.TribonacciPrefixRefutation
