/- GID: D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Dice/EaslickMinimalAdvantage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Exact independent dice probabilities and their attainable least strict advantage. -/

import Mathlib.Tactic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Exact fair independent dice probabilities and nested padding of face multisets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage

/-- A die is its unique nondecreasing list of faces, with repetitions permitted. -/
def IsDie (n : ℕ) (d : List ℕ) : Prop :=
  d.length = n ∧ d.Pairwise (· ≤ ·) ∧ ∀ x ∈ d, 1 ≤ x ∧ x ≤ n

/-- Each occurrence of each face contributes separately to the strict-win count. -/
def winCount (d e : List ℕ) : ℕ :=
  (d.map fun x => (e.map fun y => if y < x then 1 else 0).sum).sum

/-- The actual uniform product sample space consists of the two face indices. -/
def indexWinCount (d e : List ℕ) : ℕ :=
  ∑ i : Fin d.length, ∑ j : Fin e.length, if e[j.val] < d[i.val] then 1 else 0

/-- Fair independent rolls give weight one over the product of the face counts. -/
def winProbability (d e : List ℕ) : ℚ :=
  (indexWinCount d e : ℚ) / (d.length * e.length : ℕ)

/-- The first integer strictly above half the number of ordered outcomes. -/
def threshold (n : ℕ) : ℕ := n * n / 2 + 1

/-- Minimum among the actual probabilities of all valid ordered pairs of dice. -/
def IsMinimum (n : ℕ) (p : ℚ) : Prop :=
  (∃ d e, IsDie n d ∧ IsDie n e ∧ winProbability d e = p) ∧
  1 / 2 < p ∧ ∀ d e, IsDie n d → IsDie n e →
    1 / 2 < winProbability d e → p ≤ winProbability d e

/-- Edges use the true attained minimum, without substituting a parity formula. -/
def Edge (n : ℕ) (d e : List ℕ) : Prop :=
  IsDie n d ∧ IsDie n e ∧ IsMinimum n (winProbability d e)

/-- A cycle uses k distinct dice and includes the last-to-first edge. -/
def HasCycle (n k : ℕ) : Prop :=
  ∃ c : List (List ℕ), c.length = k ∧ c.Nodup ∧ c ≠ [] ∧
    (c ++ [c.head!]).IsChain (Edge n)

/-- The global maximum simple-cycle length is exactly n. -/
def S (n : ℕ) : Prop := HasCycle n n ∧ ∀ k, n < k → ¬ HasCycle n k

/-- Easlick's complete Conjecture 1, with no assertion required below six. -/
def ConjectureOne : Prop := S 6 ∧ ∀ n : ℕ, 7 ≤ n → ¬ S n

/-- Counting face occurrences is exactly counting the uniform index product. -/
theorem winCount_eq_indexWinCount (d e : List ℕ) : winCount d e = indexWinCount d e := by
  have row (x : ℕ) : (e.map fun y => if y < x then 1 else 0).sum =
      ∑ j : Fin e.length, if e[j.val] < x then 1 else 0 := by
    rw [← List.ofFn_getElem_eq_map e (fun y => if y < x then 1 else 0), List.sum_ofFn]
  simp_rw [winCount, row]
  rw [indexWinCount, ← List.ofFn_getElem_eq_map d
    (fun x => ∑ j : Fin e.length, if e[j.val] < x then 1 else 0), List.sum_ofFn]

@[simp] private theorem wins_nil_left (e : List ℕ) : winCount [] e = 0 := by simp [winCount]
@[simp] private theorem wins_nil_right (d : List ℕ) : winCount d [] = 0 := by simp [winCount]

private theorem wins_append_left (a b e : List ℕ) :
    winCount (a ++ b) e = winCount a e + winCount b e := by simp [winCount]

private theorem wins_append_right (d a b : List ℕ) :
    winCount d (a ++ b) = winCount d a + winCount d b := by
  induction d with
  | nil => simp
  | cons x d ih =>
    simp only [winCount, List.map_cons, List.sum_cons, List.map_append, List.sum_append] at *
    omega

private theorem wins_replicate (a b m k : ℕ) :
    winCount (List.replicate m a) (List.replicate k b) =
      if b < a then m * k else 0 := by
  by_cases h : b < a <;> simp [winCount, h]

private theorem wins_shift (d e : List ℕ) (s : ℕ) :
    winCount (d.map (· + s)) (e.map (· + s)) = winCount d e := by
  simp [winCount, List.map_map, Function.comp_def]

private theorem wins_all (d e : List ℕ) (h : ∀ x ∈ d, ∀ y ∈ e, y < x) :
    winCount d e = d.length * e.length := by
  have row (x : ℕ) (hx : x ∈ d) :
      (e.map fun y => if y < x then 1 else 0).sum = e.length := by
    have : (e.map fun y => if y < x then 1 else 0) = e.map (fun _ => 1) := by
      apply List.map_congr_left
      intro y hy
      simp [h x hx y hy]
    rw [this]
    simp
  unfold winCount
  rw [List.map_congr_left row]
  simp

private theorem wins_none (d e : List ℕ) (h : ∀ x ∈ d, ∀ y ∈ e, x ≤ y) :
    winCount d e = 0 := by
  have row (x : ℕ) (hx : x ∈ d) :
      (e.map fun y => if y < x then 1 else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
    simp [Nat.not_lt.mpr (h x hx y hy)]
  unfold winCount
  rw [List.map_congr_left row]
  simp

private def evenX (k : ℕ) := List.replicate (k - 1) 1 ++ [2] ++ List.replicate k 3
private def evenY (k : ℕ) := [1] ++ List.replicate (2 * k - 1) 2
private def oddX (k : ℕ) := List.replicate k 1 ++ [2] ++ List.replicate k 3
private def oddY (k : ℕ) := List.replicate (k + 1) 1 ++ List.replicate k 2

private theorem even_valid (k : ℕ) (hk : 2 ≤ k) :
    IsDie (2*k) (evenX k) ∧ IsDie (2*k) (evenY k) := by
  constructor <;> simp [IsDie, evenX, evenY, List.pairwise_append,
    List.pairwise_replicate, List.mem_replicate] <;> aesop (add safe (by omega))

private theorem odd_valid (k : ℕ) (hk : 1 ≤ k) :
    IsDie (2*k+1) (oddX k) ∧ IsDie (2*k+1) (oddY k) := by
  constructor <;> simp [IsDie, oddX, oddY, List.pairwise_append,
    List.pairwise_replicate, List.mem_replicate] <;> aesop (add safe (by omega))

private theorem even_wins (k : ℕ) (hk : 2 ≤ k) :
    winCount (evenX k) (evenY k) = threshold (2*k) := by
  have hsq : 2*k*(2*k) = (2*k*k)*2 := by ring
  have hsub : 1 + (2*k-1) = 2*k := by omega
  simp [evenX, evenY, winCount, threshold, hsq, hsub]
  ring

private theorem odd_wins (k : ℕ) (_hk : 1 ≤ k) :
    winCount (oddX k) (oddY k) = threshold (2*k+1) := by
  have hsq : (2*k+1)*(2*k+1) = (2*k*k+2*k)*2+1 := by ring
  have hdiv : ((2*k*k+2*k)*2+1)/2 = 2*k*k+2*k := by omega
  simp [oddX, oddY, winCount, threshold, hsq, hdiv]
  ring

/-- The integer-grid lower bound is attained for every number of faces at least three. -/
theorem threshold_attained (n : ℕ) (hn : 3 ≤ n) :
    ∃ d e, IsDie n d ∧ IsDie n e ∧ winCount d e = threshold n := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have hn' : n = 2*k := by omega
    rw [hn']
    exact ⟨evenX k, evenY k, (even_valid k (by omega)).1,
      (even_valid k (by omega)).2, even_wins k (by omega)⟩
  · obtain ⟨k, hk⟩ := ho
    have hn' : n = 2*k+1 := by omega
    rw [hn']
    exact ⟨oddX k, oddY k, (odd_valid k (by omega)).1,
      (odd_valid k (by omega)).2, odd_wins k (by omega)⟩

/-- Above one half is exactly the integer threshold condition. -/
theorem above_half_iff (n : ℕ) (hn : 0 < n) (d e : List ℕ)
    (hd : IsDie n d) (he : IsDie n e) :
    1/2 < winProbability d e ↔ threshold n ≤ winCount d e := by
  have hden : (0 : ℚ) < (n*n : ℕ) := by positivity
  rw [winProbability, ← winCount_eq_indexWinCount, hd.1, he.1, lt_div_iff₀ hden]
  have hgrid : (1/2 : ℚ) * (n*n : ℕ) < (winCount d e : ℚ) ↔
      n*n < 2 * winCount d e := by
    constructor <;> intro h
    · exact_mod_cast (show ((n*n : ℕ) : ℚ) < 2 * (winCount d e : ℚ) by linarith)
    · have h' : ((n*n : ℕ) : ℚ) < 2 * (winCount d e : ℚ) := by exact_mod_cast h
      linarith
  rw [hgrid]
  unfold threshold
  omega

/-- The true minimum exists and is the threshold divided by n squared. -/
theorem minimum_probability (n : ℕ) (hn : 3 ≤ n) :
    IsMinimum n ((threshold n : ℚ) / (n*n : ℕ)) := by
  obtain ⟨d,e,hd,he,hw⟩ := threshold_attained n hn
  have hp : winProbability d e = (threshold n : ℚ) / (n*n : ℕ) := by
    simp [winProbability, ← winCount_eq_indexWinCount, hd.1, he.1, hw]
  refine ⟨⟨d,e,hd,he,hp⟩, ?_, ?_⟩
  · rw [← hp, above_half_iff n (by omega) d e hd he, hw]
  · intro a b ha hb hab
    have hh := (above_half_iff n (by omega) a b ha hb).mp hab
    unfold winProbability
    rw [← winCount_eq_indexWinCount, ha.1, hb.1]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hh) (by positivity)

/-- A valid pair is an edge precisely when its score is the attained threshold. -/
theorem edge_iff (n : ℕ) (hn : 3 ≤ n) (d e : List ℕ)
    (hd : IsDie n d) (he : IsDie n e) :
    Edge n d e ↔ winCount d e = threshold n := by
  have hm := minimum_probability n hn
  have hp : winProbability d e = (winCount d e : ℚ) / (n*n : ℕ) := by
    simp [winProbability, ← winCount_eq_indexWinCount, hd.1, he.1]
  constructor
  · intro h
    have hmin : winProbability d e = (threshold n : ℚ) / (n*n : ℕ) := by
      apply le_antisymm
      · obtain ⟨a,b,ha,hb,hab⟩ := hm.1
        simpa [hab] using h.2.2.2.2 a b ha hb (by simpa [hab] using hm.2.1)
      · exact hm.2.2 d e hd he h.2.2.2.1
    rw [hp] at hmin
    have : (winCount d e : ℚ) = (threshold n : ℚ) := by
      exact (div_left_inj' (c := ((n*n : ℕ) : ℚ)) (by positivity)).mp hmin
    exact_mod_cast this
  · intro h
    refine ⟨hd,he,?_⟩
    simpa [hp,h] using hm

private theorem sandwich_score (L D H L' E H' : List ℕ)
    (hLE : ∀ x ∈ L, ∀ y ∈ E, x ≤ y)
    (hDL : ∀ x ∈ D, ∀ y ∈ L', y < x)
    (hDH : ∀ x ∈ D, ∀ y ∈ H', x ≤ y)
    (hHE : ∀ x ∈ H, ∀ y ∈ E, y < x) :
    winCount (L ++ D ++ H) (L' ++ E ++ H') =
      winCount D E + D.length * L'.length + H.length * E.length +
        winCount (L ++ H) (L' ++ H') := by
  simp only [wins_append_left, wins_append_right]
  rw [wins_none L E hLE, wins_all D L' hDL, wins_none D H' hDH,
    wins_all H E hHE]
  omega

/-- Nested low/high padding, with the seed shifted into the central label interval. -/
def padded (b t j : ℕ) (odd : Bool) (d : List ℕ) : List ℕ :=
  List.replicate j (1 + 2*odd.toNat) ++
    List.replicate (t-j) (2 + 2*odd.toNat) ++ d.map (· + 4) ++
    List.replicate t (b+6-odd.toNat)

private theorem low_length (t j : ℕ) (c : Bool) (hj : j ≤ t) :
    (List.replicate j (1+2*c.toNat) ++ List.replicate (t-j) (2+2*c.toNat)).length = t := by
  simp
  omega

/-- Both orientations of the nested intervals add exactly the same strict-win score. -/
theorem padded_winCount (b t j k : ℕ) (c : Bool) (d e : List ℕ)
    (hj : j ≤ t) (hk : k ≤ t)
    (hd : ∀ x ∈ d, 1 ≤ x ∧ x ≤ b)
    (he : ∀ x ∈ e, 1 ≤ x ∧ x ≤ b) :
    winCount (padded b t j c d) (padded b t k (!c) e) =
      winCount d e + t*d.length + t*e.length + 2*t*t := by
  let L (u : ℕ) (a : Bool) :=
    List.replicate u (1+2*a.toNat) ++ List.replicate (t-u) (2+2*a.toNat)
  have hL (u : ℕ) (a : Bool) (hu : u ≤ t) : (L u a).length = t :=
    low_length t u a hu
  have lo (u : ℕ) (a : Bool) : ∀ x ∈ L u a, 1 ≤ x ∧ x ≤ 4 := by
    cases a <;> simp [L, List.mem_replicate] <;> omega
  have centerD : ∀ x ∈ d.map (·+4), 5 ≤ x ∧ x ≤ b+4 := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    have := hd y hy
    omega
  have centerE : ∀ x ∈ e.map (·+4), 5 ≤ x ∧ x ≤ b+4 := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    have := he y hy
    omega
  have hi (a : Bool) : b+4 < b+6-a.toNat := by cases a <;> simp <;> omega
  have hs := sandwich_score (L j c) (d.map (·+4)) (List.replicate t (b+6-c.toNat))
    (L k (!c)) (e.map (·+4)) (List.replicate t (b+6-(!c).toNat))
    (by intro x hx y hy; have := lo j c x hx; have := centerE y hy; omega)
    (by intro x hx y hy; have := centerD x hx; have := lo k (!c) y hy; omega)
    (by intro x hx y hy; have := centerD x hx
        have hy' : y = b+6-(!c).toNat := (List.mem_replicate.mp hy).2
        have := hi (!c); omega)
    (by intro x hx y hy; have := centerE y hy
        have hx' : x = b+6-c.toNat := (List.mem_replicate.mp hx).2
        have := hi c; omega)
  have hp : winCount (L j c ++ List.replicate t (b+6-c.toNat))
      (L k (!c) ++ List.replicate t (b+6-(!c).toNat)) = 2*t*t := by
    have h₁ : 2 < b+5 := by omega
    have h₂ : 4 < b+5 := by omega
    have hj' : j + (t-j) = t := by omega
    have hk' : k + (t-k) = t := by omega
    have h₃ : ¬ b+6 < 3 := by omega
    have h₄ : ¬ b+6 < 4 := by omega
    have hm₁ : t*(k+(t-k)+t) = 2*t*t := by rw [hk']; ring
    have hm₂ : (j+(t-j)+t)*(k+(t-k)) = 2*t*t := by rw [hj',hk']; ring
    cases c <;>
      simp [L, wins_append_left, wins_append_right, wins_replicate, h₁, h₂, h₃, h₄] <;>
      nlinarith [hm₁, hm₂]
  change winCount (L j c ++ d.map (·+4) ++ List.replicate t (b+6-c.toNat))
    (L k (!c) ++ e.map (·+4) ++ List.replicate t (b+6-(!c).toNat)) = _
  rw [hs, hp, wins_shift, List.length_map, List.length_map, List.length_replicate,
    hL k (!c) hk]
  ring

/-- Padding preserves the integer threshold for either seed parity. -/
theorem threshold_padding (r t : ℕ) :
    threshold (r+2*t) = threshold r + 2*t*r + 2*t*t := by
  have hsq : (r+2*t)*(r+2*t) = r*r + (2*t*r+2*t*t)*2 := by ring
  unfold threshold
  rw [hsq]
  omega

/-- Padding is a valid sorted die whenever all its labels fit in the target range. -/
theorem padded_isDie (r b t j : ℕ) (c : Bool) (d : List ℕ)
    (hj : j ≤ t) (hlen : d.length = r) (hsort : d.Pairwise (· ≤ ·))
    (hb : ∀ x ∈ d, 1 ≤ x ∧ x ≤ b) (hcap : b+6 ≤ r+2*t) :
    IsDie (r+2*t) (padded b t j c d) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [padded, hlen]
    omega
  · have hm : (d.map (·+4)).Pairwise (· ≤ ·) := by
      simpa only [List.pairwise_map, Nat.add_le_add_iff_right] using hsort
    cases c <;>
      simp [padded, List.pairwise_append, List.pairwise_replicate, List.mem_replicate, hm] <;>
      aesop (add safe (by omega)) (add safe (by have hx := hb _ (by assumption); omega))
  · intro x hx
    cases c <;>
      simp [padded, List.mem_replicate, List.mem_map] at hx <;>
      aesop (add safe (by omega)) (add safe (by have hx := hb _ (by assumption); omega))

private theorem padded_central (b t j : ℕ) (c : Bool) (d : List ℕ)
    (hb : ∀ x ∈ d, 1 ≤ x ∧ x ≤ b) :
    (padded b t j c d).filter (fun x => 5 ≤ x ∧ x ≤ b+4) = d.map (·+4) := by
  have hmid : (d.map (·+4)).filter (fun x => 5 ≤ x ∧ x ≤ b+4) = d.map (·+4) := by
    apply List.filter_eq_self.mpr
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    have := hb y hy
    simp
    omega
  have h₁ : ¬ b+5 ≤ b+4 := by omega
  have h₂ : ¬ b+6 ≤ b+4 := by omega
  cases c <;> simp [padded, List.filter_append, List.filter_replicate, hmid, h₁, h₂] <;> exact hb

private theorem padded_low_count (b t j : ℕ) (c : Bool) (d : List ℕ)
    (hb : ∀ x ∈ d, 1 ≤ x ∧ x ≤ b) :
    (padded b t j c d).count (1+2*c.toNat) = j := by
  have hmid : (d.map (·+4)).count (1+2*c.toNat) = 0 := by
    apply List.count_eq_zero.mpr
    intro h
    obtain ⟨y,hy,heq⟩ := List.mem_map.mp h
    have := hb y hy
    cases c <;> simp at heq <;> omega
  have h₁ : b+5 ≠ 3 := by omega
  have h₂ : b+6 ≠ 1 := by omega
  cases c <;> simp_all [padded, List.count_append, List.count_replicate]

/-- The central faces recover the seed, and a low-face multiplicity recovers the clone. -/
theorem padded_eq_imp (b t j k : ℕ) (c c' : Bool) (d e : List ℕ)
    (hd : ∀ x ∈ d, 1 ≤ x ∧ x ≤ b) (he : ∀ x ∈ e, 1 ≤ x ∧ x ≤ b)
    (h : padded b t j c d = padded b t k c' e) :
    d = e ∧ (c = c' → j = k) := by
  constructor
  · have hm := congrArg (fun l : List ℕ => l.filter (fun x => 5 ≤ x ∧ x ≤ b+4)) h
    rw [padded_central b t j c d hd, padded_central b t k c' e he] at hm
    exact (List.map_injective_iff.mpr (fun x y hxy => Nat.add_right_cancel hxy)) hm
  · intro hc
    subst c'
    have hm := congrArg (fun l : List ℕ => l.count (1+2*c.toNat)) h
    simpa only [padded_low_count b t j c d hd, padded_low_count b t k c e he] using hm

end D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage
