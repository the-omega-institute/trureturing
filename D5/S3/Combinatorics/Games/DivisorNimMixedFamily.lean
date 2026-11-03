/- GID: D5/S3/Combinatorics/Games/DivisorNimMixedFamily
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimMixedFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete mixed two/four formula from the actual game recurrence. -/

import D5.S3.Combinatorics.Games.DivisorNimRevisedTargets
import D5.S3.Combinatorics.Games.DivisorNimGcdTwo

/-! The mixed two/four formula for all positive multiplicities and all indices.
The zero index omits the varying heap; deleting the last fixed two is included. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Games.DivisorNimGrundy
open D5.S0.Certificates.Games.CrimGrundyRefutation (mex mex_spec)

private def EvenBoard (P : Position) : Prop := Positive P ∧ ∀ x ∈ P, 2 ∣ x

private theorem odd_val {x : ℕ} (hx : x % 2 = 1) : valuation x = 0 :=
  padicValNat.eq_zero_of_not_dvd (by intro hd; have := Nat.mod_eq_zero_of_dvd hd; omega)

private theorem even_val {x : ℕ} (hx : 0 < x) (hd : 2 ∣ x) : 0 < valuation x := by
  have hv := (padicValNat_dvd_iff_le (p := 2) (n := 1) (by omega : x ≠ 0)).mp hd
  change 1 ≤ valuation x at hv
  omega

private theorem even_count_zero {P : Position} (hp : EvenBoard P) : countAt P 0 = 0 := by
  apply Multiset.countP_eq_zero.mpr
  intro x hx hv
  have := even_val (hp.1 x hx) (hp.2 x hx)
  omega

private theorem even_erase {P : Position} (hp : EvenBoard P) (h : ℕ) :
    EvenBoard (P.erase h) := by
  constructor
  · intro x hx; exact hp.1 x (Multiset.mem_of_mem_erase hx)
  · intro x hx; exact hp.2 x (Multiset.mem_of_mem_erase hx)

private theorem two_odds_zero {P : Position} (hp : EvenBoard P) {a b : ℕ}
    (ha : a % 2 = 1) (hb : b % 2 = 1) : grundy (a ::ₘ b ::ₘ P) = 0 := by
  have hap : 0 < a := by omega
  have hbp : 0 < b := by omega
  have hpos : Positive (a ::ₘ b ::ₘ P) := by
    intro x hx
    simp only [Multiset.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hap
    · exact hbp
    · exact hp.1 x hx
  have hdep : HasDepth (a ::ₘ b ::ₘ P) 0 :=
    ⟨fun _ _ => Nat.zero_le _, a, by simp, odd_val ha⟩
  apply (zero_iff_even_count hpos hdep).mpr
  have hc := even_count_zero hp
  have heq : countAt (a ::ₘ b ::ₘ P) 0 = 2 := by
    unfold countAt
    rw [Multiset.countP_cons, if_pos (odd_val ha), Multiset.countP_cons, if_pos (odd_val hb)]
    change countAt P 0 + 1 + 1 = 2
    omega
  rw [heq]
  decide

private theorem mex_zero_pair' (x : ℕ) : mex {0, x} = if x = 1 then 2 else 1 := by
  split_ifs with hx
  · subst x
    have hn := (mex_spec ({0, 1} : Finset ℕ)).1
    have hc := mex_le_card ({0, 1} : Finset ℕ)
    norm_num at hc
    have h0 : mex ({0, 1} : Finset ℕ) ≠ 0 := by intro he; apply hn; simp [he]
    have h1 : mex ({0, 1} : Finset ℕ) ≠ 1 := by intro he; apply hn; simp [he]
    omega
  · have hn := (mex_spec ({0, x} : Finset ℕ)).1
    have h0 : mex ({0, x} : Finset ℕ) ≠ 0 := by intro he; apply hn; simp [he]
    have hle : mex ({0, x} : Finset ℕ) ≤ 1 := by
      by_contra h
      have hm := (mex_spec ({0, x} : Finset ℕ)).2 1 (by omega)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      omega
    omega

/-- Adjoining one to an even positive board toggles only values one and two. -/
private theorem one_even_board {P : Position} (hp : Positive P) (he : ∀ x ∈ P, 2 ∣ x) :
    grundy (1 ::ₘ P) = if grundy P = 1 then 2 else 1 := by
  classical
  have heb : EvenBoard P := ⟨hp, he⟩
  have hs : (moves (1 ::ₘ P)).image grundy = {0, grundy P} := by
    ext v
    constructor
    · intro hv
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨h, hh, d, hd, rfl⟩ := moves_spec hQ
      rcases Multiset.mem_cons.mp hh with rfl | hh
      · have hd1 : d = 1 := by have := hd.1; have := hd.2.1; omega
        simp [successor, hd1]
      · have herase : (1 ::ₘ P).erase h = 1 ::ₘ P.erase h :=
          Multiset.erase_cons_tail_of_mem hh
        have hd1 : d = 1 := Nat.eq_one_of_dvd_one (hd.2.2 1 (by rw [herase]; simp))
        have hx : 1 < h := by
          have := hp h hh
          have := Nat.mod_eq_zero_of_dvd (he h hh)
          omega
        have hodd : (h - 1) % 2 = 1 := by
          have := Nat.mod_eq_zero_of_dvd (he h hh)
          omega
        have hsucc : successor (1 ::ₘ P) h d = 1 ::ₘ (h - 1) ::ₘ P.erase h := by
          rw [successor, herase, hd1, if_neg (by omega)]
          simp only [Multiset.cons_add]
          rw [add_comm (P.erase h), Multiset.singleton_add]
        rw [hsucc, two_odds_zero (even_erase heb h) (by decide) hodd]
        simp
    · intro hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      have hdel : P ∈ moves (1 ::ₘ P) := by
        have hm := successor_is_move (P := 1 ::ₘ P) (h := 1) (d := 1)
          (by simp) ⟨by decide, by decide, by intro x hx; exact one_dvd x⟩
        simpa [successor] using hm
      rcases hv with rfl | rfl
      · by_cases hz : P = 0
        · exact Finset.mem_image.mpr ⟨P, hdel, by rw [hz, grundy_empty]⟩
        · obtain ⟨h, hh⟩ := Multiset.exists_mem_of_ne_zero hz
          have hx : 1 < h := by
            have := hp h hh
            have := Nat.mod_eq_zero_of_dvd (he h hh)
            omega
          have hd : legal (1 ::ₘ P) h 1 :=
            ⟨by decide, by omega, by intro x hx; exact one_dvd x⟩
          have hsucc : successor (1 ::ₘ P) h 1 = 1 ::ₘ (h - 1) ::ₘ P.erase h := by
            rw [successor, Multiset.erase_cons_tail_of_mem hh, if_neg (by omega)]
            simp only [Multiset.cons_add]
            rw [add_comm (P.erase h), Multiset.singleton_add]
          refine Finset.mem_image.mpr ⟨_, successor_is_move (by simp [hh]) hd, ?_⟩
          rw [hsucc]
          exact two_odds_zero (even_erase heb h) (by decide) (by
            have := Nat.mod_eq_zero_of_dvd (he h hh); omega)
      · exact Finset.mem_image.mpr ⟨P, hdel, rfl⟩
  rw [grundy_eq, hs, mex_zero_pair']

/-- Every nonzero all-even board containing a two has value at least two. -/
private theorem even_two_lower {P : Position} (hp : Positive P) (he : ∀ x ∈ P, 2 ∣ x)
    (h2 : 2 ∈ P) (hg : grundy P ≠ 0) : 2 ≤ grundy P := by
  classical
  have hp' : Positive (P.erase 2) := (even_erase ⟨hp, he⟩ 2).1
  have he' : ∀ x ∈ P.erase 2, 2 ∣ x := (even_erase ⟨hp, he⟩ 2).2
  have hd1 : legal P 2 1 := ⟨by decide, by decide, by intro x hx; exact one_dvd x⟩
  have hd2 : legal P 2 2 := ⟨by decide, by decide, by
    intro x hx; exact he x (Multiset.mem_of_mem_erase hx)⟩
  have hm1 := successor_is_move h2 hd1
  have hm2 := successor_is_move h2 hd2
  have heq1 : successor P 2 1 = 1 ::ₘ P.erase 2 := by
    simp only [successor, show 2 - 1 = 1 by decide, if_neg (by decide : (1 : ℕ) ≠ 0)]
    rw [add_comm, Multiset.singleton_add]
  have heq2 : successor P 2 2 = P.erase 2 := by simp [successor]
  have hnot : grundy P ≠ 1 := by
    intro hg1
    apply grundy_not_follower P
    by_cases hx : grundy (P.erase 2) = 1
    · exact Finset.mem_image.mpr ⟨_, hm2, by rw [heq2, hx, hg1]⟩
    · exact Finset.mem_image.mpr ⟨_, hm1, by rw [heq1, one_even_board hp' he', if_neg hx, hg1]⟩
  omega


private theorem value_eq_of_options (P : Position) (z : ℕ)
    (hex : ∀ Q ∈ moves P, grundy Q ≠ z)
    (hcover : ∀ v < z, ∃ Q ∈ moves P, grundy Q = v) : grundy P = z := by
  classical
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · obtain ⟨Q, hQ, hv⟩ := hcover (grundy P) hlt
    exact grundy_not_follower P (Finset.mem_image.mpr ⟨Q, hQ, hv⟩)
  · obtain ⟨Q, hQ, hv⟩ := Finset.mem_image.mp (follower_mem_of_lt P hgt)
    exact hex Q hQ hv

/-- The three produced by changing a four to a three has value two. -/
private theorem three_even_board {P : Position} (hp : Positive P) (he : ∀ x ∈ P, 2 ∣ x)
    (h2 : 2 ∈ P) (hg : grundy P ≠ 0) (hz : grundy (2 ::ₘ P) = 0) :
    grundy (3 ::ₘ P) = 2 := by
  classical
  have heb : EvenBoard P := ⟨hp, he⟩
  have hlow := even_two_lower hp he h2 hg
  have hone : grundy (1 ::ₘ P) = 1 := by
    rw [one_even_board hp he, if_neg (by omega)]
  have hs1 : successor (3 ::ₘ P) 3 1 = 2 ::ₘ P := by
    simp only [successor, Multiset.erase_cons_head, show 3 - 1 = 2 by decide,
      if_neg (by decide : (2 : ℕ) ≠ 0)]
    rw [add_comm, Multiset.singleton_add]
  have hs2 : successor (3 ::ₘ P) 3 2 = 1 ::ₘ P := by
    simp only [successor, Multiset.erase_cons_head, show 3 - 2 = 1 by decide,
      if_neg (by decide : (1 : ℕ) ≠ 0)]
    rw [add_comm, Multiset.singleton_add]
  have hd1 : legal (3 ::ₘ P) 3 1 := ⟨by decide, by decide, by intro x hx; exact one_dvd x⟩
  have hd2 : legal (3 ::ₘ P) 3 2 := ⟨by decide, by decide, by simpa [dividesAll] using he⟩
  apply value_eq_of_options
  · intro Q hQ
    obtain ⟨h, hh, d, hd, rfl⟩ := moves_spec hQ
    rcases Multiset.mem_cons.mp hh with rfl | hh
    · have hdiv : d ∣ 2 := hd.2.2 2 (by simpa using h2)
      have hd12 : d = 1 ∨ d = 2 := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hdiv
      rcases hd12 with rfl | rfl
      · rw [hs1, hz]; decide
      · rw [hs2, hone]; decide
    · have herase : (3 ::ₘ P).erase h = 3 ::ₘ P.erase h :=
        Multiset.erase_cons_tail_of_mem hh
      have hd3 : d ∣ 3 := hd.2.2 3 (by rw [herase]; simp)
      have hd13 := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd3
      have hd1 : d = 1 := by
        rcases hd13 with hd1 | hd3
        · exact hd1
        · subst d
          by_cases hh2 : h = 2
          · subst h; have := hd.2.1; omega
          · have hm : 2 ∈ P.erase h := (Multiset.mem_erase_of_ne (Ne.symm hh2)).mpr h2
            have hx := hd.2.2 2 (by rw [herase]; simp [hm])
            norm_num at hx
      have hx : 1 < h := by
        have := hp h hh
        have := Nat.mod_eq_zero_of_dvd (he h hh)
        omega
      have hsucc : successor (3 ::ₘ P) h d = 3 ::ₘ (h - 1) ::ₘ P.erase h := by
        rw [successor, herase, hd1, if_neg (by omega)]
        simp only [Multiset.cons_add]
        rw [add_comm (P.erase h), Multiset.singleton_add]
      rw [hsucc, two_odds_zero (even_erase heb h) (by decide) (by
        have := Nat.mod_eq_zero_of_dvd (he h hh); omega)]
      decide
  · intro v hv
    interval_cases v
    · exact ⟨_, successor_is_move (by simp) hd1, hs1 ▸ hz⟩
    · exact ⟨_, successor_is_move (by simp) hd2, hs2 ▸ hone⟩



private theorem mixed_two (r s : ℕ) : mixedPosition (r + 1) s = 2 ::ₘ mixedPosition r s := by
  simp [mixedPosition, Multiset.replicate_succ, Multiset.cons_add]

private theorem mixed_four (r s : ℕ) : mixedPosition r (s + 1) = 4 ::ₘ mixedPosition r s := by
  simp [mixedPosition, Multiset.replicate_succ, Multiset.add_cons]

private theorem mixed_even (r s : ℕ) : EvenBoard (mixedPosition r s) := by
  constructor <;> intro x hx <;>
    simp only [mixedPosition, Multiset.mem_add, Multiset.mem_replicate] at hx <;>
    rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide

private theorem mixed_mem_two {r : ℕ} (s : ℕ) (hr : 0 < r) : 2 ∈ mixedPosition r s := by
  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_replicate.mpr ⟨hr.ne', rfl⟩))

private theorem mixed_gcd {r : ℕ} (s : ℕ) (hr : 0 < r) : (mixedPosition r s).gcd = 2 := by
  apply Nat.dvd_antisymm
  · exact Multiset.gcd_dvd (mixed_mem_two s hr)
  · exact Multiset.dvd_gcd.mpr (mixed_even r s).2

private theorem mixed_count (r s : ℕ) : countAt (mixedPosition r s) 1 = r := by
  have h2 : valuation 2 = 1 := by exact padicValNat_self
  have h4 : valuation 4 = 2 := by exact padicValNat.prime_pow 2
  have hbase : ∀ t, countAt (mixedPosition 0 t) 1 = 0 := by
    intro t
    induction t with
    | zero => simp [mixedPosition, countAt]
    | succ t ih =>
      rw [mixed_four]
      change (4 ::ₘ mixedPosition 0 t).countP _ = 0
      rw [Multiset.countP_cons, if_neg (by omega : valuation 4 ≠ 1)]
      exact ih
  induction r with
  | zero => exact hbase s
  | succ r ih =>
    rw [mixed_two]
    change (2 ::ₘ mixedPosition r s).countP _ = r + 1
    rw [Multiset.countP_cons, if_pos h2]
    exact congrArg (· + 1) ih

private theorem adjoin_cons (P : Position) (h n : ℕ) :
    adjoinHeap (h ::ₘ P) n = h ::ₘ adjoinHeap P n := by
  by_cases hn : n = 0
  · simp [adjoinHeap, hn]
  · simp only [adjoinHeap, if_neg hn, Multiset.cons_swap]

private theorem even_adjoin {P : Position} (hp : EvenBoard P) {n : ℕ} (hn : n % 2 = 0) :
    EvenBoard (adjoinHeap P n) := by
  by_cases hz : n = 0
  · simpa [adjoinHeap, hz] using hp
  · constructor <;> intro x hx <;>
      simp only [adjoinHeap, if_neg hz, Multiset.mem_cons] at hx <;>
      rcases hx with rfl | hx
    · omega
    · exact hp.1 x hx
    · exact Nat.dvd_of_mod_eq_zero hn
    · exact hp.2 x hx

private theorem mixed_zero {r s n : ℕ} (hr : 0 < r) (hn : n % 2 = 0) :
    fixedSequence (mixedPosition r s) n = 0 ↔ (r + n / 2) % 2 = 0 := by
  rw [gcd_two_zero_pattern (mixed_even r s).1 (mixed_gcd s hr), sixZeroPhase, mixed_count]
  split_ifs with hr2
  · have hmod := Nat.even_iff.mp hr2
    omega
  · have hmod : r % 2 ≠ 0 := fun h => hr2 (Nat.even_iff.mpr h)
    omega

/-- At a winning even mixed board, changing a four to a three supplies value two. -/
private theorem mixed_even_option_two {r s n : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hn : n % 2 = 0) (hwin : (r + n / 2) % 2 = 1) :
    ∃ Q ∈ moves (adjoinHeap (mixedPosition r s) n), grundy Q = 2 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  let B := adjoinHeap (mixedPosition r t) n
  have heb : EvenBoard B := even_adjoin (mixed_even r t) hn
  have h2 : 2 ∈ B := by
    dsimp [B, adjoinHeap]
    split_ifs <;> simp [mixed_mem_two t hr]
  have hg : grundy B ≠ 0 := by
    change fixedSequence (mixedPosition r t) n ≠ 0
    intro hz
    have := (mixed_zero hr hn).mp hz
    omega
  have hz : grundy (2 ::ₘ B) = 0 := by
    have hm := (mixed_zero (s := t) (by omega : 0 < r + 1) hn).mpr
      (by omega : (r + 1 + n / 2) % 2 = 0)
    simpa only [fixedSequence, mixed_two, adjoin_cons] using hm
  have hval := three_even_board heb.1 heb.2 h2 hg hz
  have hP : adjoinHeap (mixedPosition r (t + 1)) n = 4 ::ₘ B := by
    rw [mixed_four, adjoin_cons]
  have hd : legal (4 ::ₘ B) 4 1 := ⟨by decide, by decide, by intro x hx; exact one_dvd x⟩
  have hsucc : successor (4 ::ₘ B) 4 1 = 3 ::ₘ B := by
    simp only [successor, Multiset.erase_cons_head, show 4 - 1 = 3 by decide,
      if_neg (by decide : (3 : ℕ) ≠ 0)]
    rw [add_comm, Multiset.singleton_add]
  rw [hP]
  exact ⟨_, successor_is_move (by simp) hd, hsucc ▸ hval⟩

/-- Uniform lower bound needed before the exact mixed-family induction. -/
private theorem mixed_even_lower_three {r s n : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hn : n % 2 = 0) (hwin : (r + n / 2) % 2 = 1) :
    3 ≤ fixedSequence (mixedPosition r s) n := by
  have heb := even_adjoin (mixed_even r s) hn
  have h2 : 2 ∈ adjoinHeap (mixedPosition r s) n := by
    unfold adjoinHeap
    split_ifs <;> simp [mixed_mem_two s hr]
  have hg : grundy (adjoinHeap (mixedPosition r s) n) ≠ 0 := by
    change fixedSequence (mixedPosition r s) n ≠ 0
    intro hz
    have := (mixed_zero hr hn).mp hz
    omega
  have hlow := even_two_lower heb.1 heb.2 h2 hg
  obtain ⟨Q, hQ, hval⟩ := mixed_even_option_two hr hs hn hwin
  have hn2 : grundy (adjoinHeap (mixedPosition r s) n) ≠ 2 := by
    intro hg2
    exact grundy_not_follower _ (Finset.mem_image.mpr ⟨Q, hQ, hval.trans hg2.symm⟩)
  change 3 ≤ grundy (adjoinHeap (mixedPosition r s) n)
  omega



private theorem mex_eq_of_cover (S : Finset ℕ) (z : ℕ) (hex : z ∉ S)
    (hcover : ∀ v < z, v ∈ S) : mex S = z := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · exact (mex_spec S).1 (hcover _ hlt)
  · exact hex ((mex_spec S).2 z hgt)

private theorem mixed_even_range {r s n : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hn : n % 2 = 0) :
    fixedSequence (mixedPosition r s) n = 0 ∨ 3 ≤ fixedSequence (mixedPosition r s) n := by
  by_cases hz : (r + n / 2) % 2 = 0
  · exact Or.inl ((mixed_zero hr hn).mpr hz)
  · exact Or.inr (mixed_even_lower_three hr hs hn (by omega))

/-- Both odd phases of the mixed family, uniformly over all positive multiplicities. -/
private theorem mixed_odd_formula {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ∀ n, n % 2 = 1 → fixedSequence (mixedPosition r s) n =
      if n % 4 = 1 then 1 else 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ho
    by_cases hn1 : n = 1
    · subst n
      have he := one_even_board (mixed_even r s).1 (mixed_even r s).2
      have hrange := mixed_even_range (n := 0) hr hs (by decide)
      change grundy (mixedPosition r s) = 0 ∨ 3 ≤ grundy (mixedPosition r s) at hrange
      have hne : grundy (mixedPosition r s) ≠ 1 := by omega
      simpa [fixedSequence, adjoinHeap, hne] using he
    · have hn3 : 3 ≤ n := by omega
      have hrange := mixed_even_range (n := n - 1) hr hs (by omega)
      have hr := (gcd_two_odd_recurrence (mixed_even r s).1 (mixed_gcd s hr) hn3 ho).1
      have hi := ih (n - 2) (by omega) (by omega)
      rw [hr, hi]
      by_cases hn4 : n % 4 = 1
      · have hm : (n - 2) % 4 ≠ 1 := by omega
        rw [if_neg hm, if_pos hn4]
        apply mex_eq_of_cover
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        · intro v hv
          have hv0 : v = 0 := by omega
          simp [hv0]
      · have hm : (n - 2) % 4 = 1 := by omega
        rw [if_pos hm, if_neg hn4]
        apply mex_eq_of_cover
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        · intro v hv
          interval_cases v <;> simp



private theorem two_fixed_values {n : ℕ} (hn : 2 ≤ n) (he : n % 2 = 0) :
    fixedMoveValues ({2} : Position) n = {1, n} := by
  classical
  have hdata : fixedMoveData ({2} : Position) = {(2, 1), (2, 2)} := by
    ext ⟨h, d⟩
    simp only [mem_fixedMoveData, Multiset.mem_singleton, legal, dividesAll,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, hd0, hd2, _⟩
      omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
  have h1 : fixedSequence ({1} : Position) n = 1 := by
    have hp : Positive ({n} : Position) := by
      intro x hx
      have hx' : x = n := by simpa using hx
      omega
    have hd : ∀ x ∈ ({n} : Position), 2 ∣ x := by
      intro x hx
      have hx' : x = n := by simpa using hx
      rw [hx']; exact Nat.dvd_of_mod_eq_zero he
    have hval := one_even_board hp hd
    rw [singleton_grundy n (by omega), if_neg (by omega : n ≠ 1)] at hval
    simp only [fixedSequence, adjoinHeap, if_neg (by omega : n ≠ 0)]
    change grundy (n ::ₘ 1 ::ₘ 0) = 1
    rw [Multiset.cons_swap]
    exact hval
  have h0 : fixedSequence (0 : Position) n = n := by
    simpa [fixedSequence, adjoinHeap, show n ≠ 0 by omega] using singleton_grundy n (by omega)
  have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero he
  have hfilter : ({p ∈ ({(2, 1), (2, 2)} : Finset (ℕ × ℕ)) | p.2 ∣ n}) = {(2, 1), (2, 2)} := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact one_dvd _
    · exact hd
  unfold fixedMoveValues
  rw [hdata, hfilter]
  simp only [Finset.image_insert, Finset.image_singleton]
  have hs1 : successor ({2} : Position) 2 1 = {1} := by simp [successor]
  have hs2 : successor ({2} : Position) 2 2 = 0 := by simp [successor]
  change {fixedSequence (successor ({2} : Position) 2 1) n,
    fixedSequence (successor ({2} : Position) 2 2) n} = _
  rw [hs1, hs2, h1, h0]

private def pairFormula (n : ℕ) : ℕ :=
  if n = 0 then 2 else if n % 4 = 0 then 3 else
    if n % 4 = 1 then 1 else if n % 4 = 2 then 0 else 2

private theorem pair_two_formula (n : ℕ) : fixedSequence ({2} : Position) n = pairFormula n := by
  have hp : Positive ({2} : Position) := by
    intro x hx
    have hx' : x = 2 := by simpa using hx
    omega
  have hg : ({2} : Position).gcd = 2 := by simp
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      simpa [fixedSequence, adjoinHeap, pairFormula] using singleton_grundy 2 (by decide)
    by_cases h1 : n = 1
    · subst n
      have he : ∀ x ∈ ({2} : Position), 2 ∣ x := by
        intro x hx
        have hx' : x = 2 := by simpa using hx
        simp [hx']
      have hv := one_even_board hp he
      rw [singleton_grundy 2 (by decide)] at hv
      simpa [fixedSequence, adjoinHeap, pairFormula] using hv
    have hn : 2 ≤ n := by omega
    have hr := gcd_two_recurrence hp hg hn
    rw [ih (n - 1) (by omega), ih (n - 2) (by omega)] at hr
    by_cases he : n % 2 = 0
    · rw [two_fixed_values hn he] at hr
      rw [hr]
      have hmod : n % 4 = 0 ∨ n % 4 = 2 := by omega
      rcases hmod with hm | hm
      · have hn4 : 4 ≤ n := by omega
        have hm1 : (n - 1) % 4 = 3 := by omega
        have hm2 : (n - 2) % 4 = 2 := by omega
        simp only [pairFormula, if_neg hz, if_pos hm,
          if_neg (by omega : n - 1 ≠ 0), if_neg (by omega : n - 2 ≠ 0),
          hm1, hm2]
        norm_num
        apply mex_eq_of_cover
        · simp; omega
        · intro v hv; interval_cases v <;> simp
      · have hm1 : (n - 1) % 4 = 1 := by omega
        have hm2 : (n - 2) % 4 = 0 := by omega
        simp only [pairFormula, if_neg hz, hm, hm1, hm2]
        norm_num
        apply mex_eq_of_cover
        · by_cases hn2 : n - 2 = 0 <;> simp [hn2, show n - 1 ≠ 0 by omega] <;> omega
        · omega
    · have ho : n % 2 = 1 := by omega
      rw [gcd_two_odd_fixed_values hp hg ho] at hr
      rw [hr]
      have hmod : n % 4 = 1 ∨ n % 4 = 3 := by omega
      rcases hmod with hm | hm
      · have hn5 : 5 ≤ n := by omega
        have hm1 : (n - 1) % 4 = 0 := by omega
        have hm2 : (n - 2) % 4 = 3 := by omega
        simp only [pairFormula, if_neg hz, hm, hm1, hm2,
          if_neg (by omega : n - 1 ≠ 0), if_neg (by omega : n - 2 ≠ 0)]
        norm_num
        apply mex_eq_of_cover
        · simp
        · intro v hv
          have hv0 : v = 0 := by omega
          simp [hv0]
      · have hn3 : 3 ≤ n := by omega
        have hm1 : (n - 1) % 4 = 2 := by omega
        have hm2 : (n - 2) % 4 = 1 := by omega
        simp only [pairFormula, if_neg hz, hm, hm1, hm2,
          if_neg (by omega : n - 1 ≠ 0), if_neg (by omega : n - 2 ≠ 0)]
        norm_num
        apply mex_eq_of_cover
        · simp
        · intro v hv; interval_cases v <;> simp

/-- The one-two boundary needed when the last fixed two is deleted. -/
private theorem pair_two_multiple_four {n : ℕ} (hn : 0 < n) (h4 : 4 ∣ n) :
    fixedSequence ({2} : Position) n = 3 := by
  rw [pair_two_formula]
  simp [pairFormula, hn.ne', Nat.mod_eq_zero_of_dvd h4]



private theorem successor_cons_small (P : Position) {h d : ℕ} (hd : d < h) :
    successor (h ::ₘ P) h d = (h - d) ::ₘ P := by
  simp only [successor, Multiset.erase_cons_head, if_neg (by omega : h - d ≠ 0)]
  rw [add_comm, Multiset.singleton_add]

private theorem fixed_successor {P : Position} {h : ℕ} (hh : h ∈ P) (d n : ℕ) :
    successor (adjoinHeap P n) h d = adjoinHeap (successor P h d) n := by
  by_cases hn : n = 0
  · simp [adjoinHeap, hn]
  · simp only [adjoinHeap, if_neg hn, successor, Multiset.erase_cons_tail_of_mem hh,
      Multiset.cons_add]

private theorem varying_successor (P : Position) {n d : ℕ} (hn : n ≠ 0) :
    successor (adjoinHeap P n) n d = adjoinHeap P (n - d) := by
  by_cases hz : n - d = 0
  · simp [adjoinHeap, hn, successor, hz]
  · simp only [adjoinHeap, if_neg hn, successor, Multiset.erase_cons_head, if_neg hz]
    rw [add_comm, Multiset.singleton_add]

private theorem mixed_three_value {r t n : ℕ} (hr : 0 < r) (hn : n % 2 = 0)
    (hwin : (r + n / 2) % 2 = 1) :
    grundy (3 ::ₘ adjoinHeap (mixedPosition r t) n) = 2 := by
  let B := adjoinHeap (mixedPosition r t) n
  have heb := even_adjoin (mixed_even r t) hn
  have h2 : 2 ∈ B := by
    dsimp [B, adjoinHeap]
    split_ifs <;> simp [mixed_mem_two t hr]
  have hg : grundy B ≠ 0 := by
    change fixedSequence (mixedPosition r t) n ≠ 0
    intro hz
    have := (mixed_zero hr hn).mp hz
    omega
  have hz : grundy (2 ::ₘ B) = 0 := by
    have hm := (mixed_zero (s := t) (by omega : 0 < r + 1) hn).mpr
      (by omega : (r + 1 + n / 2) % 2 = 0)
    simpa only [fixedSequence, mixed_two, adjoin_cons] using hm
  exact three_even_board heb.1 heb.2 h2 hg hz

/-- The complete omission-aware mixed two/four formula, for unbounded multiplicities. -/
theorem mixed_formula_statement : MixedFormulaStatement := by
  classical
  have main : ∀ s, 0 < s → ∀ r n, 0 < r →
      fixedSequence (mixedPosition r s) n = mixedFormula r n := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro hs r n hr
      by_cases ho : n % 2 = 1
      · rw [mixed_odd_formula hr hs n ho]
        unfold mixedFormula
        split_ifs <;> omega
      have hn : n % 2 = 0 := by omega
      by_cases hz : (r + n / 2) % 2 = 0
      · rw [(mixed_zero hr hn).mpr hz]
        simp [mixedFormula, show n % 4 ≠ 1 by omega, show n % 4 ≠ 3 by omega, hz]
      have hwin : (r + n / 2) % 2 = 1 := by omega
      have hlow := mixed_even_lower_three hr hs hn hwin
      have hgoal : mixedFormula r n = 3 := by
        simp [mixedFormula, show n % 4 ≠ 1 by omega, show n % 4 ≠ 3 by omega, hwin]
      rw [hgoal]
      change grundy (adjoinHeap (mixedPosition r s) n) = 3
      apply value_eq_of_options
      · intro Q hQ
        obtain ⟨h, hh, d, hd, rfl⟩ := moves_spec hQ
        have hfixed : h ∈ mixedPosition r s ∨ (n ≠ 0 ∧ h = n) := by
          by_cases hn0 : n = 0
          · left; simpa [adjoinHeap, hn0] using hh
          · simp only [adjoinHeap, if_neg hn0, Multiset.mem_cons] at hh
            rcases hh with rfl | hh
            · exact Or.inr ⟨hn0, rfl⟩
            · exact Or.inl hh
        rcases hfixed with hfixed | ⟨hn0, heq⟩
        · have h24 : h = 2 ∨ h = 4 := by
            simp only [mixedPosition, Multiset.mem_add, Multiset.mem_replicate] at hfixed
            rcases hfixed with ⟨_, h2⟩ | ⟨_, h4⟩
            · exact Or.inl h2
            · exact Or.inr h4
          rcases h24 with rfl | rfl
          · obtain ⟨R, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
            have hA : mixedPosition (R + 1) s = 2 ::ₘ mixedPosition R s := mixed_two R s
            have hd12 : d = 1 ∨ d = 2 := by have := hd.1; have := hd.2.1; omega
            rw [fixed_successor hfixed, hA]
            rcases hd12 with rfl | rfl
            · rw [successor_cons_small _ (by decide : 1 < 2), adjoin_cons]
              have heb := even_adjoin (mixed_even R s) hn
              rw [one_even_board heb.1 heb.2]
              split_ifs <;> decide
            · simp only [successor, Multiset.erase_cons_head, Nat.sub_self, if_true,
                Multiset.add_zero]
              by_cases hR : 0 < R
              · have hzero := (mixed_zero (s := s) hR hn).mpr
                  (by omega : (R + n / 2) % 2 = 0)
                change fixedSequence (mixedPosition R s) n ≠ 3
                rw [hzero]; decide
              · have hR0 : R = 0 := by omega
                subst R
                obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
                have hn4 : n % 4 = 0 := by omega
                by_cases ht : t = 0
                · subst t
                  by_cases hn0 : n = 0
                  · subst n
                    have hpure : mixedPosition 0 (0 + 1) = ({4} : Position) := by simp [mixedPosition]
                    change fixedSequence (mixedPosition 0 1) 0 ≠ 3
                    simp only [fixedSequence, adjoinHeap, if_true, hpure]
                    rw [singleton_grundy 4 (by decide)]
                    decide
                  · have hopt : grundy (adjoinHeap (mixedPosition 0 1) n) ≠ 3 := by
                      have hpure : mixedPosition 0 1 = ({4} : Position) := by simp [mixedPosition]
                      have hleg : legal (adjoinHeap (mixedPosition 0 1) n) 4 2 := by
                        rw [hpure]
                        simp only [adjoinHeap, if_neg hn0, legal,
                          Multiset.erase_cons_tail_of_mem (show 4 ∈ ({4} : Position) by simp)]
                        refine ⟨by decide, by decide, ?_⟩
                        intro x hx
                        have hx' : x = n := by simpa using hx
                        rw [hx']; exact Nat.dvd_of_mod_eq_zero hn
                      have hmem : 4 ∈ adjoinHeap (mixedPosition 0 1) n := by simp [adjoinHeap, hn0, hpure]
                      have hsucc : successor (adjoinHeap (mixedPosition 0 1) n) 4 2 =
                          adjoinHeap ({2} : Position) n := by
                        rw [fixed_successor (by rw [hpure]; simp), hpure]
                        congr 1
                      intro hbad
                      apply grundy_not_follower (adjoinHeap (mixedPosition 0 1) n)
                      refine Finset.mem_image.mpr ⟨_, successor_is_move hmem hleg, ?_⟩
                      rw [hsucc]
                      exact (pair_two_multiple_four (by omega) (Nat.dvd_of_mod_eq_zero hn4)).trans hbad.symm
                    exact hopt
                · have htpos : 0 < t := by omega
                  have hsmall := ih t (by omega) htpos 1 n (by decide)
                  have hvalue : fixedSequence (mixedPosition 1 t) n = 3 := by
                    rw [hsmall]
                    simp [mixedFormula, hn4, show (1 + n / 2) % 2 = 1 by omega]
                  have hpure : mixedPosition 0 (t + 1) = 4 ::ₘ mixedPosition 0 t := mixed_four 0 t
                  have hmem : 4 ∈ adjoinHeap (mixedPosition 0 (t + 1)) n := by
                    rw [hpure, adjoin_cons]; simp
                  have hleg : legal (adjoinHeap (mixedPosition 0 (t + 1)) n) 4 2 := by
                    rw [hpure, adjoin_cons]
                    refine ⟨by decide, by decide, ?_⟩
                    simp only [Multiset.erase_cons_head]
                    exact (even_adjoin (mixed_even 0 t) hn).2
                  have hsucc : successor (adjoinHeap (mixedPosition 0 (t + 1)) n) 4 2 =
                      adjoinHeap (mixedPosition 1 t) n := by
                    rw [fixed_successor (by rw [hpure]; simp), hpure,
                      successor_cons_small _ (by decide : 2 < 4)]
                    congr 1
                  intro hbad
                  apply grundy_not_follower (adjoinHeap (mixedPosition 0 (t + 1)) n)
                  refine Finset.mem_image.mpr ⟨_, successor_is_move hmem hleg, ?_⟩
                  rw [hsucc]
                  exact hvalue.trans hbad.symm
          · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
            have h2 : 2 ∈ adjoinHeap (mixedPosition r (t + 1)) n := by
              unfold adjoinHeap
              split_ifs <;> simp [mixed_mem_two (t + 1) hr]
            have h2rem : 2 ∈ (adjoinHeap (mixedPosition r (t + 1)) n).erase 4 :=
              (Multiset.mem_erase_of_ne (by decide : (2 : ℕ) ≠ 4)).mpr h2
            have hd2 := hd.2.2 2 h2rem
            have hd12 := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd2
            rw [fixed_successor hfixed, mixed_four]
            rcases hd12 with rfl | rfl
            · rw [successor_cons_small _ (by decide : 1 < 4), adjoin_cons,
                mixed_three_value hr hn hwin]
              decide
            · rw [successor_cons_small _ (by decide : 2 < 4), ← mixed_two]
              have hzero := (mixed_zero (s := t) (by omega : 0 < r + 1) hn).mpr
                (by omega : (r + 1 + n / 2) % 2 = 0)
              change fixedSequence (mixedPosition (r + 1) t) n ≠ 3
              rw [hzero]; decide
        · subst h
          have h2 : 2 ∈ (adjoinHeap (mixedPosition r s) n).erase n := by
            simpa [adjoinHeap, hn0] using mixed_mem_two s hr
          have hd2 := hd.2.2 2 h2
          have hd12 := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd2
          rw [varying_successor _ hn0]
          rcases hd12 with rfl | rfl
          · have hv := mixed_odd_formula hr hs (n - 1) (by omega)
            change fixedSequence (mixedPosition r s) (n - 1) ≠ 3
            rw [hv]; split_ifs <;> decide
          · have hzero := (mixed_zero (s := s) hr (by omega : (n - 2) % 2 = 0)).mpr
              (by have := hd.2.1; omega : (r + (n - 2) / 2) % 2 = 0)
            change fixedSequence (mixedPosition r s) (n - 2) ≠ 3
            rw [hzero]; decide
      · intro v hv
        exact Finset.mem_image.mp (follower_mem_of_lt _ (lt_of_lt_of_le hv hlow))
  intro r s n hr hs
  exact main s hs r n hr

end D5.S3.Combinatorics.Games.DivisorNimGrundy
