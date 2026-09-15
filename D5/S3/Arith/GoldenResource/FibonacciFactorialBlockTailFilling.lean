/- GID: D5/S3/Arith/GoldenResource/FibonacciFactorialBlockTailFilling
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/FibonacciFactorialBlockTailFilling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Factorial blocks realize exact rational tail filling while normalized capacities vanish at infinity. -/
import D5.S3.Arith.GoldenResource.RationalCapacityTailRealization
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas

set_option autoImplicit false
open scoped BigOperators Topology
open Filter

namespace D5.S3.Arith.GoldenResource.FibonacciFactorialBlockTailFilling

open D5.S3.Arith.GoldenResource.RationalCapacityTailRealization
open D5.S3.Analytic.WeightedCapacity.DyadicTailFilling

/-- The Fibonacci row used by this chapter, indexed so that its first values are 1 and 2. -/
def G (n : ℕ) : ℕ := Nat.fib (n + 2)

/-- A separated family of finite factorial-divisible index blocks. -/
def BlockSpec (I : ℕ → Finset ℕ) : Prop :=
  I 0 = ∅ ∧ (∀ j, 0 < j → (I j).card = j * j.factorial) ∧
  (∀ j, 0 < j → ∀ n ∈ I j, j.factorial ∣ G n) ∧
  (∀ j k, 0 < j → j < k → ∀ n ∈ I j, ∀ m ∈ I k, n < m)

/-- Capacity obtained by dividing the Fibonacci row by the factorial of its block. -/
noncomputable def blockCapacity (I : ℕ → Finset ℕ) (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, 0 < j ∧ n ∈ I j then G n / (Classical.choose h).factorial else 0

set_option maxHeartbeats 800000 in
/-- Separated factorial blocks fill all rational tails while their normalized capacities vanish. -/
theorem factorial_block_tail_filling :
    (∃ I : ℕ → Finset ℕ, BlockSpec I) ∧
    ∀ I : ℕ → Finset ℕ, BlockSpec I →
      FillsRationalTails G (blockCapacity I) ∧
      Filter.Tendsto (fun n => (blockCapacity I n : ℝ) / G n) Filter.atTop (nhds 0) ∧
      ¬ CofinalDivisibleCapacity G (blockCapacity I) := by
  classical
  have hG : ∀ n, 0 < G n := by
    intro n
    exact Nat.fib_pos.mpr (by omega)
  have hcof : ∀ d : ℕ, 0 < d → ∀ N : ℕ, ∃ n : ℕ, N < n ∧ d ∣ G n := by
    intro d hd N
    let : NeZero d := ⟨hd.ne'⟩
    let T : ZMod d × ZMod d → ZMod d × ZMod d := fun x => (x.2, x.1 + x.2)
    let f : ℕ × ℕ → ℕ × ℕ := fun x => (x.2, x.1 + x.2)
    let C : ℕ × ℕ → ZMod d × ZMod d := fun x => (x.1, x.2)
    have hi : Function.Injective T := by
      intro a b h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      dsimp [T] at h₁ h₂
      apply Prod.ext
      · exact add_right_cancel (h₁ ▸ h₂)
      · exact h₁
    have hc : Function.Semiconj C f T := by
      intro x
      simp [C, f, T]
    have hcast (n : ℕ) : (Nat.fib n : ZMod d) = (T^[n] (0, 1)).1 := by
      have h := congrArg Prod.fst (hc.iterate_right n (0, 1))
      simpa [Nat.fib, f, C] using h
    obtain ⟨p, hp, hreturn⟩ := hi.mem_periodicPts (0, 1)
    have hz : (Nat.fib p : ZMod d) = 0 := by
      rw [hcast, hreturn.eq]
    have hdvd : d ∣ Nat.fib p := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hbound : N + 3 ≤ (N + 3) * p := by
      simpa using Nat.mul_le_mul_left (N + 3) (Nat.succ_le_iff.mpr hp)
    refine ⟨(N + 3) * p - 2, by omega, ?_⟩
    unfold G
    rw [Nat.sub_add_cancel (by omega : 2 ≤ (N + 3) * p)]
    exact hdvd.trans (Nat.fib_dvd p ((N + 3) * p) (dvd_mul_left p (N + 3)))
  have hall : ∀ I : ℕ → Finset ℕ, BlockSpec I →
      FillsRationalTails G (blockCapacity I) ∧
      Tendsto (fun n => (blockCapacity I n : ℝ) / G n) atTop (nhds 0) ∧
      ¬ CofinalDivisibleCapacity G (blockCapacity I) := by
    intro I hI
    obtain ⟨hzero, hcard, hdiv, hsep⟩ := hI
    have hne (j : ℕ) (hj : 0 < j) : (I j).Nonempty := by
      apply Finset.card_pos.mp
      rw [hcard j hj]
      exact Nat.mul_pos hj (Nat.factorial_pos j)
    have hunique (j k n : ℕ) (hj : 0 < j) (hk : 0 < k)
        (hnj : n ∈ I j) (hnk : n ∈ I k) : j = k := by
      rcases lt_trichotomy j k with h | h | h
      · exact False.elim ((lt_irrefl n) (hsep j k hj h n hnj n hnk))
      · exact h
      · exact False.elim ((lt_irrefl n) (hsep k j hk h n hnk n hnj))
    have hcap (j n : ℕ) (hj : 0 < j) (hn : n ∈ I j) :
        blockCapacity I n = G n / j.factorial := by
      have hex : ∃ k, 0 < k ∧ n ∈ I k := ⟨j, hj, hn⟩
      have heq := hunique (Classical.choose hex) j n
        (Classical.choose_spec hex).1 hj (Classical.choose_spec hex).2 hn
      simp only [blockCapacity, dif_pos hex]
      rw [heq]
    have hratioQ (j n : ℕ) (hj : 0 < j) (hn : n ∈ I j) :
        (blockCapacity I n : ℚ) / G n = 1 / (j.factorial : ℚ) := by
      rw [hcap j n hj hn, Nat.cast_div_charZero (hdiv j hj n hn)]
      have hg : (G n : ℚ) ≠ 0 := by exact_mod_cast (hG n).ne'
      field_simp
    have hratio (j n : ℕ) (hj : 0 < j) (hn : n ∈ I j) :
        (blockCapacity I n : ℝ) / G n = 1 / (j.factorial : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_one] using
        congrArg (fun z : ℚ => (z : ℝ)) (hratioQ j n hj hn)
    have hindex : ∀ j n : ℕ, 0 < j → n ∈ I j → j ≤ n + 1 := by
      intro j
      induction j with
      | zero => omega
      | succ j ih =>
        intro n hj hn
        by_cases hj0 : j = 0
        · omega
        · obtain ⟨m, hm⟩ := hne j (Nat.pos_of_ne_zero hj0)
          have hmn := hsep j (j + 1) (Nat.pos_of_ne_zero hj0) (by omega) m hm n hn
          have hmi := ih m (Nat.pos_of_ne_zero hj0) hm
          omega
    have hfill : FillsRationalTails G (blockCapacity I) := by
      intro q hq N
      let a := q.num.toNat
      let d := q.den
      let j := N + a + d + 2
      have hj : 0 < j := by dsimp [j]; omega
      have hd : 0 < d := q.den_pos
      have hdj : d ≤ j := by dsimp [j]; omega
      have haj : a ≤ j := by dsimp [j]; omega
      have hdF : d ∣ j.factorial := Nat.dvd_factorial hd hdj
      let m := a * (j.factorial / d)
      have hm : m ≤ (I j).card := by
        rw [hcard j hj]
        exact (Nat.mul_le_mul_left a (Nat.div_le_self _ _)).trans
          (Nat.mul_le_mul_right _ haj)
      obtain ⟨T, hTI, hTm⟩ := Finset.exists_subset_card_eq hm
      have hTN (n : ℕ) (hn : n ∈ T) : N < n := by
        have hi := hindex j n hj (hTI hn)
        dsimp [j] at hi
        omega
      have hab : (a : ℚ) / d = q := by
        dsimp [a, d]
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)]
        exact q.num_div_den
      have hmq : (m : ℚ) / j.factorial = q := by
        dsimp [m]
        rw [Nat.cast_mul, Nat.cast_div_charZero hdF]
        have hf : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
        calc
          _ = (a : ℚ) / d := by field_simp
          _ = q := hab
      let x : X (blockCapacity I) := fun n => if n ∈ T then
        ⟨blockCapacity I n, Nat.lt_succ_self _⟩ else ⟨0, Nat.zero_lt_succ _⟩
      have hs : Function.support (fun n => (x n : ℕ)) ⊆ (T : Set ℕ) := by
        intro n hn
        by_contra h
        exact hn (by simp [x, show n ∉ T from h])
      let u : B (blockCapacity I) := ⟨x, T.finite_toSet.subset hs⟩
      refine ⟨u, ?_, ?_⟩
      · intro n hn
        have hnt : n ∉ T := fun ht => (Nat.not_lt_of_ge hn) (hTN n ht)
        simp [u, x, hnt]
      · unfold weightedRead
        calc
          _ = ∑ n ∈ T, ((x n : ℕ) : ℚ) / G n := by
            apply Finset.sum_subset
            · intro n hn
              exact hs (by simpa using hn)
            · intro n _ hn
              have hz : (x n : ℕ) = 0 := by simpa [u] using hn
              simp [u, hz]
          _ = ∑ _n ∈ T, (1 / (j.factorial : ℚ)) := by
            apply Finset.sum_congr rfl
            intro n hn
            simpa [x, hn] using hratioQ j n hj (hTI hn)
          _ = q := by
            simpa only [Finset.sum_const, nsmul_eq_mul, hTm, mul_one_div] using hmq
    have hsmall : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ n : ℕ, M < n →
        (blockCapacity I n : ℝ) / G n < ε := by
      intro ε hε
      obtain ⟨J, hJ⟩ := exists_nat_gt (1 / ε)
      let S := (Finset.range (J + 1)).biUnion I
      refine ⟨S.sup id, ?_⟩
      intro n hn
      by_cases hex : ∃ j, 0 < j ∧ n ∈ I j
      · obtain ⟨j, hj, hnj⟩ := hex
        have hJj : J < j := by
          by_contra h
          have hmem : n ∈ S := Finset.mem_biUnion.mpr
            ⟨j, Finset.mem_range.mpr (by omega), hnj⟩
          have hle : n ≤ S.sup id := Finset.le_sup (f := id) hmem
          omega
        rw [hratio j n hj hnj]
        have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
        have hbound : (J : ℝ) ≤ j.factorial := by
          exact_mod_cast (hJj.le.trans (Nat.self_le_factorial j))
        apply (div_lt_iff₀ hf).mpr
        have hprod := (div_lt_iff₀ hε).mp hJ
        nlinarith
      · simp [blockCapacity, dif_neg hex, hε]
    have hlimit : Tendsto (fun n => (blockCapacity I n : ℝ) / G n) atTop (nhds 0) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨M, hM⟩ := hsmall ε hε
      refine ⟨M + 1, ?_⟩
      intro n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      exact hM n (by omega)
    have hnot : ¬ CofinalDivisibleCapacity G (blockCapacity I) := by
      rintro ⟨ε, hε, hc⟩
      obtain ⟨M, hM⟩ := hsmall ε hε
      obtain ⟨n, hn, _, hmass⟩ := hc 1 (by omega) M
      exact (not_le_of_gt (hM n hn)) hmass
    exact ⟨hfill, hlimit, hnot⟩
  refine ⟨?_, hall⟩
  have hblock : ∀ j M : ℕ, 0 < j → ∃ s : Finset ℕ,
      s.card = j * j.factorial ∧ ∀ n ∈ s, j.factorial ∣ G n ∧ M < n := by
    intro j M hj
    let S : Set ℕ := {n | M < n ∧ j.factorial ∣ G n}
    have hS : S.Infinite := by
      intro hf
      obtain ⟨n, hn, hd⟩ := hcof j.factorial (Nat.factorial_pos j)
        (max M (hf.toFinset.sup id))
      have hmem : n ∈ hf.toFinset := hf.mem_toFinset.mpr
        ⟨lt_of_le_of_lt (le_max_left _ _) hn, hd⟩
      have hle : n ≤ hf.toFinset.sup id := Finset.le_sup (f := id) hmem
      have hmax := le_max_right M (hf.toFinset.sup id)
      omega
    obtain ⟨s, hs, hcard⟩ := hS.exists_subset_card_eq (j * j.factorial)
    exact ⟨s, hcard, fun n hn => ⟨(hs hn).2, (hs hn).1⟩⟩
  let I : ℕ → Finset ℕ := Nat.rec ∅ (fun j prev =>
    Classical.choose (hblock (j + 1) (prev.sup id) (Nat.succ_pos j)))
  have hstep (j : ℕ) : (I (j + 1)).card = (j + 1) * (j + 1).factorial ∧
      ∀ n ∈ I (j + 1), (j + 1).factorial ∣ G n ∧ (I j).sup id < n := by
    exact Classical.choose_spec (hblock (j + 1) ((I j).sup id) (Nat.succ_pos j))
  have hne (j : ℕ) : (I (j + 1)).Nonempty := by
    apply Finset.card_pos.mp
    rw [(hstep j).1]
    exact Nat.mul_pos (Nat.succ_pos j) (Nat.factorial_pos _)
  have hmono : Monotone (fun j => (I j).sup id) := by
    apply monotone_nat_of_le_succ
    intro j
    obtain ⟨n, hn⟩ := hne j
    exact ((hstep j).2 n hn).2.le.trans (Finset.le_sup (f := id) hn)
  refine ⟨I, rfl, ?_, ?_, ?_⟩
  · intro j hj
    cases j with
    | zero => omega
    | succ j => exact (hstep j).1
  · intro j hj n hn
    cases j with
    | zero => omega
    | succ j => exact ((hstep j).2 n hn).1
  · intro j k hj hjk n hn m hm
    cases k with
    | zero => omega
    | succ k =>
      exact lt_of_le_of_lt
        ((Finset.le_sup (f := id) hn).trans (hmono (by omega : j ≤ k)))
        ((hstep k).2 m hm).2

end D5.S3.Arith.GoldenResource.FibonacciFactorialBlockTailFilling
