/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Equal
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Equal
   mirror-E: none(waiver:consumed-equality-schedule)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Native physical order with the ear before the first terminal when a equals s. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Physical
/-! Physical interval and prefix bounds for the stated family. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper
open SourceWidth PeriodicShortening RunFirstEarTransport
open private rank amplitude heads newHeads successor newSuccessor start length f g N source source_numeric
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Source
open private Checks equal_checks
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Arithmetic
open private block_data terminal_signs checks_strip range_end range_join finish
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Physical
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

set_option maxHeartbeats 2000000 in
private theorem equal (s : ℕ) (hs : 2 ≤ s) :
    ∃ sigma : List (Fin (rank s s)), sigma.map Fin.val = List.range (rank s s) ∧
      s - 1 ≤ rank s s ∧ OriginalOrder (rank s s) (amplitude s s) sigma ∧
      OriginalOrder (rank s s + 1) (2 * amplitude s s) (earWord (rank s s) sigma (s - 1)) := by
  let q : ℤ := 2 ^ s
  let r : ℤ := 2 ^ (s - 1)
  let F := heads q q
  let G := newHeads q q
  let b := fun j : Fin 4 => List.range' (start s j) (s - 1)
  let n := fun j : Fin 4 => start s j + length s s j - 1
  let bs := [(b 0, n 0), (b 1, n 1), (b 2, n 2), (b 3, n 3)]
  let bsn := [(b 0++[rank s s], n 0), (b 1, n 1), (b 2, n 2), (b 3, n 3)]
  have hq : 4 ≤ q := by
    simpa [q] using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) hs
  have hr : 2 * r = q := by
    dsimp [r, q]
    conv_rhs => rw [show s = s - 1 + 1 by omega, pow_succ]
    ring
  have bd (j : Fin 4) := block_data s s hs (by omega) j 0 (s - 1)
    (by fin_cases j <;> simp [length])
  have bp (j : Fin 4) :
      ((b j).map (f s s)).sum = (r - 1) * F j ∧
      ((b j).map (g s s)).sum = (r - 1) * G j ∧
      (∀ i ∈ b j, 0 ≤ f s s i) ∧ (∀ i ∈ b j, 0 ≤ g s s i) := by
    simpa only [Nat.add_zero, pow_zero, mul_one] using bd j
  have bm (j : Fin 4) : 2 * ((b j).map (f s s)).sum = (q - 2) * F j := by
    rw [(bp j).1];linear_combination F j * hr
  have gm (j : Fin 4) : 2 * ((b j).map (g s s)).sum = (q - 2) * G j := by
    rw [(bp j).2.1];linear_combination G j * hr
  have tab := source s s hs (by omega)
  have nm (j : Fin 4) :
      2 * f s s (n j) = successor F j - N s s ∧
      2 * g s s (n j) = newSuccessor q q j - (2 * N s s + 1) := tab.2.2.2.1 j
  have ear : g s s (rank s s) = F 0 := tab.2.2.2.2
  have gem : 2 * ((b 0++[rank s s]).map (g s s)).sum = (q - 2) * (2 * F 0) + 2 * F 0 := by
    simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ear]
    have hh := gm 0
    change 2 * ((b 0).map (g s s)).sum = (q - 2) * (2 * F 0) at hh
    omega
  have hN : N s s = q ^ 4 - 1 := by rw [(source_numeric s s).1];dsimp[q];ring
  have hhalf : 2 * (N s s/2) = N s s - 1 := by
    have heq : N s s = 2 * (r * q ^ 3 - 1) + 1 := by rw [hN];linear_combination -q ^ 3 * hr
    omega
  have hcap : 0 ≤ N s s/2 := by
    have hpow : 4 ≤ (2:ℤ) ^ rank s s := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (show 2 ≤ rank s s by dsimp[rank];omega)
    rw [←(source_numeric s s).2.1]
    dsimp [modulus];omega
  have cert := equal_checks q hq
  change Checks _ _ _ ∧ Checks _ _ _ at cert
  rw [←hN] at cert
  have ns (j : Fin 4) : f s s (n j) ≤ 0 ∧ g s s (n j) ≤ 0 :=
    terminal_signs s s hs (by omega) j
  have hold : InStrip (f s s) (N s s/2) 0 (blocksWord bs) := by
    apply checks_strip _ _ _ hcap
    · intro j hj i hi
      simp only [bs, List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl
      all_goals exact (bp _).2.2.1 i hi
    · intro j hj
      simp only [bs, List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl
      all_goals exact (ns _).1
    · simpa [bs, List.map_cons, List.map_nil, hhalf, bm, (nm 0).1, (nm 1).1, (nm 2).1, (nm 3).1, 
        successor] using cert.1
  have hnew : InStrip (g s s) (N s s) 0 (blocksWord bsn) := by
    apply checks_strip _ _ _ (by omega)
    · intro j hj i hi
      simp only [bsn, List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl
      · rcases List.mem_append.mp hi with hi|hi
        · exact (bp 0).2.2.2 i hi
        · have heq := List.mem_singleton.mp hi;subst i;rw [ear];exact (tab.1 0).le
      all_goals exact (bp _).2.2.2 i hi
    · intro j hj
      simp only [bsn, List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl
      all_goals exact (ns _).2
    · simpa only [bsn, List.map_cons, List.map_nil, gem, gm, (nm 0).2, (nm 1).2, (nm 2).2, (nm 3).2, 
        newSuccessor, F, G, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using cert.2
  have bend (j : Fin 4) : b j++[n j]=List.range' (start s j) s := by
    have hl : length s s j = s := by fin_cases j <;> rfl
    simpa only [b, n, hl, show start s j + (s - 1) = start s j + s - 1 by omega, 
      show s - 1 + 1 = s by omega] using range_end (start s j) (s - 1)
  have hw : blocksWord bs = List.range (rank s s) := by
    have hword : blocksWord bs = (b 0++[n 0])++(b 1++[n 1])++(b 2++[n 2])++(b 3++[n 3]) := by
      simp [blocksWord, bs, List.append_assoc]
    rw [hword, bend, bend, bend, bend]
    have h01 := range_join 0 s s
    have h012 := range_join 0 (2 * s) s
    have h0123 := range_join 0 (3 * s) s
    simp only [Nat.zero_add, show s + s = 2 * s by omega] at h01
    simp only [Nat.zero_add, show 2 * s + s = 3 * s by omega] at h012
    simp only [Nat.zero_add, show 3 * s + s = rank s s by dsimp[rank];omega] at h0123
    simpa [start, ←List.range_eq_range'] using
      (show List.range' 0 s++List.range' s s++List.range' (2 * s) s++List.range' (3 * s) s =
        List.range' 0 (rank s s) by rw [h01, h012, h0123])
  let pre := b 0
  let post := n 0::b 1++n 1::b 2++n 2::b 3++[n 3]
  have ho : blocksWord bs = pre++post := by simp [blocksWord, bs, pre, post]
  have hn : blocksWord bsn = pre++rank s s::post := by
    simp [blocksWord, bsn, pre, post, List.append_assoc]
  have hp : (pre++post).Perm (List.range (rank s s)) := by rw [←ho, hw]
  have hc : pre.length = s - 1 := by simp [pre, b]
  rw [ho] at hold
  rw [hn] at hnew
  obtain ⟨sigma, hvals, hcut, hold, hnew⟩ := finish s s hs (by omega) (s - 1) pre post hc hp hold hnew
  exact ⟨sigma, hvals.trans (ho.symm.trans hw), hcut, hold, hnew⟩
end D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper
