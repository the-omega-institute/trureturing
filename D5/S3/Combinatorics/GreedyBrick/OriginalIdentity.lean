/- GID: D5/S3/Combinatorics/GreedyBrick/OriginalIdentity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GreedyBrick/OriginalIdentity
   mirror-E: none(waiver:unbounded-literal-row-births)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Intervals]
   utility: none
   digest: Literal row births satisfy the all-index greedy-brick composition identity. -/

import D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GreedyBrick.OriginalIdentity
open SuccessorBand EventRealization RestBlock LiteralRestTrace
open D5.S3.ArithSums.GreedyBrickCapacityTotality

/-- Positive indices use the proved least literal row birth. The zero value is unused. -/
noncomputable def a (m : ℕ) : ℕ := if hm : 1 ≤ m then birth m hm else 0

/-- Every positive literal row birth satisfies the original self-composition identity. -/
theorem result (m : ℕ) (hm : 1 ≤ m) : a (a m) = a m * (a m + 3) / 2 - m := by
  have restPrefix (s : RestState) (d : ℕ) (hd : d < firstZeroBin s.capacity) :
      (placeBricks s.endpoint s.capacity.reverse d).length = s.capacity.length := by
    have pass (n : ℕ) (us ds : List ℕ)
        (hu : ∀ c ∈ us, c < n) (hf : (transfer n ds).2 = false) :
        transfer n (us ++ ds) = (us ++ (transfer n ds).1, false) := by
      induction us with
      | nil => apply Prod.ext <;> simp [hf]
      | cons c us ih =>
        have hc : ¬ n ≤ c := by have := hu c (by simp); omega
        have ht := ih (fun d hd => hu d (by simp [hd]))
        simp [transfer, hc, ht]
    have relay : ∀ (cs : List ℕ) (N a : ℕ) (lower : List ℕ) (d : ℕ),
        0 < a → (∀ c ∈ cs, c ≤ N) → d < firstZeroBin cs →
        (placeBricks N (cs.reverse ++ (N + a) :: lower) d).length =
          cs.length + 1 + lower.length := by
      intro cs
      induction cs with
      | nil =>
        intro N a lower d ha hb hd
        have : d = 0 := by simp [firstZeroBin] at hd; omega
        subst d
        simp [placeBricks, Nat.add_comm]
      | cons c cs ih =>
        intro N a lower d ha hb hd
        cases d with
        | zero => simp [placeBricks, Nat.add_comm, Nat.add_left_comm]
        | succ d =>
          have hc := hb c (by simp)
          have hz : c ≠ 0 := by
            intro hz
            simp [firstZeroBin, hz] at hd
          have hds : d < firstZeroBin cs := by simpa [firstZeroBin, hz] using hd
          have hn : ¬ N + 1 ≤ c := by omega
          have he : N + 1 ≤ N + a := by omega
          have hsub : N + a - (N + 1) = a - 1 := by omega
          have hbase : transfer (N + 1) (c :: (N + a) :: lower) =
              ((c + (N + 1)) :: (a - 1) :: lower, false) := by
            simp [transfer, hn, he, hsub]
          have hp := pass (N + 1) cs.reverse (c :: (N + a) :: lower)
            (by intro x hx; have := hb x (by simp only [List.mem_reverse] at hx; simp [hx]); omega)
            (by rw [hbase])
          have hs : step (N + 1) (cs.reverse ++ c :: (N + a) :: lower) =
              cs.reverse ++ (c + (N + 1)) :: (a - 1) :: lower := by
            unfold step
            rw [hp, hbase]
            simp
          have hi := ih (N + 1) c ((a - 1) :: lower) d (by omega)
            (by intro x hx; have := hb x (by simp [hx]); omega) hds
          simp only [placeBricks, List.reverse_cons, List.append_assoc,
            List.singleton_append, List.length_cons]
          rw [hs]
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hi
    cases hcs : s.capacity with
    | nil =>
      have : d = 0 := by simp [hcs, firstZeroBin] at hd; omega
      subst d
      simp [placeBricks]
    | cons c cs =>
      cases d with
      | zero => simp [placeBricks]
      | succ d =>
        have hb : ∀ x ∈ c :: cs, x ≤ s.endpoint := by simpa [hcs] using s.bounded
        have hc := hb c (by simp)
        have hz : c ≠ 0 := by intro hz; simp [hcs, firstZeroBin, hz] at hd
        have hds : d < firstZeroBin cs := by simpa [hcs, firstZeroBin, hz] using hd
        have hn : ¬ s.endpoint + 1 ≤ c := by omega
        have hbase : transfer (s.endpoint + 1) [c] =
            ([c + (s.endpoint + 1)], false) := by simp [transfer, hn]
        have hp := pass (s.endpoint + 1) cs.reverse [c]
          (by intro x hx; have := hb x (by simp only [List.mem_reverse] at hx; simp [hx]); omega)
          (by rw [hbase])
        have hs : step (s.endpoint + 1) (cs.reverse ++ [c]) =
            cs.reverse ++ [c + (s.endpoint + 1)] := by
          unfold step
          rw [hp, hbase]
          simp
        have hi := relay cs (s.endpoint + 1) c [] d (by omega)
          (by intro x hx; have := hb x (by simp [hx]); omega) hds
        simp only [placeBricks, List.reverse_cons, List.length_cons]
        rw [hs]
        simpa [Nat.add_comm] using hi
  have eventIdentity (T : RestTrace) (m : ℕ) (hm : 0 < m) :
      (events T).endpoint ((events T).birth ((events T).endpoint ((events T).birth m))) =
        (events T).endpoint ((events T).birth m) *
          ((events T).endpoint ((events T).birth m) + 3) / 2 - m := by
    classical
    let E := events T
    let b := fun h => E.endpoint (E.birth h)
    have L : EventLaws E := event_laws_realization T
    obtain ⟨S, I⟩ := successor_inverse_laws T
    have nmono : StrictMono E.endpoint := strictMono_nat_of_lt_succ fun t => by
      rw [L.endpoint_step]
      have := L.bin_pos (t + 1)
      omega
    have bm : ∀ h j, 0 < h → h < j → E.birth h < E.birth j := by
      intro h j hh hj
      apply (L.birth_cut j (by omega) _).mp
      rw [L.birth_height h hh]
      exact hj
    have bmono : ∀ h j, 0 < h → h ≤ j → b h ≤ b j := by
      intro h j hh hj
      rcases lt_or_eq_of_le hj with hj | rfl
      · exact (nmono (bm h j hh hj)).le
      · rfl
    have bp : ∀ h, 0 < h → 0 < b h := by
      intro h hh
      have init : E.endpoint 0 = 1 := T.initial_endpoint
      have hx := nmono.monotone (Nat.zero_le (E.birth h))
      dsimp [b]
      omega
    have cut (f : ℕ) (hf : E.Renewal f) :
        f < E.birth (b m) ↔ E.pred f < E.birth m := by
      have band := successor_band E L f hf
      change b (E.height (E.pred f)) ≤ E.height f ∧
        E.height f < b (E.height (E.pred f) + 1) at band
      have hp : 0 < E.height (E.pred f) :=
        lt_of_lt_of_le (L.bin_pos _) (L.bin_le_height _)
      rw [← L.birth_cut (b m) (bp m hm) f, ← L.birth_cut m hm (E.pred f)]
      constructor
      · intro h
        by_contra hn
        have hn' : m ≤ E.height (E.pred f) := by omega
        have hb := bmono m _ hm hn'
        omega
      · intro h
        have hb := bmono (E.height (E.pred f) + 1) m (by omega) (by omega)
        omega
    have sums (q : ℕ) : ∑ e ∈ Finset.range (q + 1), E.bin e = E.endpoint q := by
      induction q with
      | zero => simp [E, events, T.initial_endpoint, T.initial_bin]
      | succ q ih => rw [Finset.sum_range_succ, ih, L.endpoint_step]
    have before : ∑ e ∈ Finset.range (E.birth m), E.bin e + m = b m := by
      have h := sums (E.birth m)
      rw [Finset.sum_range_succ, L.birth_bin m hm] at h
      exact h
    let q := E.birth (b m)
    let renewals := (Finset.range (q + 1)).filter E.Renewal
    let births := (Finset.range (q + 1)).filter (fun f => ¬ E.Renewal f)
    have renewal_sum : ∑ f ∈ renewals, E.bin f =
        ∑ e ∈ Finset.range (E.birth m), E.bin e := by
      apply Finset.sum_bij (fun f _ => E.pred f)
      · intro f hf
        obtain ⟨hfr, hfn⟩ := Finset.mem_filter.mp hf
        have hfle : f ≤ q := by simpa using hfr
        have hne : f ≠ q := by
          intro heq
          subst f
          have hbin := L.birth_bin (b m) (bp m hm)
          exact hfn (by simp [q, hbin])
        exact Finset.mem_range.mpr ((cut f hfn).mp (by omega))
      · intro f hf g hg heq
        have hrf := (Finset.mem_filter.mp hf).2
        have hrg := (Finset.mem_filter.mp hg).2
        have hfI := I f hrf
        have hgI := I g hrg
        rw [heq] at hfI
        exact hfI.symm.trans hgI
      · intro e he
        have he' := Finset.mem_range.mp he
        have hs := S e
        have hc := (cut (successor T e) hs.2.2.1).mpr (by
          change (events T).pred (successor T e) < E.birth m
          rw [hs.2.2.2.1]
          exact he')
        refine ⟨successor T e, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs.2.2.1⟩,
          hs.2.2.2.1⟩
      · intro f hf
        exact (L.pred_bin f (Finset.mem_filter.mp hf).2).symm
    have birth_sum : ∑ f ∈ births, E.bin f =
        ∑ h ∈ Finset.range (b m), (h + 1) := by
      apply Finset.sum_bij (fun f _ => E.bin f - 1)
      · intro f hf
        obtain ⟨hfr, hfn⟩ := Finset.mem_filter.mp hf
        have hfle : f ≤ q := by simpa using hfr
        have hh := L.height_mono hfle
        have hq : E.height q = b m := L.birth_height _ (bp m hm)
        have hi := L.bin_le_height f
        have hip := L.bin_pos f
        apply Finset.mem_range.mpr
        omega
      · intro f hf g hg heq
        have hbf : f = E.birth (E.bin f) := by
          simpa [EventSequence.Renewal] using (Finset.mem_filter.mp hf).2
        have hbg : g = E.birth (E.bin g) := by
          simpa [EventSequence.Renewal] using (Finset.mem_filter.mp hg).2
        have hfp := L.bin_pos f
        have hgp := L.bin_pos g
        have hb : E.bin f = E.bin g := by omega
        exact hbf.trans ((congrArg E.birth hb).trans hbg.symm)
      · intro h hh
        have hh' := Finset.mem_range.mp hh
        have hc : E.birth (h + 1) ≤ q := by
          by_contra hn
          have hx := (L.birth_cut (h + 1) (by omega) q).mpr (by omega)
          rw [L.birth_height (b m) (bp m hm)] at hx
          omega
        have hi := L.birth_bin (h + 1) (by omega)
        refine ⟨E.birth (h + 1), ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_range.mpr (by omega), by simp [EventSequence.Renewal, hi]⟩
        · rw [hi]
          omega
      · intro f hf
        have := L.bin_pos f
        omega
    have split := Finset.sum_filter_add_sum_filter_not (Finset.range (q + 1)) E.Renewal E.bin
    change (∑ f ∈ renewals, E.bin f) + (∑ f ∈ births, E.bin f) = _ at split
    rw [renewal_sum, birth_sum, sums] at split
    have triangle : (∑ h ∈ Finset.range (b m), (h + 1)) * 2 = b m * (b m + 1) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.mul_one]
      have hx := Finset.sum_range_id_mul_two (b m)
      have hb := bp m hm
      have hpred : b m - 1 + 1 = b m := by omega
      nlinarith
    have twice : E.endpoint q * 2 + m * 2 = b m * (b m + 3) := by
      nlinarith [before, split, triangle]
    have div : b m * (b m + 3) / 2 = E.endpoint q + m := by
      rw [show b m * (b m + 3) = (E.endpoint q + m) * 2 by nlinarith,
        Nat.mul_div_cancel _ (by decide : 0 < 2)]
    change E.endpoint q = b m * (b m + 3) / 2 - m
    omega
  classical
  obtain ⟨T, hbin, hcouple, hclock, _, hrun, hcover⟩ := literal_trace_realization
  let E := events T
  have L : EventLaws E := event_laws_realization T
  have align (r : ℕ) (hr : 1 ≤ r) : a r = E.endpoint (E.birth r) := by
    have spec : 0 < a r ∧ (trajectory (a r)).length = r ∧
        (∀ K < a r, (trajectory K).length < r) ∧
        a r ≤ if r = 1 then 1 else 2 * r * (r - 1) - 1 := by
      simpa only [a, dif_pos hr, birth] using Nat.find_spec (birth_totality r hr)
    have atbirth : (trajectory (E.endpoint (E.birth r))).length = r := by
      change (trajectory (T.state (E.birth r)).endpoint).length = r
      rw [← hcouple (E.birth r), List.length_reverse]
      exact L.birth_height r (by omega)
    have earlier (K : ℕ) (hK : K < E.endpoint (E.birth r)) :
        (trajectory K).length < r := by
      by_cases hzero : K = 0
      · subst K
        simp [trajectory]
        omega
      · obtain ⟨e, d, hd, hKd, hrunK⟩ := hcover K (by omega)
        have he : e < E.birth r := by
          by_contra hn
          have hx := hclock.monotone (show E.birth r ≤ e by omega)
          change E.endpoint (E.birth r) ≤ (T.state e).endpoint at hx
          omega
        have hp := restPrefix (T.state e) d (by simpa only [hbin e] using hd)
        rw [hrunK, hp]
        exact (L.birth_cut r (by omega) e).mpr he
    rcases lt_trichotomy (a r) (E.endpoint (E.birth r)) with hlt | heq | hgt
    · have hx := earlier (a r) hlt
      omega
    · exact heq
    · have hx := spec.2.2.1 _ hgt
      omega
  have ampos : 1 ≤ a m := by
    have spec := Nat.find_spec (birth_totality m hm)
    have : 0 < a m := by simpa only [a, dif_pos hm, birth] using spec.1
    omega
  calc
    a (a m) = E.endpoint (E.birth (a m)) := align (a m) ampos
    _ = a m * (a m + 3) / 2 - m := by
      rw [align m hm]
      exact eventIdentity T m (by omega)

#print axioms result
end D5.S3.Combinatorics.GreedyBrick.OriginalIdentity
