/- GID: D5/S3/Combinatorics/Dice/EaslickPaddedCycles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Dice/EaslickPaddedCycles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.ChainOfFn]
   utility: none
   digest: Uniform simple cycles obtained by nested dice padding. -/

import D5.S3.Combinatorics.Dice.EaslickCycleSeeds
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange

/-! Uniform nested padding assembles all clone blocks into a single simple cycle. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Dice.EaslickPaddedCycles
open EaslickMinimalAdvantage EaslickCycleSeeds

private theorem closed_ofFn {α : Type} [Inhabited α] (R : α → α → Prop)
    (k : ℕ) (hk : 0 < k) (f : Fin k → α)
    (h : ∀ i : Fin k, R (f i) (f ⟨(i.val+1)%k, Nat.mod_lt _ hk⟩)) :
    (List.ofFn f ++ [(List.ofFn f).head!]).IsChain R := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hi' : i < k := by simpa using hi
  have hhead : (List.ofFn f).head! = f ⟨0,hk⟩ := by
    rw [List.head!_eq_getElem!]
    simp [hk]
  by_cases hnext : i+1 < k
  · simpa [List.getElem_append, hi', hnext, Nat.mod_eq_of_lt hnext] using h ⟨i,hi'⟩
  · have heq : i+1 = k := by omega
    simpa [List.getElem_append, hi', hnext, heq, hhead] using h ⟨i,hi'⟩

/-- Reading any cyclic seed edge includes the final return to the first vertex. -/
theorem cycle_edge_at (r k : ℕ) (c : List (List ℕ)) (hlen : c.length = k)
    (hchain : (c ++ [c.head!]).IsChain (Edge r)) (hk : 0 < k) (i : Fin k) :
    Edge r c[i.val]
      (getElem c ((i.val+1)%k) (by simpa only [hlen] using Nat.mod_lt (i.val+1) hk)) := by
  have hi : i.val < c.length := by omega
  have hm : (i.val+1)%k < c.length := by simpa [hlen] using Nat.mod_lt (i.val+1) hk
  have h := (List.isChain_iff_getElem.mp hchain) i.val (by simp; omega)
  by_cases hn : i.val+1 < k
  · simpa [List.getElem_append, hi, hlen, hn, Nat.mod_eq_of_lt hn] using h
  · have heq : i.val+1 = k := by omega
    have hh : c.head! = c[0] := by
      rw [List.head!_eq_getElem!, getElem!_pos c 0 (by omega)]
    simpa [List.getElem_append, hi, hlen, hn, heq, hh] using h

/-- An even simple seed cycle yields one longer simple cycle using every clone block. -/
theorem padded_cycle (r k t : ℕ) (hr : 3 ≤ r) (hk : 0 < k) (hke : k%2=0)
    (hcap : r+6 ≤ r+2*t) (hc : HasCycle r k) :
    HasCycle (r+2*t) (k*(t+1)) := by
  obtain ⟨c,hlen,hnd,hne,hchain⟩ := hc
  have hN : 0 < k*(t+1) := Nat.mul_pos hk (by omega)
  have hmod (a : Fin (k*(t+1))) : a.val%k < c.length := by
    simpa [hlen] using Nat.mod_lt a.val hk
  let f : Fin (k*(t+1)) → List ℕ := fun a =>
    padded r t (a.val/k) (decide (a.val%k%2=1)) (getElem c (a.val%k) (hmod a))
  have hvalid (a : Fin (k*(t+1))) : IsDie r (getElem c (a.val%k) (hmod a)) :=
    (cycle_edge_at r k c hlen hchain hk ⟨a.val%k, Nat.mod_lt _ hk⟩).1
  have hdiv (a : Fin (k*(t+1))) : a.val/k ≤ t := by
    have : a.val/k < t+1 := (Nat.div_lt_iff_lt_mul hk).mpr
      (by simpa only [Nat.mul_comm] using a.isLt)
    omega
  have hinj : Function.Injective f := by
    intro a b hab
    have ha := hvalid a
    have hb := hvalid b
    have he := padded_eq_imp r t (a.val/k) (b.val/k)
      (decide (a.val%k%2=1)) (decide (b.val%k%2=1)) _ _ ha.2.2 hb.2.2 hab
    have hm : a.val%k = b.val%k := (hnd.getElem_inj_iff).mp he.1
    have hd : a.val/k = b.val/k := he.2 (by rw [hm])
    apply Fin.ext
    calc
      a.val = a.val%k+k*(a.val/k) := (Nat.mod_add_div _ _).symm
      _ = b.val%k+k*(b.val/k) := by rw [hm,hd]
      _ = b.val := Nat.mod_add_div _ _
  have hedge (a : Fin (k*(t+1))) :
      Edge (r+2*t) (f a) (f ⟨(a.val+1)%(k*(t+1)),Nat.mod_lt _ hN⟩) := by
    let b : Fin (k*(t+1)) := ⟨(a.val+1)%(k*(t+1)),Nat.mod_lt _ hN⟩
    have hm : b.val%k = (a.val%k+1)%k := by
      dsimp [b]
      rw [Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right k (t+1))]
      simp [Nat.add_mod]
    have hp : decide (b.val%k%2=1) = !(decide (a.val%k%2=1)) := by
      rw [hm,Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hke)]
      by_cases ho : a.val%k%2=1
      · have hn : (a.val%k+1)%2 ≠ 1 := by omega
        simp [ho,hn]
      · have hn : (a.val%k+1)%2 = 1 := by omega
        simp [ho,hn]
    have ha := hvalid a
    have hb := hvalid b
    have hva := padded_isDie r r t (a.val/k) (decide (a.val%k%2=1)) (getElem c (a.val%k) (hmod a)) (hdiv a) ha.1 ha.2.1 ha.2.2 hcap
    have hvb := padded_isDie r r t (b.val/k) (decide (b.val%k%2=1)) (getElem c (b.val%k) (hmod b)) (hdiv b) hb.1 hb.2.1 hb.2.2 hcap
    apply (edge_iff (r+2*t) (by omega) _ _ hva hvb).mpr
    change winCount
      (padded r t (a.val/k) (decide (a.val%k%2=1)) (getElem c (a.val%k) (hmod a)))
      (padded r t (b.val/k) (decide (b.val%k%2=1)) (getElem c (b.val%k) (hmod b))) = _
    rw [hp, padded_winCount r t (a.val/k) (b.val/k) _ _ _ (hdiv a) (hdiv b) ha.2.2 hb.2.2]
    have hs := cycle_edge_at r k c hlen hchain hk ⟨a.val%k,Nat.mod_lt _ hk⟩
    have hs' : winCount (getElem c (a.val%k) (hmod a)) (getElem c (b.val%k) (hmod b)) = threshold r := by
      have hcidx : getElem c (b.val%k) (hmod b) =
          getElem c ((a.val%k+1)%k) (by simpa only [hlen] using Nat.mod_lt (a.val%k+1) hk) :=
        getElem_congr rfl hm (hmod b)
      rw [hcidx]
      exact (edge_iff r hr _ _ hs.1 hs.2.1).mp hs
    rw [hs',ha.1,hb.1,threshold_padding]
    ring
  refine ⟨List.ofFn f, List.length_ofFn, List.nodup_ofFn.mpr hinj, ?_, ?_⟩
  · intro hz
    have := congrArg List.length hz
    simp at this
    omega
  · exact closed_ofFn (Edge (r+2*t)) _ hN f hedge

/-- Every number of faces above six admits a simple cycle longer than its face count. -/
theorem longer_cycle (n : ℕ) (hn : 7 ≤ n) : ∃ k, n < k ∧ HasCycle n k := by
  have hseed := finite_cycle_witnesses
  by_cases hsmall : n ≤ 11
  · interval_cases n
    · exact ⟨14, by decide, hseed.2.1⟩
    · exact ⟨29, by decide, hseed.2.2.1⟩
    · exact ⟨10, by decide, hseed.2.2.2.1⟩
    · exact ⟨110, by decide, hseed.2.2.2.2.1⟩
    · exact ⟨14, by decide, hseed.2.2.2.2.2⟩
  · rcases Nat.even_or_odd n with he | ho
    · obtain ⟨q,hq⟩ := he
      have hnq : n = 6+2*(q-3) := by omega
      refine ⟨6*((q-3)+1), ?_, ?_⟩
      · omega
      · rw [hnq]
        exact padded_cycle 6 6 (q-3) (by decide) (by decide) (by decide)
          (by omega) hseed.1
    · obtain ⟨q,hq⟩ := ho
      have hnq : n = 7+2*(q-3) := by omega
      refine ⟨14*((q-3)+1), ?_, ?_⟩
      · omega
      · rw [hnq]
        exact padded_cycle 7 14 (q-3) (by decide) (by decide) (by decide)
          (by omega) hseed.2.1

/-- The global maximum cannot equal the face count at any parameter above six. -/
theorem not_S_above_six (n : ℕ) (hn : 7 ≤ n) : ¬ S n := by
  obtain ⟨k,hk,hc⟩ := longer_cycle n hn
  exact fun h => h.2 k hk hc

end D5.S3.Combinatorics.Dice.EaslickPaddedCycles
