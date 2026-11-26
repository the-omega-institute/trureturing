/- GID: D5/S3/Combinatorics/Geometry/Permutohedra/PrefixExchanges
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/Permutohedra/PrefixExchanges
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A batch of distinct adjacent exchanges changes exactly its selected prefix ranks. -/
import D5.S3.Combinatorics.Graph.PrefixHamming.ExactDimension

/-! Adjacent exchanges at proper ranks of a permutation. -/

namespace Rossi
open Finset D5.S3.Combinatorics.Graph.PrefixHamming

private def swapAt {n : ℕ} (d : Rank n) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨d.1.val - 1, by omega⟩ d.1

def exchange {n : ℕ} (p : Equiv.Perm (Fin n)) (d : Rank n) : Equiv.Perm (Fin n) :=
  (swapAt d).trans p

theorem exchange_prefix_ne_iff {n : ℕ} (p : Equiv.Perm (Fin n))
    (d : Rank n) (s : ℕ) :
    prefixSet (exchange p d) s ≠ prefixSet p s ↔ s = d.1.val := by
  let l : Fin n := ⟨d.1.val - 1, by omega⟩
  let r : Fin n := d.1
  have hd : 0 < r.val := d.2
  have hl : l.val + 1 = r.val := by dsimp [l, r] at *; omega
  have hpos (i : Fin n) :
      p i ∈ prefixSet (exchange p d) s ↔ (Equiv.swap l r i).val < s := by
    rw [mem_prefix]
    change ((Equiv.swap l r).symm (p.symm (p i))).val < s ↔ _
    simp
  have hbase (i : Fin n) : p i ∈ prefixSet p s ↔ i.val < s := by
    rw [mem_prefix, p.symm_apply_apply]
  constructor
  · intro h
    by_contra hs
    apply h
    ext x
    obtain ⟨i, rfl⟩ := p.surjective x
    rw [hpos, hbase]
    change s ≠ r.val at hs
    exact swap_mem (univ.filter fun j : Fin n => j.val < s) (a := l) (b := r)
      (by simp only [mem_filter, mem_univ, true_and]; omega) i
      |> fun h => by simpa only [mem_filter, mem_univ, true_and] using h
  · intro hs he
    change s = r.val at hs
    have ha : p l ∈ prefixSet p s := (hbase l).2 (by omega)
    have hb := (hpos l).1 (he ▸ ha)
    rw [Equiv.swap_apply_left] at hb
    omega

private theorem exchange_prefix_eq_iff {n : ℕ} (p : Equiv.Perm (Fin n))
    (d : Rank n) (s : ℕ) :
    prefixSet (exchange p d) s = prefixSet p s ↔ s ≠ d.1.val := by
  simpa only [not_ne_iff] using not_congr (exchange_prefix_ne_iff p d s)

def batch {n : ℕ} (p : Equiv.Perm (Fin n)) (ds : List (Rank n)) :=
  ds.foldl exchange p

theorem batch_prefix_ne_iff {n : ℕ} (p : Equiv.Perm (Fin n))
    (ds : List (Rank n)) (hd : ds.Nodup) (s : Rank n) :
    prefixSet (batch p ds) s.1.val ≠ prefixSet p s.1.val ↔ s ∈ ds := by
  induction ds generalizing p with
  | nil => simp [batch]
  | cons d ds ih =>
    obtain ⟨hdmem, hd⟩ := List.nodup_cons.mp hd
    change prefixSet (batch (exchange p d) ds) s.1.val ≠ prefixSet p s.1.val ↔ _
    by_cases h : s = d
    · subst s
      rw [show prefixSet (batch (exchange p d) ds) d.1.val =
          prefixSet (exchange p d) d.1.val from not_ne_iff.mp
            (fun hn => hdmem ((ih _ hd).1 hn))]
      simp [exchange_prefix_ne_iff]
    · have hv : s.1.val ≠ d.1.val := fun hv => h (Subtype.ext (Fin.ext hv))
      rw [← (exchange_prefix_eq_iff p d _).2 hv, ih _ hd]
      simp [h]

end Rossi
