/- GID: D5/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankTiling
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankTiling
   mirror-E: none(waiver:disjoint-block-construction)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Disjoint copies preserve forbidden cycles and bound the independence number. -/

import D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankDefs
import Mathlib.Combinatorics.SimpleGraph.Clique

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PhylogeneticRank

open SimpleGraph

/-- Fill complete blocks with copies, leaving the last incomplete block edgeless. -/
theorem tile_graph {m : ℕ} (hm : 0 < m) (H : SimpleGraph (Fin m))
    (htri : H.CliqueFree 3)
    (hfour : ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      H.Adj a b → H.Adj b c → H.Adj c d → H.Adj d a → False)
    (n : ℕ) (hn : 3 * m ≤ n) :
    ∃ K : SimpleGraph (Fin n), K.CliqueFree 3 ∧
      (∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        K.Adj a b → K.Adj b c → K.Adj c d → K.Adj d a → False) ∧
      Kᶜ.Connected ∧ (∀ a b, Kᶜ.dist a b ≤ 2) ∧
      K.indepNum ≤ n / m * H.indepNum + m := by
  classical
  let f : Fin n → Fin m := fun x => ⟨x.val % m, Nat.mod_lt _ hm⟩
  let q : Fin n → ℕ := fun x => x.val / m
  let K : SimpleGraph (Fin n) := {
    Adj := fun x y => q x = q y ∧ q x < n / m ∧ H.Adj (f x) (f y)
    symm := ⟨by
      intro x y h
      exact ⟨h.1.symm, h.1 ▸ h.2.1, h.2.2.symm⟩⟩
    loopless := ⟨by intro x h; exact H.irrefl h.2.2⟩ }
  have hfinj : ∀ x y, q x = q y → f x = f y → x = y := by
    intro x y hq hf
    apply Fin.ext
    have hx := Nat.mod_add_div x.val m
    have hy := Nat.mod_add_div y.val m
    have hf' : x.val % m = y.val % m := congrArg Fin.val hf
    change x.val / m = y.val / m at hq
    rw [hq, hf'] at hx
    omega
  have hkadj : ∀ x y, K.Adj x y → H.Adj (f x) (f y) := fun _ _ h => h.2.2
  have htriK : K.CliqueFree 3 := by
    intro s hs
    apply htri (s.image f)
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      exact hkadj x y (hs.isClique hx hy (fun h => hab (congrArg f h)))
    · rw [Finset.card_image_iff.mpr]
      · exact hs.card_eq
      · intro x hx y hy hxy
        by_contra hne
        exact (hkadj x y (hs.isClique hx hy hne)).ne hxy
  have hfourK : ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      K.Adj a b → K.Adj b c → K.Adj c d → K.Adj d a → False := by
    intro a b c d hab hac had hbc hbd hcd eab ebc ecd eda
    have qab : q a = q b := eab.1
    have qbc : q b = q c := ebc.1
    have qcd : q c = q d := ecd.1
    apply hfour (f a) (f b) (f c) (f d)
    · exact fun h => hab (hfinj a b qab h)
    · exact fun h => hac (hfinj a c (qab.trans qbc) h)
    · exact fun h => had (hfinj a d (qab.trans (qbc.trans qcd)) h)
    · exact fun h => hbc (hfinj b c qbc h)
    · exact fun h => hbd (hfinj b d (qbc.trans qcd) h)
    · exact fun h => hcd (hfinj c d qcd h)
    · exact hkadj _ _ eab
    · exact hkadj _ _ ebc
    · exact hkadj _ _ ecd
    · exact hkadj _ _ eda
  have hwalk : ∀ a b : Fin n, ∃ p : Kᶜ.Walk a b, p.length = 2 := by
    intro a b
    let j : ℕ := if q a = 0 ∨ q b = 0 then
      if q a = 1 ∨ q b = 1 then 2 else 1 else 0
    have hj : j < 3 ∧ j ≠ q a ∧ j ≠ q b := by
      dsimp [j]
      split_ifs <;> omega
    let c : Fin n := ⟨j * m, by nlinarith [hj.1]⟩
    have hqc : q c = j := by
      dsimp [q, c]
      exact Nat.mul_div_cancel _ hm
    have eac : Kᶜ.Adj a c := by
      refine ⟨?_, ?_⟩
      · intro h; exact hj.2.1 (hqc.symm.trans (congrArg q h).symm)
      · intro h; exact hj.2.1 (hqc.symm.trans h.1.symm)
    have ecb : Kᶜ.Adj c b := by
      refine ⟨?_, ?_⟩
      · intro h; exact hj.2.2 (hqc.symm.trans (congrArg q h))
      · intro h; exact hj.2.2 (hqc.symm.trans h.1)
    exact ⟨eac.toWalk.append ecb.toWalk, by simp⟩
  have hconn : Kᶜ.Connected := by
    let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨p, _⟩ := hwalk a b
    exact ⟨p⟩
  have hdiam : ∀ a b, Kᶜ.dist a b ≤ 2 := by
    intro a b
    obtain ⟨p, hp⟩ := hwalk a b
    exact hp ▸ SimpleGraph.dist_le p
  have hindep : K.indepNum ≤ n / m * H.indepNum + m := by
    obtain ⟨s, hs⟩ := K.exists_isNIndepSet_indepNum
    have hqbound : ∀ x : Fin n, q x < n / m + 1 := by
      intro x
      dsimp [q]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right x.isLt.le)
    have hcard : s.card = ∑ i ∈ Finset.range (n / m + 1),
        (s.filter (fun x => q x = i)).card :=
      Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_range.mpr (hqbound x))
    have hfiber : ∀ i, (s.filter (fun x => q x = i)).card ≤ m := by
      intro i
      have hinj : Set.InjOn f (s.filter (fun x => q x = i)) := by
        intro x hx y hy hxy
        exact hfinj x y ((Finset.mem_filter.mp hx).2.trans
          (Finset.mem_filter.mp hy).2.symm) hxy
      have hc := Finset.card_image_iff.mpr hinj
      have hb := Finset.card_le_card (Finset.subset_univ
        ((s.filter (fun x => q x = i)).image f))
      simpa [hc, Fintype.card_fin] using hb
    have hfull : ∀ i < n / m, (s.filter (fun x => q x = i)).card ≤ H.indepNum := by
      intro i hi
      let u := s.filter (fun x => q x = i)
      have hinj : Set.InjOn f u := by
        intro x hx y hy hxy
        exact hfinj x y ((Finset.mem_filter.mp hx).2.trans
          (Finset.mem_filter.mp hy).2.symm) hxy
      have hu : H.IsIndepSet (u.image f) := by
        intro a ha b hb hab eab
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
        have hx' := Finset.mem_filter.mp hx
        have hy' := Finset.mem_filter.mp hy
        apply hs.isIndepSet hx'.1 hy'.1 (fun h => hab (congrArg f h))
        exact ⟨hx'.2.trans hy'.2.symm, hx'.2 ▸ hi, eab⟩
      simpa [Finset.card_image_iff.mpr hinj] using hu.card_le_indepNum
    rw [← hs.card_eq, hcard, Finset.sum_range_succ]
    have hsum : ∑ i ∈ Finset.range (n / m),
        (s.filter (fun x => q x = i)).card ≤ n / m * H.indepNum := by
      calc
        _ ≤ ∑ _i ∈ Finset.range (n / m), H.indepNum :=
          Finset.sum_le_sum (fun i hi => hfull i (Finset.mem_range.mp hi))
        _ = _ := by simp
    exact Nat.add_le_add hsum (hfiber _)
  exact ⟨K, htriK, hfourK, hconn, hdiam, hindep⟩

end D5.S3.Combinatorics.PhylogeneticRank
