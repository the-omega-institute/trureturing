/- GID: D5/S3/Factorization/RankThreeBlockAvoidance
   generality: G
   mirror-B: D5/B/S3/Factorization/RankThreeBlockAvoidance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transitive finite linear incidence partitions admit whole-block avoidance. -/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.Tactic

/-! Block avoidance for a finite transitive linear incidence geometry. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.RankThreeBlockAvoidance

/-- The two incidence counts used in the distinct-closure branch cannot hold
when there are at least two blocks and each original block has at least two
points. -/
theorem incidence_count_contradiction {b m d : ℕ}
    (hb : 2 ≤ b) (hm : 2 ≤ m)
    (hB : b * (d - 1) = m - 1)
    (hL : (b + m - 1) * (d - 1) = m - 1) :
    False := by
  have hd : 1 ≤ d := by
    by_contra h
    have : d = 0 := by omega
    subst d
    simp at hB
    omega
  have hbm : b + m - 1 = b + (m - 1) := by omega
  have hsum : b * (d - 1) + (m - 1) * (d - 1) = m - 1 := by
    calc
      b * (d - 1) + (m - 1) * (d - 1) =
          (b + (m - 1)) * (d - 1) := by rw [Nat.add_mul]
      _ = (b + m - 1) * (d - 1) := by rw [hbm]
      _ = m - 1 := hL
  have hzero : (m - 1) * (d - 1) = 0 := by omega
  have hm1 : m - 1 ≠ 0 := by omega
  have hdsubzero : d - 1 = 0 :=
    (Nat.mul_eq_zero.mp hzero).resolve_left hm1
  have hBzero : b * 0 = m - 1 := by simpa [hdsubzero] using hB
  omega


/-- In a point-transitive finite partition, suppose each block has at least two
points and is contained in its assigned closure. Distinct closures have at most
one common point, and not all closures coincide. Then every closure avoids a
whole original block. The hypotheses concern the incidence geometry, rather
than presumed counting equations. -/
theorem exists_block_disjoint_of_transitive_linear_closures
    {G P I : Type*} [Group G] [Fintype P] [Finite I]
    [DecidableEq I]
    [MulAction G P] [MulAction G I] [MulAction.IsPretransitive G P]
    (owner : P → I) (L : I → Finset P)
    (hsize : ∀ i, 2 ≤ (Finset.univ.filter (fun x => owner x = i)).card)
    (hcontain : ∀ x, x ∈ L (owner x))
    (howner : ∀ (g : G) x, owner (g • x) = g • owner x)
    (hline : ∀ (g : G) i x, g • x ∈ L (g • i) ↔ x ∈ L i)
    (hsep : ∀ i j, L i ≠ L j → ∀ x ∈ L i, ∀ y ∈ L i,
      x ∈ L j → y ∈ L j → x = y)
    (hnonconstant : ∃ i j, L i ≠ L j) :
    ∀ i, ∃ j, ∀ x, owner x = j → x ∉ L i := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  have hpoint : ∀ i, ∃ x, owner x = i := by
    intro i
    have hpos : 0 < (Finset.univ.filter (fun x => owner x = i)).card :=
      lt_of_lt_of_le (by decide : 0 < 2) (hsize i)
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    exact ⟨x, (Finset.mem_filter.mp hx).2⟩
  have htrans : ∀ i j : I, ∃ g : G, g • i = j := by
    intro i j
    obtain ⟨x, hx⟩ := hpoint i
    obtain ⟨y, hy⟩ := hpoint j
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    refine ⟨g, ?_⟩
    calc
      g • i = g • owner x := by rw [hx]
      _ = owner (g • x) := (howner g x).symm
      _ = j := by rw [hg, hy]
  intro i
  by_contra hbad
  push Not at hbad
  have hmeet : ∀ a j, ∃ x, owner x = j ∧ x ∈ L a := by
    intro a j
    obtain ⟨g, hg⟩ := htrans i a
    obtain ⟨x, hx, hxi⟩ := hbad (g⁻¹ • j)
    refine ⟨g • x, ?_, ?_⟩
    · rw [howner, hx, smul_inv_smul]
    · rw [← hg]
      exact (hline g i x).mpr hxi
  -- A repeated closure would give two different original blocks in its fiber.
  -- A different closure meets both, producing two distinct intersection points.
  have hinj : Function.Injective L := by
    intro j k heq
    obtain ⟨a, ha⟩ : ∃ a, L a ≠ L j := by
      obtain ⟨u, v, huv⟩ := hnonconstant
      by_cases hu : L u = L j
      · exact ⟨v, by intro hv; exact huv (hu.trans hv.symm)⟩
      · exact ⟨u, hu⟩
    obtain ⟨x, hx, hxa⟩ := hmeet a j
    obtain ⟨y, hy, hya⟩ := hmeet a k
    have hxj : x ∈ L j := by simpa [hx] using hcontain x
    have hyj : y ∈ L j := by simpa [heq, hy] using hcontain y
    have hxy := hsep a j ha x hxa y hya hxj hyj
    exact hx.symm.trans ((congrArg owner hxy).trans hy)
  have hblock : ∀ a j, a ≠ j →
      ((L a).filter (fun x => owner x = j)).card = 1 := by
    intro a j haj
    obtain ⟨x, hx, hxa⟩ := hmeet a j
    apply Finset.card_eq_one_iff_existsUnique.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨hxa, hx⟩, ?_⟩
    intro y hy
    obtain ⟨hya, hyj⟩ := Finset.mem_filter.mp hy
    exact hsep a j (fun h => haj (hinj h)) y hya x hxa
      (by simpa [hyj] using hcontain y) (by simpa [hx] using hcontain x)
  have hintersection : ∀ a j, a ≠ j →
      ((L a).filter (fun x => x ∈ L j)).card = 1 := by
    intro a j haj
    obtain ⟨x, hx, hxa⟩ := hmeet a j
    have hxj : x ∈ L j := by simpa [hx] using hcontain x
    apply Finset.card_eq_one_iff_existsUnique.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨hxa, hxj⟩, ?_⟩
    intro y hy
    exact hsep a j (fun h => haj (hinj h)) y
      (Finset.mem_filter.mp hy).1 x hxa (Finset.mem_filter.mp hy).2 hxj
  let degree := fun x => (Finset.univ.filter (fun j => x ∈ L j)).card
  have hdegree : ∀ x y, degree x = degree y := by
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    dsimp [degree]
    apply Finset.card_bij (fun j _ => g • j)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [← hg]
      exact (hline g j x).mpr hj
    · intro j _ k _ h
      exact MulAction.injective g h
    · intro j hj
      refine ⟨g⁻¹ • j, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have h := (hline g (g⁻¹ • j) x).mp
      apply h
      simpa [hg] using hj
  obtain ⟨p, hp⟩ := hpoint i
  let d := degree p
  let B := Finset.univ.filter (fun x => owner x = i)
  let b := B.card
  let m := Fintype.card I
  have hm : 2 ≤ m := by
    obtain ⟨u, v, huv⟩ := hnonconstant
    have hcard : 1 < (Finset.univ : Finset I).card :=
      Finset.one_lt_card.mpr ⟨u, Finset.mem_univ _, v, Finset.mem_univ _,
        fun h => huv (congrArg L h)⟩
    simpa only [Finset.card_univ] using Nat.succ_le_of_lt hcard
  have hb : 2 ≤ b := hsize i
  have herase : ∀ x ∈ L i,
      ((Finset.univ.erase i).filter (fun j => x ∈ L j)).card = d - 1 := by
    intro x hx
    have hfilter : (Finset.univ.erase i).filter (fun j => x ∈ L j) =
        (Finset.univ.filter (fun j => x ∈ L j)).erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
      tauto
    rw [hfilter, Finset.card_erase_of_mem (by simp [hx])]
    exact congrArg (fun n => n - 1) (hdegree x p)
  have hself : (L i).filter (fun x => owner x = i) = B := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, B]
    exact ⟨And.right, fun hx => ⟨by simpa [hx] using hcontain x, hx⟩⟩
  have hlength : (L i).card = b + m - 1 := by
    have hf := Finset.card_eq_sum_card_fiberwise
      (s := L i) (t := (Finset.univ : Finset I)) (f := owner) (by simp)
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset I)
      (fun j => ((L i).filter (fun x => owner x = j)).card) (Finset.mem_univ i)
    have hother : ∑ j ∈ (Finset.univ.erase i),
        ((L i).filter (fun x => owner x = j)).card = m - 1 := by
      calc
        _ = ∑ _j ∈ (Finset.univ.erase i), 1 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hblock i j (Finset.mem_erase.mp hj).1.symm
        _ = m - 1 := by simp [m]
    rw [hother, hself] at hsplit
    dsimp [b] at ⊢
    omega
  have countB : b * (d - 1) = m - 1 := by
    have hc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun x j => x ∈ L j) (s := B) (t := Finset.univ.erase i)
    have hleft : (∑ x ∈ B,
        ((Finset.univ.erase i).bipartiteAbove (fun x j => x ∈ L j) x).card) =
        b * (d - 1) := by
      calc
        _ = ∑ _x ∈ B, (d - 1) := by
          apply Finset.sum_congr rfl
          intro x hx
          apply herase
          have hxi := (Finset.mem_filter.mp hx).2
          simpa [hxi] using hcontain x
        _ = b * (d - 1) := by simp [b]
    have hright : (∑ j ∈ (Finset.univ.erase i),
        (B.bipartiteBelow (fun x j => x ∈ L j) j).card) = m - 1 := by
      calc
        _ = ∑ _j ∈ (Finset.univ.erase i), 1 := by
          apply Finset.sum_congr rfl
          intro j hj
          have heq : B.bipartiteBelow (fun x j => x ∈ L j) j =
              (L j).filter (fun x => owner x = i) := by
            ext x
            simp [Finset.bipartiteBelow, B, and_comm]
          rw [heq]
          exact hblock j i (Finset.mem_erase.mp hj).1
        _ = m - 1 := by simp [m]
    omega
  have countL : (b + m - 1) * (d - 1) = m - 1 := by
    have hc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun x j => x ∈ L j) (s := L i) (t := Finset.univ.erase i)
    have hleft : (∑ x ∈ L i,
        ((Finset.univ.erase i).bipartiteAbove (fun x j => x ∈ L j) x).card) =
        (b + m - 1) * (d - 1) := by
      calc
        _ = ∑ _x ∈ L i, (d - 1) := by
          apply Finset.sum_congr rfl
          exact herase
        _ = (b + m - 1) * (d - 1) := by simp [hlength]
    have hright : (∑ j ∈ (Finset.univ.erase i),
        ((L i).bipartiteBelow (fun x j => x ∈ L j) j).card) = m - 1 := by
      calc
        _ = ∑ _j ∈ (Finset.univ.erase i), 1 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hintersection i j (Finset.mem_erase.mp hj).1.symm
        _ = m - 1 := by simp [m]
    omega
  exact incidence_count_contradiction hb hm countB countL

end D5.S3.Factorization.RankThreeBlockAvoidance
