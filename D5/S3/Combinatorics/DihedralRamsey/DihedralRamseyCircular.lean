/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyCircular
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyCircular
   mirror-E: none(waiver:cyclic-colour-constructions)
   anchors: []
   utility: none
   digest: Circular short-edge colourings exclude long alternating paths. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyPermutations
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyRanks
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyColoring
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyOrder
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyCircularDegree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs

/-- Short circular edges exclude an alternating path and leave few complementary neighbours. -/
theorem short_circular_colouring {a n r : ℕ} (ha : 2 * r + 1 < a) (hn : 2 * r < n) :
    ∃ G : SimpleGraph (Fin n),
      letI := Classical.propDecidable
      ¬DihedralEmbeddable (altPath a) G ∧
        (∀ x, Gᶜ.degree x ≤ n - 2 * r - 1) ∧
        ∀ b, 3 ≤ b → n < 2 * r + b → ¬DihedralEmbeddable (altPath b) Gᶜ := by
  classical
  let G : SimpleGraph (Fin n) := SimpleGraph.fromRel fun x y =>
    Nat.dist x.val y.val ≤ r ∨ n - Nat.dist x.val y.val ≤ r
  have hadj : ∀ x y, G.Adj x y ↔ x ≠ y ∧
      (Nat.dist x.val y.val ≤ r ∨ n - Nat.dist x.val y.val ≤ r) := by
    intro x y
    simp only [G, SimpleGraph.fromRel_adj, Nat.dist_comm y.val x.val, or_self]
  refine ⟨G, ?_, ?_, ?_⟩
  · rintro ⟨s, refl, ψ, hψ, hE⟩
    obtain ⟨q, hq, hdist⟩ := alternating_ranks a
    let j := a - 1 - a / 2
    have hj : j + 1 < a := by dsimp [j]; omega
    let x := q ⟨j, by omega⟩
    let y := q ⟨j + 1, hj⟩
    have hxy : Nat.dist x.val y.val = a / 2 := by
      rw [hq, hq, hdist j hj]
      dsimp [j]
      omega
    let u := dihedralPerm s refl x
    let v := dihedralPerm s refl y
    have hu := dihedralPerm_val s refl x
    have hv := dihedralPerm_val s refl y
    change u.val = _ at hu
    change v.val = _ at hv
    have harcs : r < Nat.dist u.val v.val ∧ r < a - Nat.dist u.val v.val := by
      have hx := x.isLt
      have hy := y.isLt
      have hs : s % a < a := Nat.mod_lt _ (by omega)
      unfold Nat.dist at hxy ⊢
      cases refl <;> simp only [Bool.false_eq_true, ↓reduceIte] at hu hv <;>
        split_ifs at hu hv <;> omega
    have he := hE x y (by
      apply (SimpleGraph.fromRel_adj _ _ _).mpr
      refine ⟨?_, Or.inl ⟨j, hj, hq _, hq _⟩⟩
      intro he
      have he' := congrArg Fin.val (q.injective he)
      dsimp [x, y] at he'
      omega)
    change G.Adj (ψ u) (ψ v) at he
    have hstretch := circular_order_stretch ψ hψ u v
    have hshort := (hadj _ _).mp he |>.2
    omega
  · intro x
    have hdegree : G.degree x = 2 * r := by
      convert short_circular_degree hn G hadj x using 1
      exact congrArg (fun I : Fintype (G.neighborSet x) => @SimpleGraph.degree _ G x I)
        (Subsingleton.elim _ _)
    have hcomp : Gᶜ.degree x = n - 1 - G.degree x := by
      rw [G.degree_compl, Fintype.card_fin]
    have hbound : Gᶜ.degree x ≤ n - 2 * r - 1 := by omega
    convert hbound using 1
    exact congrArg (fun I : Fintype (Gᶜ.neighborSet x) => @SimpleGraph.degree _ Gᶜ x I)
      (Subsingleton.elim _ _)
  · intro b hb hn' hemb
    obtain ⟨s, refl, ψ, hψ, hE⟩ := hemb
    obtain ⟨q, hq, hdist⟩ := alternating_ranks b
    have hinj := dihedralPerm_injective b s refl
    have hnear : ∀ x y : Fin b,
        (Nat.dist x.val y.val = 1 ∨ Nat.dist x.val y.val = b - 1) →
        Nat.dist (dihedralPerm s refl x).val (dihedralPerm s refl y).val = 1 ∨
          Nat.dist (dihedralPerm s refl x).val (dihedralPerm s refl y).val = b - 1 := by
      intro x y hxy
      exact (dihedralPerm_circular (by omega) s refl x y).mp hxy
    let next : Fin b → Fin b := fun p => ⟨(p.val + 1) % b, Nat.mod_lt _ (by omega)⟩
    let gap : Fin b → ℕ := fun p =>
      if p.val + 1 < b then (ψ (next p)).val - (ψ p).val
      else n + (ψ (next p)).val - (ψ p).val
    have hnext : ∀ p : Fin b, (p.val + 1 < b → (next p).val = p.val + 1) ∧
        (¬p.val + 1 < b → (next p).val = 0) := by
      intro p
      have hp := p.isLt
      constructor
      · intro h
        exact Nat.mod_eq_of_lt h
      · intro h
        have he : p.val + 1 = b := by omega
        dsimp [next]
        rw [he, Nat.mod_self]
    have stretch : ∀ x y : Fin b, x.val ≤ y.val →
        y.val - x.val + (ψ x).val ≤ (ψ y).val := by
      intro x y hxy
      have hmono : (ψ x).val ≤ (ψ y).val := hψ.monotone hxy
      have h := (circular_order_stretch ψ hψ x y).1
      rw [Nat.dist_eq_sub_of_le hxy, Nat.dist_eq_sub_of_le hmono] at h
      omega
    let zero : Fin b := ⟨0, by omega⟩
    let last : Fin b := ⟨b - 1, by omega⟩
    have budget : ∀ p t : Fin b, p.val < t.val → r + 1 ≤ gap p →
        r + 1 ≤ gap t → 2 * r + b ≤ n := by
      intro p t hpt hp ht
      have hpl := p.isLt
      have htl := t.isLt
      have hp' : p.val + 1 < b := by omega
      have hnp := (hnext p).1 hp'
      have h₁ := stretch zero p (by dsimp [zero]; omega)
      have h₂ := stretch (next p) t (by omega)
      have hl := (ψ last).isLt
      have htl' := (ψ t).isLt
      have hz : zero.val = 0 := rfl
      have hlv : last.val = b - 1 := rfl
      dsimp [gap] at hp ht
      rw [if_pos hp'] at hp
      by_cases ht' : t.val + 1 < b
      · have hnt := (hnext t).1 ht'
        have h₃ := stretch (next t) last (by dsimp [last]; omega)
        rw [if_pos ht'] at ht
        omega
      · have hnt := (hnext t).2 ht'
        have hnz : next t = zero := Fin.ext hnt
        rw [if_neg ht', hnz] at ht
        omega
    have getgap : ∀ u v : Fin b, u ≠ v →
        (Nat.dist u.val v.val = 1 ∨ Nat.dist u.val v.val = b - 1) →
        r + 1 ≤ Nat.dist (ψ u).val (ψ v).val →
        r + 1 ≤ n - Nat.dist (ψ u).val (ψ v).val →
        ∃ p : Fin b, ((u = p ∧ v = next p) ∨ (v = p ∧ u = next p)) ∧
          r + 1 ≤ gap p := by
      intro u v hne hnear hd hc
      have hu := u.isLt
      have hv := v.isLt
      rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with huv | hvu
      · have hψuv := hψ huv
        have hnuv : Nat.dist u.val v.val = v.val - u.val :=
          Nat.dist_eq_sub_of_le huv.le
        have hnud : Nat.dist (ψ u).val (ψ v).val = (ψ v).val - (ψ u).val :=
          Nat.dist_eq_sub_of_le hψuv.le
        rcases hnear with hnear | hnear
        · have hp : u.val + 1 < b := by omega
          have hnextu : next u = v := Fin.ext (by have := (hnext u).1 hp; omega)
          refine ⟨u, Or.inl ⟨rfl, hnextu.symm⟩, ?_⟩
          dsimp [gap]
          rw [if_pos hp, hnextu]
          omega
        · have hp : ¬v.val + 1 < b := by omega
          have hnextv : next v = u := Fin.ext (by have := (hnext v).2 hp; omega)
          refine ⟨v, Or.inr ⟨rfl, hnextv.symm⟩, ?_⟩
          dsimp [gap]
          rw [if_neg hp, hnextv]
          have hbound := (ψ v).isLt
          omega
      · have hψvu := hψ hvu
        have hnuv : Nat.dist u.val v.val = u.val - v.val := by
          rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hvu.le]
        have hnud : Nat.dist (ψ u).val (ψ v).val = (ψ u).val - (ψ v).val := by
          rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hψvu.le]
        rcases hnear with hnear | hnear
        · have hp : v.val + 1 < b := by omega
          have hnextv : next v = u := Fin.ext (by have := (hnext v).1 hp; omega)
          refine ⟨v, Or.inr ⟨rfl, hnextv.symm⟩, ?_⟩
          dsimp [gap]
          rw [if_pos hp, hnextv]
          omega
        · have hp : ¬u.val + 1 < b := by omega
          have hnextu : next u = v := Fin.ext (by have := (hnext u).2 hp; omega)
          refine ⟨u, Or.inl ⟨rfl, hnextu.symm⟩, ?_⟩
          dsimp [gap]
          rw [if_neg hp, hnextu]
          have hbound := (ψ u).isLt
          omega
    have blue : ∀ x y : Fin b, (altPath b).Adj x y →
        r + 1 ≤ Nat.dist (ψ (dihedralPerm s refl x)).val
          (ψ (dihedralPerm s refl y)).val ∧
        r + 1 ≤ n - Nat.dist (ψ (dihedralPerm s refl x)).val
          (ψ (dihedralPerm s refl y)).val := by
      intro x y hxy
      have hedge := hE x y hxy
      rw [SimpleGraph.compl_adj, hadj] at hedge
      constructor <;> by_contra h
      · exact hedge.2 ⟨hedge.1, Or.inl (by omega)⟩
      · exact hedge.2 ⟨hedge.1, Or.inr (by omega)⟩
    let x₀ := q ⟨0, by omega⟩
    let x₁ := q ⟨1, by omega⟩
    let x₂ := q ⟨b - 2, by omega⟩
    let x₃ := q ⟨b - 1, by omega⟩
    have hfirst : (altPath b).Adj x₀ x₁ := by
      rw [altPath, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ⟨0, by omega, hq _, hq _⟩⟩
      intro he
      have he' := congrArg Fin.val (q.injective he)
      change 0 = 1 at he'
      omega
    have hlast : (altPath b).Adj x₂ x₃ := by
      rw [altPath, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ⟨b - 2, by omega, hq _, ?_⟩⟩
      · intro he
        have he' := congrArg Fin.val (q.injective he)
        change b - 2 = b - 1 at he'
        omega
      · rw [hq]
        change altVertex b (b - 1) = altVertex b (b - 2 + 1)
        congr 1
        omega
    have hnear₁ := hnear x₀ x₁ (Or.inr (by
      rw [hq, hq]
      change Nat.dist (altVertex b 0) (altVertex b 1) = b - 1
      simpa using hdist 0 (by omega)))
    have hnear₂ := hnear x₂ x₃ (Or.inl (by
      rw [hq, hq]
      change Nat.dist (altVertex b (b - 2)) (altVertex b (b - 1)) = 1
      have he : b - 1 = b - 2 + 1 := by omega
      rw [he, hdist (b - 2) (by omega)]
      omega))
    have hblue₁ := blue x₀ x₁ hfirst
    have hblue₂ := blue x₂ x₃ hlast
    obtain ⟨p, hp, hgp⟩ := getgap (dihedralPerm s refl x₀)
      (dihedralPerm s refl x₁) (fun he => hfirst.ne (hinj he))
      hnear₁ hblue₁.1 hblue₁.2
    obtain ⟨t, ht, hgt⟩ := getgap (dihedralPerm s refl x₂)
      (dihedralPerm s refl x₃) (fun he => hlast.ne (hinj he))
      hnear₂ hblue₂.1 hblue₂.2
    have hnot₂ : dihedralPerm s refl x₀ ≠ dihedralPerm s refl x₂ := by
      intro he
      have he' := congrArg Fin.val (q.injective (hinj he))
      change 0 = b - 2 at he'
      omega
    have hnot₃ : dihedralPerm s refl x₀ ≠ dihedralPerm s refl x₃ := by
      intro he
      have he' := congrArg Fin.val (q.injective (hinj he))
      change 0 = b - 1 at he'
      omega
    have hpt : p ≠ t := by
      intro he
      subst t
      rcases hp with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩ <;>
        rcases ht with ⟨h₃, h₄⟩ | ⟨h₄, h₃⟩
      · exact hnot₂ (h₁.trans h₃.symm)
      · exact hnot₃ (h₁.trans h₄.symm)
      · exact hnot₃ (h₁.trans h₄.symm)
      · exact hnot₂ (h₁.trans h₃.symm)
    rcases lt_or_gt_of_ne (fun he => hpt (Fin.ext he)) with hpt | htp
    · have := budget p t hpt hgp hgt
      omega
    · have := budget t p htp hgt hgp
      omega

end D5.S3.Combinatorics.DihedralRamsey
