/- GID: D5/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/PointDeletedSteinerSwitch
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: A matching edge replaced by a four-edge path has one possible triangle. -/

import D5.S3.Combinatorics.Matroids.RankThreeSaturatedTopGap

/-! # The leave of a switch in a point-deleted Steiner packing -/

namespace D5.S3.Combinatorics.Matroids.PointDeletedSteinerSwitch

private def PathAdjacent {V : Type*} (p : Fin 5 → V) (x y : V) : Prop :=
  ∃ i j, p i = x ∧ p j = y ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val)

private def RemainingMatch {V : Type*} (p : Fin 5 → V) (m : V → V) (x y : V) : Prop :=
  x ≠ p 0 ∧ x ≠ p 4 ∧ y ≠ p 0 ∧ y ≠ p 4 ∧ m x = y

private def SwitchedLeave {V : Type*} (p : Fin 5 → V) (m : V → V) (x y : V) : Prop :=
  PathAdjacent p x y ∨ RemainingMatch p m x y

private theorem two_path_edges {V : Type*} {p : Fin 5 → V} {x y z : V}
    (injective : Function.Injective p) (xy : PathAdjacent p x y)
    (yz : PathAdjacent p y z) (distinct : x ≠ z) :
    ∃ i k : Fin 5, p i = x ∧ p k = z ∧ (i.val + 2 = k.val ∨ k.val + 2 = i.val) := by
  obtain ⟨i, j, hi, hj, step₁⟩ := xy
  obtain ⟨j', k, hj', hk, step₂⟩ := yz
  have eq := injective (hj.trans hj'.symm)
  subst j'
  have ne : i.val ≠ k.val := fun same => distinct (hi.symm.trans (Fin.ext same ▸ hk))
  exact ⟨i, k, hi, hk, by omega⟩

private theorem path_two_then_match {V : Type*} {p : Fin 5 → V} {m : V → V}
    (injective : Function.Injective p) (involutive : Function.Involutive m) {x y z : V}
    (xy : PathAdjacent p x y) (yz : PathAdjacent p y z) (zx : SwitchedLeave p m z x)
    (distinct : x ≠ z) : m (p 1) = p 3 := by
  obtain ⟨i, k, hi, hk, distance⟩ := two_path_edges injective xy yz distinct
  rcases zx with ⟨l, j, hl, hj, step⟩ | ⟨nz₀, nz₄, nx₀, nx₄, mate⟩
  · have eli := injective (hj.trans hi.symm)
    have elk := injective (hl.trans hk.symm)
    subst j
    subst l
    omega
  have internal (l : Fin 5) (n₀ : p l ≠ p 0) (n₄ : p l ≠ p 4) :
      1 ≤ l.val ∧ l.val ≤ 3 := by
    have h₀ : l.val ≠ 0 := fun eq => n₀ (congrArg p (Fin.ext eq))
    have h₄ : l.val ≠ 4 := fun eq => n₄ (congrArg p (Fin.ext eq))
    omega
  have il := internal i (by rw [hi]; exact nx₀) (by rw [hi]; exact nx₄)
  have kl := internal k (by rw [hk]; exact nz₀) (by rw [hk]; exact nz₄)
  rcases distance with lower | upper
  · have i1 : i = 1 := Fin.ext (by omega)
    have k3 : k = 3 := Fin.ext (by omega)
    rw [i1] at hi
    rw [k3] at hk
    rw [hi, hk]
    rw [← mate, involutive]
  · have i3 : i = 3 := Fin.ext (by omega)
    have k1 : k = 1 := Fin.ext (by omega)
    rw [i3] at hi
    rw [k1] at hk
    simpa only [hi, hk] using mate

private theorem matched_path_triangle {V : Type*} {p : Fin 5 → V} {m : V → V}
    (injective : Function.Injective p) (involutive : Function.Involutive m)
    (fixedPointFree : ∀ x, m x ≠ x) :
    (∃ x y z, SwitchedLeave p m x y ∧ SwitchedLeave p m y z ∧
      SwitchedLeave p m z x) ↔ m (p 1) = p 3 := by
  have distinct {x y : V} (h : SwitchedLeave p m x y) : x ≠ y := by
    intro eq
    subst y
    rcases h with ⟨i, j, hi, hj, step⟩ | ⟨_, _, _, _, e⟩
    · have same := injective (hi.trans hj.symm)
      subst j
      omega
    · exact fixedPointFree _ e
  have two_matches {x y z : V} (xy : RemainingMatch p m x y)
      (yz : RemainingMatch p m y z) : z = x := by
    obtain ⟨_, _, _, _, e₁⟩ := xy
    obtain ⟨_, _, _, _, e₂⟩ := yz
    rw [← e₁, involutive] at e₂
    exact e₂.symm
  constructor
  · rintro ⟨x, y, z, xy, yz, zx⟩
    have hxy := distinct xy
    have hyz := distinct yz
    have hzx := distinct zx
    rcases xy with (xy | xy)
    · rcases yz with (yz | yz)
      · exact path_two_then_match injective involutive xy yz zx hzx.symm
      · rcases zx with (zx | zx)
        · exact path_two_then_match injective involutive zx xy (Or.inr yz) hyz.symm
        · exact (hxy (two_matches yz zx)).elim
    · rcases yz with (yz | yz)
      · rcases zx with (zx | zx)
        · exact path_two_then_match injective involutive yz zx (Or.inr xy) hxy.symm
        · exact (hyz (two_matches zx xy)).elim
      · exact (hzx (two_matches xy yz)).elim
  · intro mate
    have reverse : m (p 3) = p 1 := by rw [← mate, involutive]
    have different {i j : Fin 5} (ne : i ≠ j) : p i ≠ p j := fun eq => ne (injective eq)
    refine ⟨p 1, p 2, p 3, Or.inl ⟨1, 2, rfl, rfl, Or.inl rfl⟩,
      Or.inl ⟨2, 3, rfl, rfl, Or.inl rfl⟩, Or.inr ?_⟩
    exact ⟨different (by decide), different (by decide), different (by decide),
      different (by decide), reverse⟩

end D5.S3.Combinatorics.Matroids.PointDeletedSteinerSwitch
