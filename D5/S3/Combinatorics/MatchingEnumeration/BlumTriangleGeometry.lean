/- GID: D5/S3/Combinatorics/MatchingEnumeration/BlumTriangleGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatchingEnumeration/BlumTriangleGeometry
   mirror-E: none(waiver:reflection-halfplane-path-construction)
   anchors: []
   utility: none
   digest: Axis overlay components fold to paths in the closed left half-plane. -/

import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleOverlay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleGeometry

open BlumTriangleDefs BlumTriangleSwitching

/-- A strictly crossing matching edge is its own reflected doubled component. It cannot
belong to an axis component. Folding the latter's paths therefore gives left-half paths. -/
theorem axis_component_left_connection (k : ℕ) (P : PerfectMatching (4 * k))
    (a b : Vertex (4 * k)) (ha : reflection (4 * k) a = a)
    (hb : reflection (4 * k) b = b)
    (hab : Relation.EqvGen
      (fun u z => z = P.1 u ∨ z = reflection (4 * k) (P.1 (reflection (4 * k) u)))
        a b) :
    Relation.EqvGen (fun u z =>
      (z = P.1 u ∨ z = reflection (4 * k) (P.1 (reflection (4 * k) u))) ∧
        u.1.2.val ≤ 4 * k - 1 ∧ z.1.2.val ≤ 4 * k - 1) a b := by
  classical
  let h := 4 * k - 1
  let r : Vertex (4 * k) → Vertex (4 * k) := reflection (4 * k)
  let p := P.1
  let q : Vertex (4 * k) → Vertex (4 * k) := fun u => r (p (r u))
  let edge : Vertex (4 * k) → Vertex (4 * k) → Prop := fun u z => z = p u ∨ z = q u
  let conn := Relation.EqvGen edge
  have rr (u : Vertex (4 * k)) : r (r u) = u := (reflection (4 * k)).left_inv u
  have pp (u : Vertex (4 * k)) : p (p u) = u := (P.2 u).1
  have qq (u : Vertex (4 * k)) : q (q u) = u := by simp only [q, rr, pp]
  have rx (u : Vertex (4 * k)) : (r u).1.2.val = 2 * h - u.1.2.val := rfl
  have ar : r a = a := ha
  have br : r b = b := hb
  have ax : a.1.2.val = h := by
    have he := congrArg (fun u : Vertex (4 * k) => u.1.2.val) ar
    rw [rx] at he
    have hv := a.2
    dsimp [h] at *
    omega
  have bx : b.1.2.val = h := by
    have he := congrArg (fun u : Vertex (4 * k) => u.1.2.val) br
    rw [rx] at he
    have hv := b.2
    dsimp [h] at *
    omega
  have reflect_edge {u z : Vertex (4 * k)} (hz : edge u z) : edge (r u) (r z) := by
    rcases hz with hz | hz
    · right
      simp only [q, rr, hz]
    · left
      simp only [q] at hz ⊢
      rw [hz, rr]
  have reflect_conn {u z : Vertex (4 * k)} (hz : conn u z) : conn (r u) (r z) := by
    induction hz with
    | rel u z hz => exact Relation.EqvGen.rel _ _ (reflect_edge hz)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  have crossing (u z : Vertex (4 * k)) (hadj : Adj u z)
      (hx : u.1.2.val < h ∧ h < z.1.2.val) : z = r u := by
    have hu := u.2
    have hz := z.2
    have hr := u.1.1.isLt
    have xr : z.1.2.val = 2 * h - u.1.2.val ∧ z.1.1 = u.1.1 := by
      rcases hadj with hadj | hadj
      · rcases hadj with ⟨hd, hd'⟩ | ⟨he, ⟨hd, hd'⟩ | ⟨hd, hd'⟩⟩
        · rcases hd' with hd' | hd' <;> omega
        · refine ⟨?_, Fin.ext (by omega)⟩
          dsimp [h] at *
          omega
        · omega
      · rcases hadj with ⟨hd, hd'⟩ | ⟨he, ⟨hd, hd'⟩ | ⟨hd, hd'⟩⟩
        · rcases hd' with hd' | hd' <;> omega
        · omega
        · omega
    apply Subtype.ext
    apply Prod.ext
    · exact xr.2
    · exact Fin.ext xr.1
  have crossing_either (u z : Vertex (4 * k)) (hadj : Adj u z)
      (hx : (u.1.2.val < h ∧ h < z.1.2.val) ∨
        (z.1.2.val < h ∧ h < u.1.2.val)) : z = r u := by
    rcases hx with hx | hx
    · exact crossing u z hadj hx
    · have he := crossing z u (hadj.elim Or.inr Or.inl) hx
      have he' := congrArg r he
      simpa only [rr] using he'.symm
  have isolated (u : Vertex (4 * k)) (hu : p u = r u) :
      ∀ z, conn u z → z = u ∨ z = r u := by
    have pru : p (r u) = u := by rw [← hu, pp]
    have qu : q u = r u := by simp only [q, pru]
    have qru : q (r u) = u := by simp only [q, rr, hu]
    have carry {x y : Vertex (4 * k)} (hc : conn x y) :
        (x = u ∨ x = r u) ↔ (y = u ∨ y = r u) := by
      induction hc with
      | rel x y he =>
        have forward {x y : Vertex (4 * k)} (he : edge x y)
            (hx : x = u ∨ x = r u) : y = u ∨ y = r u := by
          rcases hx with rfl | rfl <;> rcases he with rfl | rfl
          · exact Or.inr hu
          · exact Or.inr qu
          · exact Or.inl pru
          · exact Or.inl qru
        refine ⟨forward he, fun hy => forward ?_ hy⟩
        rcases he with rfl | rfl
        · exact Or.inl (pp x).symm
        · exact Or.inr (qq x).symm
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
    intro z hz
    exact (carry hz).mp (Or.inl rfl)
  have no_crossing (u : Vertex (4 * k)) (hc : conn a u) :
      ¬ ((u.1.2.val < h ∧ h < (p u).1.2.val) ∨
        ((p u).1.2.val < h ∧ h < u.1.2.val)) := by
    intro hx
    have hu := crossing_either u (p u) (P.2 u).2.2 hx
    have hh := isolated u hu a (Relation.EqvGen.symm _ _ hc)
    have hn : u.1.2.val ≠ h := by rcases hx with hx | hx <;> omega
    rcases hh with he | he
    · exact hn ((congrArg (fun z : Vertex (4 * k) => z.1.2.val) he).symm.trans ax)
    · have he' := congrArg r he
      rw [ar, rr] at he'
      exact hn ((congrArg (fun z : Vertex (4 * k) => z.1.2.val) he').symm.trans ax)
  have no_crossing_edge {u z : Vertex (4 * k)} (hc : conn a u) (he : edge u z) :
      ¬ ((u.1.2.val < h ∧ h < z.1.2.val) ∨
        (z.1.2.val < h ∧ h < u.1.2.val)) := by
    rcases he with rfl | rfl
    · exact no_crossing u hc
    · intro hx
      have hc' : conn a (r u) := by simpa only [ar] using reflect_conn hc
      have hn := no_crossing (r u) hc'
      apply hn
      have hu := u.2
      have hp := (p (r u)).2
      dsimp [q] at hx
      rw [rx] at hx
      rw [rx]
      rcases hx with hx | hx
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
  let fold : Vertex (4 * k) → Vertex (4 * k) := fun u =>
    if u.1.2.val ≤ h then u else r u
  let leftEdge : Vertex (4 * k) → Vertex (4 * k) → Prop := fun u z =>
    edge u z ∧ u.1.2.val ≤ h ∧ z.1.2.val ≤ h
  have fold_left (u : Vertex (4 * k)) : (fold u).1.2.val ≤ h := by
    dsimp [fold]
    split_ifs with hu
    · exact hu
    · rw [rx]
      omega
  have fixed_on_axis (u : Vertex (4 * k)) (hu : u.1.2.val = h) : r u = u := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      rw [rx, hu]
      omega
  have fold_step {u z : Vertex (4 * k)} (hc : conn a u) (he : edge u z) :
      leftEdge (fold u) (fold z) := by
    refine ⟨?_, fold_left u, fold_left z⟩
    have hn := no_crossing_edge hc he
    dsimp [fold]
    split_ifs with hu hz hz
    · exact he
    · have hux : u.1.2.val = h := by omega
      simpa only [fixed_on_axis u hux] using reflect_edge he
    · have hzx : z.1.2.val = h := by omega
      simpa only [fixed_on_axis z hzx] using reflect_edge he
    · exact reflect_edge he
  have transport {u z : Vertex (4 * k)} (hc : conn u z) :
      conn a u → Relation.EqvGen leftEdge (fold u) (fold z) := by
    induction hc with
    | rel u z he =>
      intro hu
      exact Relation.EqvGen.rel _ _ (fold_step hu he)
    | refl => exact fun _ => Relation.EqvGen.refl _
    | symm u z hc ih =>
      intro hu
      exact Relation.EqvGen.symm _ _ (ih (Relation.EqvGen.trans _ _ _ hu
        (Relation.EqvGen.symm _ _ hc)))
    | trans u z w hc hc' ih ih' =>
      intro hu
      exact Relation.EqvGen.trans _ _ _ (ih hu)
        (ih' (Relation.EqvGen.trans _ _ _ hu hc))
  have answer := transport hab (Relation.EqvGen.refl a)
  have fa : fold a = a := if_pos (by rw [ax])
  have fb : fold b = b := if_pos (by rw [bx])
  rw [fa, fb] at answer
  exact answer

end D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleGeometry
