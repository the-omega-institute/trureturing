/- GID: D5/S3/Geometry/Hyperideal/LowFaceAngleObstruction
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LowFaceAngleObstruction
   mirror-E: none(waiver:actual-low-face-angle-obstruction)
   anchors: []
   utility: none
   digest: Low-face transport pairs genuine middle-edge occurrences on each actual global edge. -/

import D5.S3.Geometry.Hyperideal.EdgeStarTransitions
import D5.S3.Geometry.Hyperideal.EvenAngleSumObstruction
import D5.S3.PrimeForms.Crossing.GlideCrossingParity

/-! Actual low-face transport and angle sums on the original edge quotient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.Hyperideal.LowFaceAngleObstruction

open EdgeStarTransitions

/-- Opposite edges in the order (12,13,14,34,24,23). -/
def opposite : Fin 6 → Fin 6 := ![3, 4, 5, 0, 1, 2]

/-- A block either has no short edge, or has one short axis, its long opposite,
and four middle edges. -/
def BlockShape (x : Fin 6 → ℝ) (h : ℝ) : Prop :=
  (∀ j, h ≤ x j) ∨ ∃ a : Fin 6,
    x a < h ∧ h < x (opposite a) ∧
      ∀ j, j ≠ a → j ≠ opposite a → x j = h

/-- A face is low when it contains an edge shorter than the middle length. -/
def LowFace (x : Fin 6 → ℝ) (h : ℝ) (f : Fin 4) : Prop :=
  ∃ n : Fin 3, x (faceEdge f n) < h

private theorem unique_low_flag_table :
    ∀ a j : Fin 6, j ≠ a → j ≠ opposite a →
      ∃! z : Fin 4 × Fin 3,
        faceEdge z.1 z.2 = j ∧ ∃ k : Fin 3, faceEdge z.1 k = a := by
  unfold ExistsUnique
  decide

private theorem local_low_flag_unique {x : Fin 6 → ℝ} {h : ℝ}
    (hx : BlockShape x h) (j : Fin 6) (hj : x j = h) :
    (∃ a, x a < h) ↔
      ∃! z : Fin 4 × Fin 3, faceEdge z.1 z.2 = j ∧ LowFace x h z.1 := by
  rcases hx with hflat | ⟨a, ha, hb, hrest⟩
  · have hnoshort : ¬ ∃ a, x a < h := by
      rintro ⟨a, ha⟩
      exact (not_lt_of_ge (hflat a)) ha
    have hnolow : ∀ f, ¬ LowFace x h f := by
      rintro f ⟨n, hn⟩
      exact hnoshort ⟨faceEdge f n, hn⟩
    simp [hnoshort, hnolow]
  · have hshort : ∀ k, x k < h ↔ k = a := by
      intro k
      constructor
      · intro hk
        by_contra hka
        by_cases hkb : k = opposite a
        · rw [hkb] at hk
          exact (not_lt_of_ge hb.le) hk
        · rw [hrest k hka hkb] at hk
          exact (lt_irrefl _ hk)
      · rintro rfl
        exact ha
    have hja : j ≠ a := by
      intro heq
      subst j
      rw [hj] at ha
      exact (lt_irrefl _ ha)
    have hjb : j ≠ opposite a := by
      intro heq
      rw [heq] at hj
      rw [hj] at hb
      exact (lt_irrefl _ hb)
    have hfaces : ∀ f, LowFace x h f ↔ ∃ k, faceEdge f k = a := by
      intro f
      simp only [LowFace, hshort]
    constructor
    · intro _
      simpa only [hfaces] using unique_low_flag_table a j hja hjb
    · intro _
      exact ⟨a, ha⟩

attribute [local instance] Classical.propDecidable

variable {T : Type*} [Fintype T]

/-- The low-face flags over a middle global edge count genuine local occurrences
with their full multiplicity; the actual face pairing makes this count even. -/
theorem genuine_occurrences_even
    (p : RawFacePairing T) (length : p.GlobalEdge → ℝ) (h : ℝ)
    (hshape : ∀ t, BlockShape (fun j => length (p.edgeLabel t j)) h)
    (e : p.GlobalEdge) (he : length e = h) :
    Even (Fintype.card {i : Occurrence T //
      p.edgeLabel i.1 i.2 = e ∧ ∃ a, length (p.edgeLabel i.1 a) < h}) := by
  classical
  let O := {i : Occurrence T //
    p.edgeLabel i.1 i.2 = e ∧ ∃ a, length (p.edgeLabel i.1 a) < h}
  let L := {d : FlagOrientation.Flag T //
    p.edgeLabel d.1 (faceEdge d.2.1 d.2.2) = e ∧
      LowFace (fun j => length (p.edgeLabel d.1 j)) h d.2.1}
  let project : L → O := fun d =>
    ⟨(d.1.1, faceEdge d.1.2.1 d.1.2.2), d.2.1, by
      obtain ⟨k, hk⟩ := d.2.2
      exact ⟨faceEdge d.1.2.1 k, hk⟩⟩
  have hbij : Function.Bijective project := by
    constructor
    · intro d z hdz
      have hocc := congrArg Subtype.val hdz
      dsimp only [project] at hocc
      have ht : d.1.1 = z.1.1 := congrArg Prod.fst hocc
      have hj : faceEdge d.1.2.1 d.1.2.2 = faceEdge z.1.2.1 z.1.2.2 :=
        congrArg Prod.snd hocc
      obtain ⟨q, hq, huniq⟩ :=
        (local_low_flag_unique (hshape d.1.1)
          (faceEdge d.1.2.1 d.1.2.2) (by rw [d.2.1]; exact he)).mp (project d).2.2
      have hd : d.1.2 = q := huniq _ ⟨rfl, d.2.2⟩
      have hz : z.1.2 = q := huniq _ ⟨hj.symm, by simpa only [ht] using z.2.2⟩
      apply Subtype.ext
      exact Prod.ext ht (hd.trans hz.symm)
    · intro i
      obtain ⟨z, hz, _⟩ :=
        (local_low_flag_unique (hshape i.1.1) i.1.2 (by rw [i.2.1]; exact he)).mp i.2.2
      refine ⟨⟨(i.1.1, z), ?_⟩, ?_⟩
      · exact ⟨by simpa only [hz.1] using i.2.1, hz.2⟩
      · apply Subtype.ext
        exact Prod.ext rfl hz.1
  let pairing : FlagOrientation.Pairing T := {
    facePair := p.facePair
    faceMap := p.faceMap
    pairInvolutive := p.pairInvolutive
    pairFixedFree := p.pairFixedFree
    mapInverse := p.mapInverse
  }
  have hlabel (x : T × Fin 4) (n : Fin 3) :
      p.edgeLabel x.1 (faceEdge x.2 n) =
        p.edgeLabel (p.facePair x).1
          (faceEdge (p.facePair x).2 (p.faceMap x n)) := by
    apply Quotient.sound
    exact Relation.EqvGen.rel _ _ ⟨x, n, rfl, rfl⟩
  let partner : L → L := fun d =>
    ⟨pairing.cross d.1, by
      change p.edgeLabel (p.facePair (d.1.1, d.1.2.1)).1
        (faceEdge (p.facePair (d.1.1, d.1.2.1)).2
          (p.faceMap (d.1.1, d.1.2.1) d.1.2.2)) = e ∧ _
      constructor
      · exact (hlabel _ _).symm.trans d.2.1
      · obtain ⟨k, hk⟩ := d.2.2
        refine ⟨p.faceMap (d.1.1, d.1.2.1) k, ?_⟩
        change length (p.edgeLabel (p.facePair (d.1.1, d.1.2.1)).1
          (faceEdge (p.facePair (d.1.1, d.1.2.1)).2
            (p.faceMap (d.1.1, d.1.2.1) k))) < h
        rw [← hlabel]
        exact hk⟩
  have hinvol : Function.Involutive partner := by
    intro d
    apply Subtype.ext
    change pairing.cross.symm (pairing.cross d.1) = d.1
    exact pairing.cross.symm_apply_apply d.1
  have hfree : ∀ d, partner d ≠ d := by
    intro d hd
    apply p.pairFixedFree (d.1.1, d.1.2.1)
    exact congrArg (fun z : L => (z.1.1, z.1.2.1)) hd
  have heven : Even (Fintype.card L) :=
    D5.S3.PrimeForms.Crossing.GlideCrossingParity.glide_crossing_count_even
      partner hinvol hfree
  rw [Fintype.card_congr (Equiv.ofBijective project hbij)] at heven
  exact heven

/-- Actual middle-edge angle sums cannot close when flat occurrences vanish
and genuine contributions lie strictly between pi/3 and pi/2. -/
theorem middle_edge_angle_sum_ne_two_pi
    (p : RawFacePairing T) (length : p.GlobalEdge → ℝ) (h : ℝ)
    (hshape : ∀ t, BlockShape (fun j => length (p.edgeLabel t j)) h)
    (e : p.GlobalEdge) (he : length e = h) (angle : Occurrence T → ℝ)
    (hangle : ∀ i : Occurrence T, p.edgeLabel i.1 i.2 = e →
      ((∃ a, length (p.edgeLabel i.1 a) < h) →
        Real.pi / 3 < angle i ∧ angle i < Real.pi / 2) ∧
      ((¬ ∃ a, length (p.edgeLabel i.1 a) < h) → angle i = 0)) :
    (∑ i : {i : Occurrence T // p.edgeLabel i.1 i.2 = e}, angle i.1) ≠
      2 * Real.pi := by
  classical
  let F := {i : Occurrence T // p.edgeLabel i.1 i.2 = e}
  let genuine : Occurrence T → Prop := fun i =>
    ∃ a, length (p.edgeLabel i.1 a) < h
  let U := {i : F // genuine i.1}
  let collapse : U ≃ {i : Occurrence T //
      p.edgeLabel i.1 i.2 = e ∧ genuine i} :=
    Equiv.subtypeSubtypeEquivSubtypeInter _ _
  have heven : Even (Fintype.card U) := by
    rw [Fintype.card_congr collapse]
    exact genuine_occurrences_even p length h hshape e he
  have hrange : ∀ i : U,
      Real.pi / 3 < angle i.1.1 ∧ angle i.1.1 < Real.pi / 2 := by
    intro i
    exact (hangle i.1.1 i.1.2).1 i.2
  have hne := EvenAngleSumObstruction.even_middle_angle_sum_ne_two_pi
    (fun i : U => angle i.1.1) heven hrange
  have hsum : (∑ i : U, angle i.1.1) = ∑ i : F, angle i.1 := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (p := fun i : F => genuine i.1) (f := fun i : F => angle i.1)
    have hzero : (∑ i : {i : F // ¬ genuine i.1}, angle i.1.1) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact (hangle i.1.1 i.1.2).2 i.2
    simpa only [hzero, add_zero] using hsplit
  rw [hsum] at hne
  exact hne

#print axioms genuine_occurrences_even
#print axioms middle_edge_angle_sum_ne_two_pi

end D5.S3.Geometry.Hyperideal.LowFaceAngleObstruction
