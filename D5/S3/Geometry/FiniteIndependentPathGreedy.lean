/- GID: D5/S3/Geometry/FiniteIndependentPathGreedy
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteIndependentPathGreedy
   mirror-E: none(waiver:augmented-path-greedy-recurrence)
   anchors: [mathlib/module/Mathlib.Data.Finset.Basic]
   utility: none
   digest: Augmented independent paths have an exact unbounded three-coordinate greedy recurrence. -/
import D5.S3.Geometry.FiniteGreedyFamilyTransport

/-! UNCOMPILED. The empty face is part of the augmented path family. It is
bookkeeping for complementary original faces, not a lower native collapse face.
All paths are on the supplied list of original labels. -/

noncomputable section
open Finset

namespace D5.S3.Geometry.FiniteIndependentPathGreedy
open FiniteCoordinateGreedyMatching FiniteGreedyFamilyTransport
variable {V : Type*} [Fintype V] [DecidableEq V]

def paths : List V → Finset (Finset V)
  | [] => {∅}
  | [v] => {∅, {v}}
  | v :: w :: vs => paths (w :: vs) ∪ (paths vs).image (insert v)

private theorem paths_cons (v : V) (vs : List V) :
    paths (v :: vs) = paths vs ∪ (paths (vs.drop 1)).image (insert v) := by
  cases vs with
  | nil => simp [paths]
  | cons w vs => rfl

private theorem paths_supported (vs : List V) {a : Finset V} (ha : a ∈ paths vs) :
    ∀ v ∈ a, v ∈ vs := by
  induction vs using paths.induct generalizing a with
  | case1 =>
    have he : a = ∅ := Finset.mem_singleton.mp ha
    subst a
    simp
  | case2 v =>
    simp only [paths, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · simp
    · simp
  | case3 v w vs ih1 ih2 =>
    rcases Finset.mem_union.mp ha with ha | ha
    · intro x hx; exact List.mem_cons_of_mem _ (ih1 ha x hx)
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih2 hb x hx))

private theorem paths_avoid (vs : List V) (v : V) (hv : v ∉ vs) :
    ∀ a ∈ paths vs, v ∉ a := fun a ha hm => hv (paths_supported vs ha v hm)

private theorem paths_step_decomposition (v w z : V) (vs : List V) :
    paths (v :: w :: z :: vs) =
      (paths (z :: vs) ∪ (paths vs).image (insert w)) ∪
        (paths (z :: vs)).image (insert v) := rfl

/-- Literal first-coordinate remaining family: fixed 0,1,0 followed by an
arbitrary augmented independent tail from the fourth coordinate. -/
theorem remaining_paths_three (v w z : V) (vs : List V)
    (hd : (v :: w :: z :: vs).Nodup) :
    remaining (paths (v :: w :: z :: vs)) v = (paths vs).image (insert w) := by
  have hv : v ∉ w :: z :: vs := (List.nodup_cons.mp hd).1
  have hw : w ∉ z :: vs := (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1
  have hvw : v ≠ w := fun h => hv (by simp [h])
  have hvT : ∀ a ∈ paths (z :: vs), v ∉ a :=
    paths_avoid _ _ (fun h => hv (by simp [h]))
  have hwT : ∀ a ∈ paths (z :: vs), w ∉ a := paths_avoid _ _ hw
  have hvU : ∀ a ∈ paths vs, v ∉ a := paths_avoid _ _ (fun h => hv (by simp [h]))
  have hwU : ∀ a ∈ paths vs, w ∉ a := paths_avoid _ _ (fun h => hw (by simp [h]))
  rw [paths_step_decomposition]
  ext a
  rw [mem_remaining]
  constructor
  · rintro ⟨ha, hn⟩
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp ha with ha | ha
      · exfalso
        apply hn
        have hva := hvT a ha
        simp only [FiniteGreedyFamilyTransport.flip, if_neg hva]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      · exact ha
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      exfalso
      apply hn
      have hvb := hvT b hb
      have he : FiniteGreedyFamilyTransport.flip v (insert v b) = b := by simp [FiniteGreedyFamilyTransport.flip, hvb]
      rw [he]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
  · intro ha
    refine ⟨Finset.mem_union_left _ (Finset.mem_union_right _ ha), ?_⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    have hvb := hvU b hb
    have hwb := hwU b hb
    have hvwb : v ∉ insert w b := by simp [hvw, hvb]
    rw [FiniteGreedyFamilyTransport.flip, if_neg hvwb]
    intro ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · exact hvT _ ht (by simp)
      · obtain ⟨c, hc, he⟩ := Finset.mem_image.mp ht
        have hvC : v ∉ insert w c := by simp [hvw, hvU c hc]
        exact hvC (he.symm ▸ Finset.mem_insert_self v (insert w b))
    · obtain ⟨c, hc, he⟩ := Finset.mem_image.mp ht
      have hwC : w ∉ insert v c := by simp [Ne.symm hvw, hwT c hc]
      exact hwC (he.symm ▸ (by simp : w ∈ insert v (insert w b)))

theorem remaining_paths_two (v w : V) (hvw : v ≠ w) :
    remaining (paths [v, w]) v = {{w}} := by
  have he : paths [v, w] = {∅, {w}, {v}} := by
    ext a
    simp [paths, or_assoc, or_left_comm, or_comm]
  rw [he]
  ext a
  rw [mem_remaining, Finset.mem_singleton]
  constructor
  · rintro ⟨ha, hn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact (hn (by simp [FiniteGreedyFamilyTransport.flip])).elim
    · rfl
    · exact (hn (by simp [FiniteGreedyFamilyTransport.flip])).elim
  · rintro rfl
    refine ⟨by simp, ?_⟩
    have hvw' : v ∉ ({w} : Finset V) := by simpa using hvw
    have hvf : v ∈ FiniteGreedyFamilyTransport.flip v ({w} : Finset V) := by simp [hvw']
    have hwf : w ∈ FiniteGreedyFamilyTransport.flip v ({w} : Finset V) := by simp [Ne.symm hvw]
    intro hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact (by simpa only [hm, Finset.notMem_empty] using hvf)
    · have he : v = w := Finset.mem_singleton.mp (hm ▸ hvf)
      exact hvw he
    · have he : w = v := Finset.mem_singleton.mp (hm ▸ hwf)
      exact hvw he.symm

theorem remaining_paths_one (v : V) : remaining (paths [v]) v = ∅ := by
  ext a
  simp only [mem_remaining, Finset.notMem_empty, iff_false]
  rintro ⟨ha, hn⟩
  simp only [paths, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact hn (by simp [FiniteGreedyFamilyTransport.flip, paths])
  · exact hn (by simp [FiniteGreedyFamilyTransport.flip, paths])

/-- Recursive answer, with the three actual augmented bases distinguished.
This is a result computed from the path, not a supplied survivor certificate. -/
def pathCritical : List V → Finset (Finset V)
  | [] => {∅}
  | [_] => ∅
  | [_, w] => {{w}}
  | _ :: w :: _ :: vs => (pathCritical vs).image (insert w)

/-- Unbounded induction on the original coordinate list. The induction step
deletes three coordinates and commutes every remaining actual greedy round
with insertion of the fixed middle vertex. -/
theorem survivors_paths (vs : List V) (hd : vs.Nodup) :
    survivors (paths vs) vs = pathCritical vs := by
  induction vs using pathCritical.induct with
  | case1 => rfl
  | case2 v => simp [survivors, remaining_paths_one, pathCritical]
  | case3 v w =>
    have hvw : v ≠ w := by simpa using (List.nodup_cons.mp hd).1
    simp only [survivors, remaining_paths_two v w hvw]
    rw [remaining_of_fixed _ w (Or.inl (by simp))]
    rfl
  | case4 v w z vs ih =>
    have htail : (w :: z :: vs).Nodup := (List.nodup_cons.mp hd).2
    have hw : w ∉ z :: vs := (List.nodup_cons.mp htail).1
    have hz : z ∉ vs := (List.nodup_cons.mp (List.nodup_cons.mp htail).2).1
    have hvs : vs.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp htail).2).2
    have hwvs : w ∉ vs := fun h => hw (by simp [h])
    have hzF : ∀ a ∈ (paths vs).image (insert w), z ∉ a := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      have hzw : z ≠ w := by intro he; exact hw (by simp [he])
      simp [hzw, paths_avoid vs z hz b hb]
    change survivors (remaining (paths (v :: w :: z :: vs)) v) (w :: z :: vs) = _
    rw [remaining_paths_three v w z vs hd]
    change survivors (remaining (remaining ((paths vs).image (insert w)) w) z) vs = _
    rw [remaining_of_fixed _ w (Or.inl (by
      intro a ha
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
      simp))]
    rw [remaining_of_fixed _ z (Or.inr hzF)]
    rw [survivors_insert (paths vs) vs w (paths_avoid vs w hwvs) hwvs, ih hvs]
    rfl

/-- The selected second vertex of each consecutive triple, including the
second vertex of a final two-vertex block. -/
def pathChosen : List V → Finset V
  | [] => ∅
  | [_] => ∅
  | [_, w] => {w}
  | _ :: w :: _ :: vs => insert w (pathChosen vs)

private theorem pathCritical_closed (vs : List V) :
    pathCritical vs = if vs.length % 3 = 1 then ∅ else {pathChosen vs} := by
  induction vs using pathCritical.induct with
  | case1 => simp [pathCritical, pathChosen]
  | case2 v => simp [pathCritical, pathChosen]
  | case3 v w => simp [pathCritical, pathChosen]
  | case4 v w z vs ih =>
    have hm : (v :: w :: z :: vs).length % 3 = vs.length % 3 := by
      simp only [List.length_cons]
      omega
    simp only [pathCritical, pathChosen, hm, ih]
    split <;> simp_all

theorem survivors_paths_closed (vs : List V) (hd : vs.Nodup) :
    survivors (paths vs) vs =
      if vs.length % 3 = 1 then ∅ else {pathChosen vs} := by
  rw [survivors_paths vs hd, pathCritical_closed]

/-- Explicit local definition of path independence, with no cyclic edge. -/
def IndependentAlong : List V → Finset V → Prop
  | [], _ => True
  | [_], _ => True
  | v :: w :: vs, a => (v ∉ a ∨ w ∉ a) ∧ IndependentAlong (w :: vs) a

private theorem independent_tail (v : V) (vs : List V) (a : Finset V)
    (h : IndependentAlong (v :: vs) a) : IndependentAlong vs a := by
  cases vs with
  | nil => trivial
  | cons w vs => exact h.2

private theorem independent_congr (vs : List V) (a b : Finset V)
    (h : ∀ x ∈ vs, x ∈ a ↔ x ∈ b) : IndependentAlong vs a ↔ IndependentAlong vs b := by
  induction vs generalizing a b with
  | nil => rfl
  | cons v vs ih =>
    cases vs with
    | nil => rfl
    | cons w vs =>
      change ((v ∉ a ∨ w ∉ a) ∧ IndependentAlong (w :: vs) a) ↔
        ((v ∉ b ∨ w ∉ b) ∧ IndependentAlong (w :: vs) b)
      rw [h v (by simp), h w (by simp)]
      exact and_congr Iff.rfl (ih a b (fun x hx => h x (by simp [hx])))

/-- Identification with the full augmented independent-path family. Support,
adjacency and the empty face are all part of this equivalence. -/
theorem mem_paths_iff (vs : List V) (hd : vs.Nodup) (a : Finset V) :
    a ∈ paths vs ↔ (∀ x ∈ a, x ∈ vs) ∧ IndependentAlong vs a := by
  induction vs using paths.induct generalizing a with
  | case1 =>
    simp only [paths, Finset.mem_singleton, List.not_mem_nil, IndependentAlong, and_true]
    constructor
    · rintro rfl; simp
    · intro h
      apply Finset.eq_empty_iff_forall_notMem.mpr
      exact h
  | case2 v =>
    simp only [paths, Finset.mem_insert, Finset.mem_singleton, IndependentAlong, and_true]
    constructor
    · rintro (rfl | rfl) <;> simp
    · intro h
      by_cases hv : v ∈ a
      · right
        ext x
        constructor
        · intro hx; simpa using h x hx
        · intro hx
          exact (Finset.mem_singleton.mp hx).symm ▸ hv
      · left
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have he : x = v := by simpa using h x hx
        exact hv (he ▸ hx)
  | case3 v w vs ih1 ih2 =>
    have hv : v ∉ w :: vs := (List.nodup_cons.mp hd).1
    have htail : (w :: vs).Nodup := (List.nodup_cons.mp hd).2
    have hw : w ∉ vs := (List.nodup_cons.mp htail).1
    have hvs : vs.Nodup := (List.nodup_cons.mp htail).2
    have hvw : v ≠ w := fun h => hv (by simp [h])
    have hvvs : v ∉ vs := fun h => hv (by simp [h])
    constructor
    · intro ha
      refine ⟨paths_supported _ ha, ?_⟩
      rcases Finset.mem_union.mp ha with ha | ha
      · exact ⟨Or.inl (paths_avoid _ v hv a ha), ((ih1 htail a).mp ha).2⟩
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
        have hvb := paths_avoid vs v hvvs b hb
        have hwb := paths_avoid vs w hw b hb
        have hbI := ((ih2 hvs b).mp hb).2
        have hI : IndependentAlong vs (insert v b) :=
          (independent_congr vs b (insert v b) (by
            intro x hx
            have hxv : x ≠ v := fun he => hvvs (he ▸ hx)
            simp [hxv])).mp hbI
        have hwi : w ∉ insert v b := by simp [Ne.symm hvw, hwb]
        refine ⟨Or.inr hwi, ?_⟩
        cases vs with
        | nil => trivial
        | cons z vs => exact ⟨Or.inl hwi, hI⟩
    · rintro ⟨hsupp, hI⟩
      by_cases hva : v ∈ a
      · have hwa : w ∉ a := hI.1.resolve_left (not_not.mpr hva)
        let b := a.erase v
        have hbSupp : ∀ x ∈ b, x ∈ vs := by
          intro x hx
          have hx' := Finset.mem_erase.mp hx
          have hxs := hsupp x hx'.2
          rcases List.mem_cons.mp hxs with h | h
          · exact (hx'.1 h).elim
          · rcases List.mem_cons.mp h with h | h
            · exact (hwa (h ▸ hx'.2)).elim
            · exact h
        have hbI : IndependentAlong vs b := by
          have hIa := independent_tail w vs a (independent_tail v (w :: vs) a hI)
          apply (independent_congr vs a b (by
            intro x hx
            have hxv : x ≠ v := fun he => hvvs (he ▸ hx)
            simp [b, hxv])).mp hIa
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨b, (ih2 hvs b).mpr ⟨hbSupp, hbI⟩, Finset.insert_erase hva⟩)
      · apply Finset.mem_union_left
        apply (ih1 htail a).mpr
        refine ⟨?_, hI.2⟩
        intro x hx
        rcases List.mem_cons.mp (hsupp x hx) with h | h
        · exact (hva (h ▸ hx)).elim
        · exact h

end D5.S3.Geometry.FiniteIndependentPathGreedy
