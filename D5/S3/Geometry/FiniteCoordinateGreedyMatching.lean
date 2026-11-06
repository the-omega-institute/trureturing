/- GID: D5/S3/Geometry/FiniteCoordinateGreedyMatching
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCoordinateGreedyMatching
   mirror-E: none(waiver:relative-coordinate-matching)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Coordinate rounds give disjoint original-label face pairs and explicit relative A and B branches. -/
import D5.S3.Geometry.FiniteAcyclicFaceMatching

/-! UNCOMPILED. This is the literal simultaneous-round algorithm on E minus D.
No empty face is silently removed from an arbitrary relative family. For a
native nonempty complex use E = empty plus its faces and D = {empty}.
The acyclicity consumer is separate from the combinatorial definitions here.
-/

noncomputable section
open Set Finset

namespace D5.S3.Geometry.FiniteCoordinateGreedyMatching

open FiniteAcyclicFaceMatching
open FiniteVertexDominationCollapse (faceSet mem_faceSet)

variable {V : Type*} [Fintype V] [DecidableEq V]

def lowers (F : Finset (Finset V)) (v : V) : Finset (Finset V) := by
  classical exact F.filter fun s => v ∉ s ∧ insert v s ∈ F

def roundPairs (F : Finset (Finset V)) (v : V) : Finset (Finset V × V) :=
  (lowers F v).image fun s => (s, v)

def pairedFaces (F : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  lowers F v ∪ (lowers F v).image (insert v)

def remaining (F : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  F \ pairedFaces F v

def greedy (F : Finset (Finset V)) : List V → Finset (Finset V × V)
  | [] => ∅
  | v :: vs => roundPairs F v ∪ greedy (remaining F v) vs

def survivors (F : Finset (Finset V)) : List V → Finset (Finset V)
  | [] => F
  | v :: vs => survivors (remaining F v) vs

def rounds (F : Finset (Finset V)) : List V → List (Finset (Finset V × V))
  | [] => []
  | v :: vs => roundPairs F v :: rounds (remaining F v) vs

@[simp] theorem mem_lowers (F : Finset (Finset V)) (v : V) (s : Finset V) :
    s ∈ lowers F v ↔ s ∈ F ∧ v ∉ s ∧ insert v s ∈ F := by
  classical simp [lowers]

@[simp] theorem mem_roundPairs (F : Finset (Finset V)) (v : V) (e : Finset V × V) :
    e ∈ roundPairs F v ↔ e.2 = v ∧ e.1 ∈ lowers F v := by
  classical
  simp only [roundPairs, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨rfl, hs⟩
  · rintro ⟨hv, hs⟩; exact ⟨e.1, hs, Prod.ext rfl hv.symm⟩

theorem paired_subset (F : Finset (Finset V)) (v : V) : pairedFaces F v ⊆ F := by
  intro s hs
  rcases Finset.mem_union.mp hs with hs | hs
  · exact ((mem_lowers F v s).mp hs).1
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact ((mem_lowers F v t).mp ht).2.2

theorem round_incident {F : Finset (Finset V)} {v : V}
    {e : Finset V × V} (he : e ∈ roundPairs F v) {s : Finset V}
    (hs : Incident s e) : s ∈ pairedFaces F v := by
  obtain ⟨hv, hl⟩ := (mem_roundPairs F v e).mp he
  rcases hs with rfl | rfl
  · exact Finset.mem_union_left _ hl
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.1, hl, by simp [upper, hv]⟩)

theorem round_disjoint {F : Finset (Finset V)} {v : V}
    {e f : Finset V × V} (he : e ∈ roundPairs F v) (hf : f ∈ roundPairs F v)
    {s : Finset V} (hse : Incident s e) (hsf : Incident s f) : e = f := by
  obtain ⟨hev, hel⟩ := (mem_roundPairs F v e).mp he
  obtain ⟨hfv, hfl⟩ := (mem_roundPairs F v f).mp hf
  have hen := ((mem_lowers F v e.1).mp hel).2.1
  have hfn := ((mem_lowers F v f.1).mp hfl).2.1
  apply Prod.ext _ (hev.trans hfv.symm)
  rcases hse with heq | heq <;> rcases hsf with hfq | hfq
  · exact heq.symm.trans hfq
  · have hv : v ∈ s := by rw [hfq]; simp [upper, hfv]
    exact (hen (heq ▸ hv)).elim
  · have hv : v ∈ s := by rw [heq]; simp [upper, hev]
    exact (hfn (hfq ▸ hv)).elim
  · have hi : insert v e.1 = insert v f.1 := by
      simpa only [upper, hev, hfv] using heq.symm.trans hfq
    have hee := congrArg (fun t : Finset V => t.erase v) hi
    simpa [Finset.erase_insert, hen, hfn] using hee

theorem remaining_subset (F : Finset (Finset V)) (v : V) : remaining F v ⊆ F :=
  Finset.sdiff_subset

theorem greedy_endpoints (F : Finset (Finset V)) (vs : List V)
    {e : Finset V × V} (he : e ∈ greedy F vs) :
    e.1 ∈ F ∧ upper e ∈ F ∧ e.2 ∉ e.1 := by
  induction vs generalizing F with
  | nil => simp [greedy] at he
  | cons v vs ih =>
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨hev, hel⟩ := (mem_roundPairs F v e).mp he
        obtain ⟨hl, hn, hu⟩ := (mem_lowers F v e.1).mp hel
        exact ⟨hl, by simpa [upper, hev] using hu, by simpa [hev] using hn⟩
      · obtain ⟨hl, hu, hn⟩ := ih (remaining F v) he
        exact ⟨(remaining_subset F v) hl, (remaining_subset F v) hu, hn⟩

theorem greedy_disjoint (F : Finset (Finset V)) (vs : List V)
    {e f : Finset V × V} (he : e ∈ greedy F vs) (hf : f ∈ greedy F vs)
    {s : Finset V} (hse : Incident s e) (hsf : Incident s f) : e = f := by
  induction vs generalizing F with
  | nil => simp [greedy] at he
  | cons v vs ih =>
      rcases Finset.mem_union.mp he with he | he <;>
        rcases Finset.mem_union.mp hf with hf | hf
      · exact round_disjoint he hf hse hsf
      · have hsf' : s ∈ remaining F v := by
          rcases hsf with rfl | rfl
          · exact (greedy_endpoints _ _ hf).1
          · exact (greedy_endpoints _ _ hf).2.1
        exact ((Finset.mem_sdiff.mp hsf').2 (round_incident he hse)).elim
      · have hse' : s ∈ remaining F v := by
          rcases hse with rfl | rfl
          · exact (greedy_endpoints _ _ he).1
          · exact (greedy_endpoints _ _ he).2.1
        exact ((Finset.mem_sdiff.mp hse').2 (round_incident hf hsf)).elim
      · exact ih (remaining F v) he hf hse hsf

theorem survivors_subset (F : Finset (Finset V)) (vs : List V) :
    survivors F vs ⊆ F := by
  induction vs generalizing F with
  | nil => exact le_rfl
  | cons v vs ih => exact (ih _).trans (remaining_subset F v)

theorem mem_survivors (F : Finset (Finset V)) (vs : List V) (s : Finset V) :
    s ∈ survivors F vs ↔ s ∈ F ∧ ∀ e ∈ greedy F vs, ¬ Incident s e := by
  induction vs generalizing F with
  | nil => simp [survivors, greedy]
  | cons v vs ih =>
      have hr : s ∈ remaining F v ↔ s ∈ F ∧ ∀ e ∈ roundPairs F v, ¬ Incident s e := by
        constructor
        · intro hs
          exact ⟨(Finset.mem_sdiff.mp hs).1, fun e he hse =>
            (Finset.mem_sdiff.mp hs).2 (round_incident he hse)⟩
        · rintro ⟨hs, hne⟩
          refine Finset.mem_sdiff.mpr ⟨hs, ?_⟩
          intro hp
          rcases Finset.mem_union.mp hp with hl | hu
          · exact hne (s, v) ((mem_roundPairs F v _).mpr ⟨rfl, hl⟩) (Or.inl rfl)
          · obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hu
            exact hne (t, v) ((mem_roundPairs F v _).mpr ⟨rfl, ht⟩) (Or.inr heq.symm)
      change s ∈ survivors (remaining F v) vs ↔ _
      rw [ih, hr]
      constructor
      · rintro ⟨⟨hs, h0⟩, h1⟩
        exact ⟨hs, fun e he => (Finset.mem_union.mp he).elim (h0 e) (h1 e)⟩
      · rintro ⟨hs, h⟩
        exact ⟨⟨hs, fun e he => h e (Finset.mem_union_left _ he)⟩,
          fun e he => h e (Finset.mem_union_right _ he)⟩

/-- Actual pairing on the NONEMPTY native faces, without any acyclicity field. -/
def pairing (K : PreAbstractSimplicialComplex V) (vs : List V) : Pairing K where
  pairs := greedy (faceSet K) vs
  lower_nonempty := by
    intro e he
    exact (K.isRelLowerSet_faces ((mem_faceSet K _).mp (greedy_endpoints _ _ he).1)).1
  apex_notMem := fun e he => (greedy_endpoints _ _ he).2.2
  upper_mem := fun e he => (mem_faceSet K _).mp (greedy_endpoints _ _ he).2.1
  disjoint := fun _ he _ hf _ hse hsf => greedy_disjoint _ _ he hf hse hsf

def Down (F : Finset (Finset V)) : Prop :=
  ∀ s ∈ F, ∀ t ⊆ s, t ∈ F

/-- Augmented complexes represented literally as finite downward families.
The empty family and the family containing only empty are distinct. -/
structure RelativeFamily where
  E : Finset (Finset V)
  D : Finset (Finset V)
  downE : Down E
  downD : Down D
  inclusion : D ⊆ E

namespace RelativeFamily

def F (R : RelativeFamily (V := V)) : Finset (Finset V) := R.E \ R.D

def A (R : RelativeFamily (V := V)) (v : V) : Finset (Finset V) := by
  classical exact R.F.filter fun s => v ∉ s ∧ insert v s ∉ R.E

def B (R : RelativeFamily (V := V)) (v : V) : Finset (Finset V) := by
  classical exact R.F.filter fun s => v ∈ s ∧ s.erase v ∈ R.D

@[simp] theorem mem_A (R : RelativeFamily (V := V)) (v : V) (s : Finset V) :
    s ∈ R.A v ↔ s ∈ R.F ∧ v ∉ s ∧ insert v s ∉ R.E := by
  classical simp [A]

@[simp] theorem mem_B (R : RelativeFamily (V := V)) (v : V) (s : Finset V) :
    s ∈ R.B v ↔ s ∈ R.F ∧ v ∈ s ∧ s.erase v ∈ R.D := by
  classical simp [B]

theorem A_upper (R : RelativeFamily (V := V)) (v : V)
    {s t : Finset V} (hs : s ∈ R.A v) (ht : t ∈ R.F) (hst : s ⊆ t) : t ∈ R.A v := by
  obtain ⟨hsF, hsv, hsE⟩ := (R.mem_A v s).mp hs
  have htE := (Finset.mem_sdiff.mp ht).1
  have htv : v ∉ t := fun hv => hsE
    (R.downE t htE (insert v s) (Finset.insert_subset hv hst))
  exact (R.mem_A v t).mpr ⟨ht, htv, fun hu => hsE
    (R.downE _ hu _ (Finset.insert_subset_insert v hst))⟩

theorem B_lower (R : RelativeFamily (V := V)) (v : V)
    {s t : Finset V} (hs : s ∈ R.B v) (ht : t ∈ R.F) (hts : t ⊆ s) : t ∈ R.B v := by
  obtain ⟨hsF, hsv, hsD⟩ := (R.mem_B v s).mp hs
  have htv : v ∈ t := by
    by_contra htv
    apply (Finset.mem_sdiff.mp ht).2
    apply R.downD _ hsD t
    intro a ha
    exact Finset.mem_erase.mpr ⟨fun hav => htv (hav ▸ ha), hts ha⟩
  exact (R.mem_B v t).mpr ⟨ht, htv,
    R.downD _ hsD _ (Finset.erase_subset_erase v hts)⟩

theorem branches_incomparable (R : RelativeFamily (V := V)) (v : V)
    {s t : Finset V} (hs : s ∈ R.A v) (ht : t ∈ R.B v) :
    ¬ s ⊆ t ∧ ¬ t ⊆ s := by
  have ha := (R.mem_A v s).mp hs
  have hb := (R.mem_B v t).mp ht
  constructor
  · intro hst
    exact ha.2.2 (R.downE t (Finset.mem_sdiff.mp hb.1).1
      (insert v s) (Finset.insert_subset hb.2.1 hst))
  · intro hts
    exact ha.2.1 (hts hb.2.1)

/-- Exact residual decomposition, including the empty face if it is available. -/
theorem remaining_eq (R : RelativeFamily (V := V)) (v : V) :
    remaining R.F v = R.A v ∪ R.B v := by
  classical
  ext s
  by_cases hsv : v ∈ s
  · have hins : insert v (s.erase v) = s := Finset.insert_erase hsv
    have hlow : s ∈ R.F → (s.erase v ∈ lowers R.F v ↔ s.erase v ∉ R.D) := by
      intro hsF
      have he : s.erase v ∈ R.E :=
        R.downE s (Finset.mem_sdiff.mp hsF).1 _ (Finset.erase_subset _ _)
      rw [mem_lowers]
      constructor
      · intro h; exact (Finset.mem_sdiff.mp h.1).2
      · intro hd
        exact ⟨Finset.mem_sdiff.mpr ⟨he, hd⟩, Finset.notMem_erase _ _,
          by simpa only [hins] using hsF⟩
    constructor
    · intro hs
      obtain ⟨hsF, hsp⟩ := Finset.mem_sdiff.mp hs
      apply Finset.mem_union_right
      apply (R.mem_B v s).mpr
      refine ⟨hsF, hsv, ?_⟩
      by_contra hd
      apply hsp
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨s.erase v, (hlow hsF).mpr hd, hins⟩)
    · intro hs
      rcases Finset.mem_union.mp hs with hs | hs
      · exact (((R.mem_A v s).mp hs).2.1 hsv).elim
      · obtain ⟨hsF, _, hsD⟩ := (R.mem_B v s).mp hs
        refine Finset.mem_sdiff.mpr ⟨hsF, ?_⟩
        intro hp
        rcases Finset.mem_union.mp hp with hl | hu
        · exact ((mem_lowers R.F v s).mp hl).2.1 hsv
        · obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hu
          have ht' := (mem_lowers R.F v t).mp ht
          have he' : t = s.erase v := by
            have hh := congrArg (fun a : Finset V => a.erase v) he
            simpa [Finset.erase_insert, ht'.2.1] using hh
          exact (Finset.mem_sdiff.mp ht'.1).2 (he'.symm ▸ hsD)
  · constructor
    · intro hs
      obtain ⟨hsF, hsp⟩ := Finset.mem_sdiff.mp hs
      apply Finset.mem_union_left
      apply (R.mem_A v s).mpr
      refine ⟨hsF, hsv, ?_⟩
      intro huE
      have huD : insert v s ∉ R.D := fun h =>
        (Finset.mem_sdiff.mp hsF).2 (R.downD _ h s (subset_insert _ _))
      exact hsp (Finset.mem_union_left _ ((mem_lowers R.F v s).mpr
        ⟨hsF, hsv, Finset.mem_sdiff.mpr ⟨huE, huD⟩⟩))
    · intro hs
      rcases Finset.mem_union.mp hs with hs | hs
      · obtain ⟨hsF, _, hsE⟩ := (R.mem_A v s).mp hs
        refine Finset.mem_sdiff.mpr ⟨hsF, ?_⟩
        intro hp
        rcases Finset.mem_union.mp hp with hl | hu
        · exact hsE (Finset.mem_sdiff.mp ((mem_lowers R.F v s).mp hl).2.2).1
        · obtain ⟨t, _, he⟩ := Finset.mem_image.mp hu
          exact hsv (he ▸ Finset.mem_insert_self v t)
      · exact (hsv ((R.mem_B v s).mp hs).2.1).elim

/-- A as a relative difference on the SAME original coordinate type. -/
def noBranch (R : RelativeFamily (V := V)) (v : V) : RelativeFamily (V := V) where
  E := R.E.filter fun s => v ∉ s
  D := R.E.filter fun s => v ∉ s ∧ (s ∈ R.D ∨ insert v s ∈ R.E)
  downE := by
    intro s hs t hts
    obtain ⟨hsE, hsv⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨R.downE s hsE t hts, fun hv => hsv (hts hv)⟩
  downD := by
    intro s hs t hts
    obtain ⟨hsE, hsv, hsd⟩ := Finset.mem_filter.mp hs
    refine Finset.mem_filter.mpr ⟨R.downE s hsE t hts, fun hv => hsv (hts hv), ?_⟩
    rcases hsd with hd | he
    · exact Or.inl (R.downD s hd t hts)
    · exact Or.inr (R.downE _ he _ (Finset.insert_subset_insert v hts))
  inclusion := by
    intro s hs
    have h := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨h.1, h.2.1⟩

/-- B as a relative difference without relabelling or dropping its fixed v.
All no-v faces of the upper family are put in the lower family. -/
def yesBranch (R : RelativeFamily (V := V)) (v : V) : RelativeFamily (V := V) where
  E := R.E.filter fun s => s.erase v ∈ R.D
  D := R.E.filter fun s => s.erase v ∈ R.D ∧ (v ∉ s ∨ s ∈ R.D)
  downE := by
    intro s hs t hts
    obtain ⟨hsE, hsD⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨R.downE s hsE t hts,
      R.downD _ hsD _ (Finset.erase_subset_erase v hts)⟩
  downD := by
    intro s hs t hts
    obtain ⟨hsE, hsD, hsd⟩ := Finset.mem_filter.mp hs
    refine Finset.mem_filter.mpr ⟨R.downE s hsE t hts,
      R.downD _ hsD _ (Finset.erase_subset_erase v hts), ?_⟩
    rcases hsd with hv | hd
    · exact Or.inl (fun hvt => hv (hts hvt))
    · exact Or.inr (R.downD s hd t hts)
  inclusion := by
    intro s hs
    have h := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨h.1, h.2.1⟩

theorem noBranch_faces (R : RelativeFamily (V := V)) (v : V) :
    (R.noBranch v).F = R.A v := by
  classical
  ext s
  simp only [F, noBranch, Finset.mem_sdiff, Finset.mem_filter, mem_A]
  constructor
  · rintro ⟨⟨he, hv⟩, hn⟩
    exact ⟨⟨he, fun hd => hn ⟨he, hv, Or.inl hd⟩⟩, hv,
      fun hu => hn ⟨he, hv, Or.inr hu⟩⟩
  · rintro ⟨⟨he, hd⟩, hv, hu⟩
    exact ⟨⟨he, hv⟩, fun h => h.2.2.elim hd hu⟩

theorem yesBranch_faces (R : RelativeFamily (V := V)) (v : V) :
    (R.yesBranch v).F = R.B v := by
  classical
  ext s
  simp only [F, yesBranch, Finset.mem_sdiff, Finset.mem_filter, mem_B]
  constructor
  · rintro ⟨⟨he, her⟩, hn⟩
    refine ⟨⟨he, fun hd => hn ⟨he, her, Or.inr hd⟩⟩, ?_, her⟩
    by_contra hv
    exact hn ⟨he, her, Or.inl hv⟩
  · rintro ⟨⟨he, hd⟩, hv, her⟩
    exact ⟨⟨he, her⟩, fun h => h.2.2.elim (fun hnv => hnv hv) hd⟩

end RelativeFamily

/-- The exact augmented/native bridge used by the nonempty greedy algorithm. -/
def nativeRelative (K : PreAbstractSimplicialComplex V) : RelativeFamily (V := V) where
  E := insert ∅ (faceSet K)
  D := {∅}
  downE := by
    intro s hs t hts
    rcases Finset.mem_insert.mp hs with rfl | hs
    · have ht : t = ∅ := Finset.subset_empty.mp hts
      simpa only [ht] using (Finset.mem_insert_self (∅ : Finset V) (faceSet K))
    · by_cases ht : t = ∅
      · simpa only [ht] using (Finset.mem_insert_self (∅ : Finset V) (faceSet K))
      · exact Finset.mem_insert_of_mem ((mem_faceSet K t).mpr
          ((K.isRelLowerSet_faces ((mem_faceSet K s).mp hs)).2 hts
            (Finset.nonempty_iff_ne_empty.mpr ht)))
  downD := by
    intro s hs t hts
    have hs0 : s = ∅ := Finset.mem_singleton.mp hs
    have ht0 : t = ∅ := Finset.subset_empty.mp (hs0 ▸ hts)
    exact Finset.mem_singleton.mpr ht0
  inclusion := by
    intro s hs
    simpa only [Finset.mem_singleton.mp hs] using
      (Finset.mem_insert_self (∅ : Finset V) (faceSet K))

theorem nativeRelative_faces (K : PreAbstractSimplicialComplex V) :
    (nativeRelative K).F = faceSet K := by
  classical
  have hn : (∅ : Finset V) ∉ faceSet K := by
    intro h
    exact Finset.not_nonempty_empty
      ((K.isRelLowerSet_faces ((mem_faceSet K ∅).mp h)).1)
  ext s
  simp only [RelativeFamily.F, nativeRelative, Finset.mem_sdiff,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | hs, hne⟩
    · exact (hne rfl).elim
    · exact hs
  · intro hs
    exact ⟨Or.inr hs, fun he => hn (he ▸ hs)⟩

end D5.S3.Geometry.FiniteCoordinateGreedyMatching
