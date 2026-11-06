/- GID: D5/S3/Geometry/FiniteGreedyFamilyTransport
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGreedyFamilyTransport
   mirror-E: none(waiver:finite-greedy-family-transport)
   anchors: [mathlib/module/Mathlib.Data.Finset.Basic]
   utility: none
   digest: Exact coordinate rounds commute with injective toggle maps, including original-label complementation. -/
import D5.S3.Geometry.FiniteCoordinateGreedyMatching

/-! UNCOMPILED source. Families in this module are augmented finite families,
not native complexes. In particular {∅} is never identified with ∅. -/

noncomputable section
open Finset

namespace D5.S3.Geometry.FiniteGreedyFamilyTransport
open FiniteCoordinateGreedyMatching

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def flip (v : V) (a : Finset V) : Finset V :=
  if v ∈ a then a.erase v else insert v a

@[simp] theorem mem_flip (v x : V) (a : Finset V) :
    x ∈ flip v a ↔ (x = v ∧ v ∉ a) ∨ (x ≠ v ∧ x ∈ a) := by
  by_cases hv : v ∈ a <;> by_cases hx : x = v <;> simp [flip, hv, hx]

@[simp] theorem flip_flip (v : V) (a : Finset V) : flip v (flip v a) = a := by
  ext x
  by_cases hx : x = v <;> by_cases hv : v ∈ a <;> simp [hx, hv]

private theorem mem_paired (F : Finset (Finset V)) (v : V) (a : Finset V) :
    a ∈ pairedFaces F v ↔ a ∈ F ∧ flip v a ∈ F := by
  by_cases hv : v ∈ a
  · have hi : insert v (a.erase v) = a := Finset.insert_erase hv
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · exact (((mem_lowers F v a).mp h).2.1 hv).elim
      · obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp h
        obtain ⟨hbF, hbv, hiF⟩ := (mem_lowers F v b).mp hb
        have he : a.erase v = b := by
          rw [← hba]
          simp [hbv]
        exact ⟨hba ▸ hiF, by simpa [flip, hv, he] using hbF⟩
    · rintro ⟨ha, hb⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨a.erase v, (mem_lowers F v _).mpr
          ⟨by simpa [flip, hv] using hb, Finset.notMem_erase _ _, hi.symm ▸ ha⟩, hi⟩)
  · constructor
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨ha, _, hb⟩ := (mem_lowers F v a).mp h
        exact ⟨ha, by simpa [flip, hv] using hb⟩
      · obtain ⟨b, _, he⟩ := Finset.mem_image.mp h
        exact (hv (he ▸ Finset.mem_insert_self v b)).elim
    · rintro ⟨ha, hb⟩
      exact Finset.mem_union_left _ ((mem_lowers F v a).mpr
        ⟨ha, hv, by simpa [flip, hv] using hb⟩)

@[simp] theorem mem_remaining (F : Finset (Finset V)) (v : V) (a : Finset V) :
    a ∈ remaining F v ↔ a ∈ F ∧ flip v a ∉ F := by
  rw [remaining, Finset.mem_sdiff, mem_paired]
  tauto

theorem remaining_image (F : Finset (Finset V)) (u : V) (v : W)
    (f : Finset V → Finset W) (hf : Function.Injective f)
    (hc : ∀ a, flip v (f a) = f (flip u a)) :
    remaining (F.image f) v = (remaining F u).image f := by
  ext b
  constructor
  · intro h
    obtain ⟨hb, hn⟩ := (mem_remaining _ _ _).mp h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨a, (mem_remaining _ _ _).mpr ⟨ha, ?_⟩, rfl⟩
    intro ht
    apply hn
    rw [hc]
    exact Finset.mem_image.mpr ⟨flip u a, ht, rfl⟩
  · rintro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ha, hn⟩ := (mem_remaining _ _ _).mp ha
    refine (mem_remaining _ _ _).mpr ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    intro ht
    obtain ⟨c, hcF, he⟩ := Finset.mem_image.mp ht
    have hec : c = flip u a := hf (he.trans (hc a))
    exact hn (hec ▸ hcF)

theorem survivors_image (F : Finset (Finset V)) (vs : List V)
    (f : Finset V → Finset W) (g : V → W) (hf : Function.Injective f)
    (hc : ∀ v ∈ vs, ∀ a, flip (g v) (f a) = f (flip v a)) :
    survivors (F.image f) (vs.map g) = (survivors F vs).image f := by
  induction vs generalizing F with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, survivors]
    rw [remaining_image F v (g v) f hf (hc v (by simp))]
    exact ih _ (fun w hw => hc w (by simp [hw]))

private theorem flip_map (e : V ↪ W) (v : V) (a : Finset V) :
    flip (e v) (a.map e) = (flip v a).map e := by
  by_cases hv : v ∈ a
  · have hev : e v ∈ a.map e := Finset.mem_map.mpr ⟨v, hv, rfl⟩
    simp only [flip, if_pos hv, if_pos hev]
    ext x
    simp only [Finset.mem_erase, Finset.mem_map]
    constructor
    · rintro ⟨hx, y, hy, rfl⟩
      exact ⟨y, ⟨fun he => hx (congrArg e he), hy⟩, rfl⟩
    · rintro ⟨y, ⟨hyv, hy⟩, rfl⟩
      exact ⟨fun he => hyv (e.injective he), y, hy, rfl⟩
  · have hev : e v ∉ a.map e := by simpa using hv
    simp [flip, hv, hev, Finset.map_insert]

theorem survivors_map (e : V ↪ W) (F : Finset (Finset V)) (vs : List V) :
    survivors (F.image (Finset.map e)) (vs.map e) =
      (survivors F vs).image (Finset.map e) :=
  survivors_image F vs _ e (Finset.map_injective e) (fun v _ => flip_map e v)

def complementMap (e : V ↪ W) (a : Finset V) : Finset W :=
  (Finset.univ \ a).map e

private theorem complementMap_injective (e : V ↪ W) :
    Function.Injective (complementMap e) := by
  intro a b hab
  have he : Finset.univ \ a = Finset.univ \ b := Finset.map_injective e hab
  ext x
  have hx := Finset.ext_iff.mp he x
  simpa using not_congr hx

private theorem complementMap_flip (e : V ↪ W) (v : V) (a : Finset V) :
    flip (e v) (complementMap e a) = complementMap e (flip v a) := by
  unfold complementMap
  rw [flip_map]
  congr 1
  ext x
  by_cases hx : x = v <;> by_cases hv : v ∈ a <;> simp [hx, hv]

/-- Each actual remaining round is conjugate, with the original vertex label.
Complements reverse the lower/upper orientation but preserve the deleted pair. -/
theorem remaining_complement (e : V ↪ W) (F : Finset (Finset V)) (v : V) :
    remaining (F.image (complementMap e)) (e v) =
      (remaining F v).image (complementMap e) :=
  remaining_image F v (e v) _ (complementMap_injective e) (complementMap_flip e v)

theorem survivors_complement (e : V ↪ W) (F : Finset (Finset V)) (vs : List V) :
    survivors (F.image (complementMap e)) (vs.map e) =
      (survivors F vs).image (complementMap e) :=
  survivors_image F vs _ e (complementMap_injective e) (fun v _ => complementMap_flip e v)

/-- Toggle-separated families have no cross-branch pairs at this coordinate. -/
theorem remaining_union (A B : Finset (Finset V)) (v : V)
    (hab : ∀ a ∈ A, flip v a ∉ B) (hba : ∀ b ∈ B, flip v b ∉ A) :
    remaining (A ∪ B) v = remaining A v ∪ remaining B v := by
  ext a
  simp only [mem_remaining, Finset.mem_union, not_or]
  constructor
  · rintro ⟨ha | hb, hnA, hnB⟩
    · exact Or.inl ⟨ha, hnA⟩
    · exact Or.inr ⟨hb, hnB⟩
  · rintro (⟨ha, hn⟩ | ⟨hb, hn⟩)
    · exact ⟨Or.inl ha, hn, hab a ha⟩
    · exact ⟨Or.inr hb, hba a hb, hn⟩

theorem survivors_union (A B : Finset (Finset V)) (vs : List V)
    (hab : ∀ v ∈ vs, ∀ a ∈ A, flip v a ∉ B)
    (hba : ∀ v ∈ vs, ∀ b ∈ B, flip v b ∉ A) :
    survivors (A ∪ B) vs = survivors A vs ∪ survivors B vs := by
  induction vs generalizing A B with
  | nil => rfl
  | cons v vs ih =>
    simp only [survivors]
    rw [remaining_union A B v (hab v (by simp)) (hba v (by simp))]
    exact ih _ _
      (fun w hw a ha ht => hab w (by simp [hw]) a (remaining_subset A v ha)
        (remaining_subset B v ht))
      (fun w hw b hb ht => hba w (by simp [hw]) b (remaining_subset B v hb)
        (remaining_subset A v ht))

theorem survivors_by_pin (A B : Finset (Finset V)) (vs : List V) (p : V)
    (ha : ∀ a ∈ A, p ∉ a) (hb : ∀ b ∈ B, p ∈ b) (hp : p ∉ vs) :
    survivors (A ∪ B) vs = survivors A vs ∪ survivors B vs := by
  apply survivors_union
  · intro v hv a ham hbm
    have hpv : p ≠ v := fun he => hp (he.symm ▸ hv)
    have hpin : p ∈ flip v a := hb _ hbm
    have hpa : p ∉ a := ha a ham
    simpa [hpv, hpa] using hpin
  · intro v hv b hbm ham
    have hpv : p ≠ v := fun he => hp (he.symm ▸ hv)
    have hpin : p ∉ flip v b := ha _ ham
    have hpb : p ∈ b := hb b hbm
    exact hpin (by simp [hpv, hpb])

theorem remaining_of_fixed (F : Finset (Finset V)) (v : V)
    (h : (∀ a ∈ F, v ∈ a) ∨ (∀ a ∈ F, v ∉ a)) : remaining F v = F := by
  ext a
  rw [mem_remaining]
  constructor
  · exact And.left
  · intro ha
    refine ⟨ha, ?_⟩
    intro ht
    rcases h with h | h
    · have hp := h a ha
      have hn := h _ ht
      simpa [hp] using hn
    · have hp := h a ha
      have hn := h _ ht
      exact hn (by simp [hp])

private theorem flip_insert (v w : V) (hvw : v ≠ w) (a : Finset V) :
    flip v (insert w a) = insert w (flip v a) := by
  ext x
  by_cases hxv : x = v
  · subst x
    simp [hvw]
  · simp [hxv]

theorem remaining_insert (F : Finset (Finset V)) (v w : V) (hvw : v ≠ w)
    (hw : ∀ a ∈ F, w ∉ a) :
    remaining (F.image (insert w)) v = (remaining F v).image (insert w) := by
  ext b
  constructor
  · intro h
    obtain ⟨hb, hn⟩ := (mem_remaining _ _ _).mp h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨a, (mem_remaining _ _ _).mpr ⟨ha, ?_⟩, rfl⟩
    intro ht
    apply hn
    rw [flip_insert v w hvw]
    exact Finset.mem_image.mpr ⟨flip v a, ht, rfl⟩
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ha, hn⟩ := (mem_remaining _ _ _).mp ha
    refine (mem_remaining _ _ _).mpr ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    intro ht
    obtain ⟨c, hc, he⟩ := Finset.mem_image.mp ht
    rw [flip_insert v w hvw] at he
    have hwa := hw a ha
    have hwc := hw c hc
    have hwt : w ∉ flip v a := by simp [Ne.symm hvw, hwa]
    have hec : c = flip v a := by
      have h := congrArg (fun a : Finset V => a.erase w) he
      simpa [hwc, hwt] using h
    exact hn (hec ▸ hc)

theorem survivors_insert (F : Finset (Finset V)) (vs : List V) (w : V)
    (hw : ∀ a ∈ F, w ∉ a) (hvs : w ∉ vs) :
    survivors (F.image (insert w)) vs = (survivors F vs).image (insert w) := by
  induction vs generalizing F with
  | nil => rfl
  | cons v vs ih =>
    have hvw : v ≠ w := by intro he; exact hvs (by simp [he])
    simp only [survivors]
    rw [remaining_insert F v w hvw hw]
    exact ih _ (fun a ha => hw a (remaining_subset F v ha))
      (fun h => hvs (by simp [h]))

/-- Computational presentation of the SAME survivors. This definition avoids
the classical decidability local to the frozen owner's `lowers`; it is used
only for closed finite base proofs, with the equivalence proved below. -/
def computeSurvivors (F : Finset (Finset V)) : List V → Finset (Finset V)
  | [] => F
  | v :: vs => computeSurvivors (F.filter fun a => flip v a ∉ F) vs

theorem computeSurvivors_eq (F : Finset (Finset V)) (vs : List V) :
    computeSurvivors F vs = survivors F vs := by
  induction vs generalizing F with
  | nil => rfl
  | cons v vs ih =>
    have he : (F.filter fun a => flip v a ∉ F) = remaining F v := by
      ext a
      simp only [Finset.mem_filter, mem_remaining]
    change computeSurvivors _ vs = survivors (remaining F v) vs
    rw [he, ih]

end D5.S3.Geometry.FiniteGreedyFamilyTransport
