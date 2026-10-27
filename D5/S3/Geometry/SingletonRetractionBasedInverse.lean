/- GID: D5/S3/Geometry/SingletonRetractionBasedInverse
   generality: G
   mirror-B: D5/B/S3/Geometry/SingletonRetractionBasedInverse
   mirror-E: none(waiver:singleton-retraction-based-inverse)
   anchors: [mathlib/module/Mathlib.Topology.Homotopy.Basic]
   utility: none
   digest: Singleton-cylinder retractions construct both relative inverse homotopies. -/
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Piecewise
import Mathlib.Tactic

/-!
# Based inverses from singleton-cylinder retractions

The classical cofiber homotopy equivalence theorem, in its one-point case
(May, A Concise Course in Algebraic Topology, Chapter 6, section 5), is
constructed directly on the supplied topological carriers. The square
retraction is explicit. No homotopy extension or loop contraction hypothesis
is added to the input.
-/

noncomputable section

open Set Topology ContinuousMap
open scoped unitInterval

namespace D5.S3.Geometry.SingletonRetractionBasedInverse

variable {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace W]

/-- A map into the actual bottom-or-point cylinder, fixing that subspace. -/
structure CylinderRetraction (p : Z) where
  map : C(Z × I, {z : Z × I | z.2 = 0 ∨ z.1 = p})
  fixed : ∀ z, (z.2 = 0 ∨ z.1 = p) → (map z).val = z

private def sides : Set (I × I) := {q | q.2 = 0 ∨ q.1 = 0 ∨ q.1 = 1}

private def depth (q : I × I) : ℝ := max (1 - (q.2 : ℝ) / 2) |2 * (q.1 : ℝ) - 1|

private def rhoT (q : I × I) : ℝ := 1 / 2 + ((q.1 : ℝ) - 1 / 2) / depth q

private def rhoS (q : I × I) : ℝ := 2 + ((q.2 : ℝ) - 2) / depth q

private theorem geometry (q : I × I) :
    0 < depth q ∧ depth q ≤ 1 ∧
    0 ≤ rhoT q ∧ rhoT q ≤ 1 ∧ 0 ≤ rhoS q ∧ rhoS q ≤ 1 ∧
    (rhoS q = 0 ∨ rhoT q = 0 ∨ rhoT q = 1) ∧
    depth q * rhoT q + (1 - depth q) / 2 = (q.1 : ℝ) ∧
    depth q * rhoS q + 2 * (1 - depth q) = (q.2 : ℝ) := by
  obtain ⟨ht0, ht1⟩ := q.1.property
  obtain ⟨hs0, hs1⟩ := q.2.property
  have hd : 1 / 2 ≤ depth q := (by linarith : (1 / 2 : ℝ) ≤ 1 - (q.2 : ℝ) / 2).trans
    (le_max_left _ _)
  have hd0 : 0 < depth q := by linarith
  have hd1 : depth q ≤ 1 := max_le (by linarith) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have ha : |2 * (q.1 : ℝ) - 1| ≤ depth q := le_max_right _ _
  have hb : 1 - (q.2 : ℝ) / 2 ≤ depth q := le_max_left _ _
  have hat := (abs_le.mp ha)
  have hrt : depth q * rhoT q + (1 - depth q) / 2 = (q.1 : ℝ) := by
    dsimp [rhoT]
    field_simp [ne_of_gt hd0]
    ring
  have hrs : depth q * rhoS q + 2 * (1 - depth q) = (q.2 : ℝ) := by
    dsimp [rhoS]
    field_simp [ne_of_gt hd0]
    ring
  have et : rhoT q = (depth q + 2 * (q.1 : ℝ) - 1) / (2 * depth q) := by
    unfold rhoT
    field_simp [ne_of_gt hd0]
    ring
  have es : rhoS q = (2 * depth q + (q.2 : ℝ) - 2) / depth q := by
    unfold rhoS
    field_simp [ne_of_gt hd0]
    ring
  have rt0 : 0 ≤ rhoT q := by rw [et]; exact div_nonneg (by linarith) (by positivity)
  have rt1 : rhoT q ≤ 1 := by
    rw [et]; apply (div_le_iff₀ (by positivity : 0 < 2 * depth q)).mpr; linarith
  have rs0 : 0 ≤ rhoS q := by rw [es]; exact div_nonneg (by linarith) hd0.le
  have rs1 : rhoS q ≤ 1 := by
    rw [es]; apply (div_le_iff₀ hd0).mpr; linarith
  refine ⟨hd0, hd1, rt0, rt1, rs0, rs1, ?_, hrt, hrs⟩
  by_cases h : |2 * (q.1 : ℝ) - 1| ≤ 1 - (q.2 : ℝ) / 2
  · left
    have he : depth q = 1 - (q.2 : ℝ) / 2 := max_eq_left h
    have hz : depth q * rhoS q = 0 := by nlinarith
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hd0)
  · right
    have he : depth q = |2 * (q.1 : ℝ) - 1| := max_eq_right (le_of_not_ge h)
    rcases le_total 0 (2 * (q.1 : ℝ) - 1) with ht' | ht'
    · right
      rw [abs_of_nonneg ht'] at he
      have hz : depth q * (rhoT q - 1) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hd0))
    · left
      rw [abs_of_nonpos ht'] at he
      have hz : depth q * rhoT q = 0 := by nlinarith
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hd0)

private theorem depth_on_sides (q : I × I) (hq : q ∈ sides) : depth q = 1 := by
  have habs : |2 * (q.1 : ℝ) - 1| ≤ 1 :=
    abs_le.mpr ⟨by linarith [q.1.property.1], by linarith [q.1.property.2]⟩
  have hbase : 1 - (q.2 : ℝ) / 2 ≤ 1 := by linarith [q.2.property.1]
  rcases hq with h | h | h
  · simpa [depth, h] using max_eq_left habs
  · norm_num [depth, h, max_eq_right hbase]
  · norm_num [depth, h, max_eq_right hbase]

private def level (q : I × I) : I := ⟨1 - depth q, by
  obtain ⟨hd, hd1, _⟩ := geometry q
  exact ⟨by linarith, by linarith⟩⟩

private theorem continuous_depth : Continuous depth := by unfold depth; fun_prop
private theorem continuous_level : Continuous level := by
  apply Continuous.subtype_mk
  exact continuous_const.sub continuous_depth
private theorem continuous_rhoT : Continuous rhoT := by
  unfold rhoT
  have h : Continuous (fun q : I × I => (q.1 : ℝ) - 1 / 2) := by fun_prop
  exact continuous_const.add (h.div continuous_depth (fun q => ne_of_gt (geometry q).1))
private theorem continuous_rhoS : Continuous rhoS := by
  unfold rhoS
  have h : Continuous (fun q : I × I => (q.2 : ℝ) - 2) := by fun_prop
  exact continuous_const.add (h.div continuous_depth (fun q => ne_of_gt (geometry q).1))

variable {p : Z}

private def squareAmount (R : CylinderRetraction p) (z : Z × (I × I)) : ℝ :=
  min ((R.map (z.1, level z.2)).val.2 : ℝ) (level z.2 : ℝ)

private theorem amount_bounds (R : CylinderRetraction p) (z : Z × (I × I)) :
    0 ≤ squareAmount R z ∧ squareAmount R z ≤ 1 - depth z.2 := by
  exact ⟨le_min (R.map (z.1, level z.2)).val.2.property.1 (level z.2).property.1,
    min_le_right _ _⟩

private def squarePoint (R : CylinderRetraction p) (z : Z × (I × I)) : I × I := by
  let a := squareAmount R z
  obtain ⟨hd, hd1, ht0, ht1, hs0, hs1, _, hqt, hqs⟩ := geometry z.2
  have ha := amount_bounds R z
  refine (⟨(1 - a) * rhoT z.2 + a / 2, ?_⟩,
    ⟨(1 - a) * rhoS z.2 + 2 * a, ?_⟩)
  · have ha1 : 0 ≤ 1 - a := by dsimp [a]; linarith
    constructor
    · exact add_nonneg (mul_nonneg ha1 ht0) (div_nonneg ha.1 (by norm_num))
    · nlinarith [mul_nonneg ha1 (sub_nonneg.mpr ht1)]
  · have ha1 : 0 ≤ 1 - a := by dsimp [a]; linarith
    constructor
    · exact add_nonneg (mul_nonneg ha1 hs0) (mul_nonneg (by norm_num) ha.1)
    · have hprod := mul_nonneg (sub_nonneg.mpr ha.2)
        (show 0 ≤ 2 - rhoS z.2 by linarith)
      nlinarith [z.2.2.property.2]

/-- The three square sides, together with the entire square over the basepoint. -/
def SquareBoundary (p : Z) : Set (Z × (I × I)) :=
  {z | z.2 ∈ sides ∨ z.1 = p}

private def squareRaw (R : CylinderRetraction p) (z : Z × (I × I)) : Z × (I × I) :=
  ((R.map (z.1, level z.2)).val.1, squarePoint R z)

private theorem squareRaw_mem (R : CylinderRetraction p) (z : Z × (I × I)) :
    squareRaw R z ∈ SquareBoundary p := by
  by_cases ha : squareAmount R z = 0
  · left
    obtain ⟨_, _, _, _, _, _, h, _⟩ := geometry z.2
    rcases h with h | h | h
    · left; apply Subtype.ext; simpa [squareRaw, squarePoint, ha] using h
    · right; left; apply Subtype.ext; simpa [squareRaw, squarePoint, ha] using h
    · right; right; apply Subtype.ext; simpa [squareRaw, squarePoint, ha] using h
  · right
    rcases (R.map (z.1, level z.2)).property with ht | hp
    · exact (ha (by simp [squareAmount, ht, min_eq_left (level z.2).property.1])).elim
    · exact hp

private theorem continuous_squareRaw (R : CylinderRetraction p) : Continuous (squareRaw R) := by
  have hR : Continuous (fun z : Z × (I × I) => (R.map (z.1, level z.2)).val) :=
    continuous_subtype_val.comp (R.map.continuous.comp
      (continuous_fst.prodMk (continuous_level.comp continuous_snd)))
  have ha : Continuous (squareAmount R) :=
    (continuous_subtype_val.comp (continuous_snd.comp hR)).min
      (continuous_subtype_val.comp (continuous_level.comp continuous_snd))
  refine (continuous_fst.comp hR).prodMk ?_
  apply Continuous.prodMk <;> apply Continuous.subtype_mk
  · exact ((continuous_const.sub ha).mul (continuous_rhoT.comp continuous_snd)).add
      (ha.div_const 2)
  · exact ((continuous_const.sub ha).mul (continuous_rhoS.comp continuous_snd)).add
      (continuous_const.mul ha)

private theorem squareRaw_fixed (R : CylinderRetraction p) (z : Z × (I × I))
    (hz : z ∈ SquareBoundary p) : squareRaw R z = z := by
  obtain ⟨hd, _, _, _, _, _, _, hqt, hqs⟩ := geometry z.2
  rcases hz with hq | hp
  · have hd1 := depth_on_sides z.2 hq
    have hl : level z.2 = 0 := Subtype.ext (by simp [level, hd1])
    have hr := R.fixed (z.1, 0) (Or.inl rfl)
    have ha : squareAmount R z = 0 := by simp [squareAmount, hl, hr]
    apply Prod.ext
    · simp [squareRaw, hl, hr]
    · apply Prod.ext <;> apply Subtype.ext
      · simpa [squareRaw, squarePoint, ha, hd1] using hqt
      · simpa [squareRaw, squarePoint, ha, hd1] using hqs
  · have hr := R.fixed (z.1, level z.2) (Or.inr hp)
    have ha : squareAmount R z = 1 - depth z.2 := by
      unfold squareAmount
      rw [hr]
      exact min_self _
    apply Prod.ext
    · simp [squareRaw, hr]
    · apply Prod.ext <;> apply Subtype.ext
      · simpa [squareRaw, squarePoint, ha] using hqt
      · simpa [squareRaw, squarePoint, ha] using hqs

/-- Radial projection from `(1/2,2)` combined with the supplied cylinder retraction. -/
def squareRetraction (R : CylinderRetraction p) :
    {S : C(Z × (I × I), SquareBoundary p) //
      ∀ z : SquareBoundary p, (S z.val).val = z.val} :=
  ⟨⟨fun z => ⟨squareRaw R z, squareRaw_mem R z⟩,
      continuous_squareRaw R |>.subtype_mk _⟩,
    fun z => squareRaw_fixed R z.val z.property⟩

private theorem closed_pasting {D : Type*} [TopologicalSpace D]
    (A B : Set D) (hA : IsClosed A) (hB : IsClosed B) (hc : A ∪ B = univ)
    (f : D → W) (hf : ContinuousOn f A) (hg : ContinuousOn f B) : Continuous f := by
  rw [← continuousOn_univ, ← hc]
  exact hf.union_of_isClosed hg hA hB

private def extensionBoundary (p : Z) (f : C(Z, W)) (η : C(I, W)) :
    {z : Z × I | z.2 = 0 ∨ z.1 = p} → W :=
  fun z => if z.val.2 = 0 then f z.val.1 else η z.val.2

private theorem continuous_extensionBoundary [T1Space Z] (p : Z)
    (f : C(Z, W)) (η : C(I, W)) (hη : η 0 = f p) :
    Continuous (extensionBoundary p f η) := by
  let A : Set {z : Z × I | z.2 = 0 ∨ z.1 = p} := {z | z.val.2 = 0}
  let B : Set {z : Z × I | z.2 = 0 ∨ z.1 = p} := {z | z.val.1 = p}
  apply closed_pasting A B
    (isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const)
    (isClosed_singleton.preimage (continuous_fst.comp continuous_subtype_val))
    (by ext z; exact iff_true_intro z.property)
  · apply (f.continuous.comp (continuous_fst.comp continuous_subtype_val)).continuousOn.congr
    intro z hz
    simp [extensionBoundary, show z.val.2 = 0 from hz]
  · apply (η.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn.congr
    intro z hz
    by_cases ht : z.val.2 = 0
    · simp [extensionBoundary, ht, show z.val.1 = p from hz, hη]
    · simp [extensionBoundary, ht]

private def extendPath [T1Space Z] (R : CylinderRetraction p)
    (f : C(Z, W)) (η : C(I, W)) (hη : η 0 = f p) :
    {E : C(Z × I, W) // (∀ z, E (z, 0) = f z) ∧ ∀ t, E (p, t) = η t} := by
  let D : C({z : Z × I | z.2 = 0 ∨ z.1 = p}, W) :=
    ⟨extensionBoundary p f η, continuous_extensionBoundary p f η hη⟩
  refine ⟨D.comp R.map, ?_, ?_⟩
  · intro z
    change extensionBoundary p f η (R.map (z, 0)) = f z
    simp [extensionBoundary, R.fixed (z, 0) (Or.inl rfl)]
  · intro t
    change extensionBoundary p f η (R.map (p, t)) = η t
    simp only [extensionBoundary, R.fixed (p, t) (Or.inr rfl)]
    split_ifs with ht
    · simpa [ht] using hη.symm
    · rfl

private def straightBoundary {a b : C(Z, W)} (p : Z) (_w : W)
    (P : a.Homotopy b) (N : C(I × I, W)) : SquareBoundary p → W :=
  fun z => if z.val.2.2 = 0 then P (z.val.2.1, z.val.1)
    else if z.val.2.1 = 0 then a z.val.1
    else if z.val.2.1 = 1 then b z.val.1 else N z.val.2

private theorem continuous_straightBoundary [T1Space Z] {a b : C(Z, W)}
    (p : Z) (w : W) (P : a.Homotopy b) (N : C(I × I, W))
    (ha : a p = w) (hb : b p = w)
    (hN0 : ∀ t, N (t, 0) = P (t, p))
    (hNl : ∀ s, N (0, s) = w) (hNr : ∀ s, N (1, s) = w) :
    Continuous (straightBoundary p w P N) := by
  let A : Set (SquareBoundary p) := {z | z.val.2.2 = 0}
  let B : Set (SquareBoundary p) := {z | z.val.2.1 = 0}
  let C : Set (SquareBoundary p) := {z | z.val.2.1 = 1}
  let D : Set (SquareBoundary p) := {z | z.val.1 = p}
  have hA : IsClosed A := isClosed_eq (by fun_prop) continuous_const
  have hB : IsClosed B := isClosed_eq (by fun_prop) continuous_const
  have hC : IsClosed C := isClosed_eq (by fun_prop) continuous_const
  have hD : IsClosed D := isClosed_singleton.preimage (by fun_prop)
  have hfA : ContinuousOn (straightBoundary p w P N) A := by
    have hc : Continuous (fun z : SquareBoundary p => P (z.val.2.1, z.val.1)) :=
      P.continuous.comp (by fun_prop)
    apply hc.continuousOn.congr
    intro z hz
    simp [straightBoundary, show z.val.2.2 = 0 from hz]
  have hfB : ContinuousOn (straightBoundary p w P N) B := by
    have hc : Continuous (fun z : SquareBoundary p => a z.val.1) :=
      a.continuous.comp (by fun_prop)
    apply hc.continuousOn.congr
    intro z hz
    simp [straightBoundary, show z.val.2.1 = 0 from hz]
  have hfC : ContinuousOn (straightBoundary p w P N) C := by
    have hc : Continuous (fun z : SquareBoundary p => b z.val.1) :=
      b.continuous.comp (by fun_prop)
    apply hc.continuousOn.congr
    intro z hz
    simp [straightBoundary, show z.val.2.1 = 1 from hz]
  have hfD : ContinuousOn (straightBoundary p w P N) D := by
    have hc : Continuous (fun z : SquareBoundary p => N z.val.2) :=
      N.continuous.comp (by fun_prop)
    apply hc.continuousOn.congr
    intro z hz
    have hp : z.val.1 = p := hz
    dsimp [straightBoundary]
    split_ifs with hs ht ht
    · have he : z.val.2 = (z.val.2.1, 0) := Prod.ext rfl hs
      rw [hp, he, hN0]
    · have he : z.val.2 = (0, z.val.2.2) := Prod.ext ht rfl
      rw [he, hNl, hp, ha]
    · have he : z.val.2 = (1, z.val.2.2) := Prod.ext ht rfl
      rw [he, hNr, hp, hb]
    · rfl
  have hcover : (A ∪ B ∪ C) ∪ D = univ := by
    ext z
    apply iff_true_intro
    rcases z.property with (h | h | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  apply closed_pasting (A ∪ B ∪ C) D ((hA.union hB).union hC) hD hcover
  · exact (hfA.union_of_isClosed hfB hA hB).union_of_isClosed hfC (hA.union hB) hC
  · exact hfD

private def straighten [T1Space Z] (R : CylinderRetraction p)
    {a b : C(Z, W)} (w : W) (P : a.Homotopy b) (N : C(I × I, W))
    (ha : a p = w) (hb : b p = w)
    (hN0 : ∀ t, N (t, 0) = P (t, p)) (hN1 : ∀ t, N (t, 1) = w)
    (hNl : ∀ s, N (0, s) = w) (hNr : ∀ s, N (1, s) = w) :
    a.HomotopyRel b {p} := by
  let S := squareRetraction R
  let D : C(SquareBoundary p, W) :=
    ⟨straightBoundary p w P N,
      continuous_straightBoundary p w P N ha hb hN0 hNl hNr⟩
  let E := D.comp S.val
  have hE (z : Z × (I × I)) (hz : z ∈ SquareBoundary p) :
      E z = straightBoundary p w P N ⟨z, hz⟩ := by
    change D (S.val z) = D ⟨z, hz⟩
    congr 1
    exact Subtype.ext (S.property ⟨z, hz⟩)
  refine { toFun := fun z => E (z.2, (z.1, 1))
           continuous_toFun := E.continuous.comp (by fun_prop)
           map_zero_left := ?_
           map_one_left := ?_
           prop' := ?_ }
  · intro z
    rw [hE _ (Or.inl (Or.inr (Or.inl rfl)))]
    simp [straightBoundary]
  · intro z
    rw [hE _ (Or.inl (Or.inr (Or.inr rfl)))]
    simp [straightBoundary]
  · intro t z hz
    have hz' : z = p := hz
    subst z
    change E (p, (t, 1)) = a p
    rw [hE _ (Or.inr rfl)]
    simp only [straightBoundary, one_ne_zero, ite_false]
    split_ifs with ht ht
    · rfl
    · exact hb.trans ha.symm
    · exact (hN1 t).trans ha.symm

private theorem moveMap [T1Space Z] (R : CylinderRetraction p)
    (f : C(Z, W)) (η : C(I, W)) (hη : η 0 = f p) :
    ∃ F : C(Z, W), ∃ A : f.Homotopy F, ∀ t, A (t, p) = η t := by
  let E := extendPath R f η hη
  let F : C(Z, W) := ⟨fun z => E.val (z, 1), E.val.continuous.comp (by fun_prop)⟩
  refine ⟨F, { toFun := fun z => E.val (z.2, z.1)
               continuous_toFun := E.val.continuous.comp continuous_swap
               map_zero_left := E.property.1
               map_one_left := fun _ => rfl }, E.property.2⟩

private def contractionParameter (b : C(I, I)) : C(I × I, I) :=
  ⟨fun q => ⟨(q.2 : ℝ) + (1 - (q.2 : ℝ)) * (b q.1 : ℝ), by
    have hs := q.2.property
    have hb := (b q.1).property
    constructor
    · exact add_nonneg hs.1 (mul_nonneg (sub_nonneg.mpr hs.2) hb.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hb.2)]⟩, by fun_prop⟩

private def cancelTrace [T1Space Z] (R : CylinderRetraction p)
    {a b : C(Z, W)} (w : W) (P : a.Homotopy b)
    (δ : C(I, W)) (r : C(I, I)) (ha : a p = w) (hb : b p = w)
    (hδ : δ 1 = w) (hr0 : r 0 = 1) (hr1 : r 1 = 1)
    (htrace : ∀ t, P (t, p) = δ (r t)) : a.HomotopyRel b {p} := by
  let N := δ.comp (contractionParameter r)
  apply straighten R w P N ha hb
  · intro t
    simpa [N, contractionParameter] using (htrace t).symm
  · intro t
    simpa [N, contractionParameter] using hδ
  · intro s
    have he : contractionParameter r (0, s) = 1 := by
      apply Subtype.ext
      simp [contractionParameter, hr0]
    simpa [N, he] using hδ
  · intro s
    have he : contractionParameter r (1, s) = 1 := by
      apply Subtype.ext
      simp [contractionParameter, hr1]
    simpa [N, he] using hδ

private def backtrack : C(I, I) :=
  ⟨fun t => ⟨|2 * (t : ℝ) - 1|, abs_nonneg _, abs_le.mpr
    ⟨by linarith [t.property.1], by linarith [t.property.2]⟩⟩, by fun_prop⟩

private def pausedBacktrack : C(I, I) :=
  ⟨fun t => ⟨max (max (1 - 4 * (t : ℝ)) 0) (2 * (t : ℝ) - 1),
    (le_max_right (1 - 4 * (t : ℝ)) 0).trans (le_max_left _ _),
    max_le (max_le (by linarith [t.property.1]) zero_le_one)
      (by linarith [t.property.2])⟩, by fun_prop⟩

/-- Both maps and both point-fixed inverse homotopies, on the original spaces. -/
structure BasedEquivalence (x : X) (y : Y) where
  forward : C(X, Y)
  backward : C(Y, X)
  forward_point : forward x = y
  backward_point : backward y = x
  left : (backward.comp forward).HomotopyRel (ContinuousMap.id X) {x}
  right : (forward.comp backward).HomotopyRel (ContinuousMap.id Y) {y}

/-- An ordinary equivalence and an actual basepoint path give a genuine based equivalence. -/
theorem based_inverse [T1Space X] [T1Space Y] (x : X) (y : Y)
    (RX : CylinderRetraction x) (RY : CylinderRetraction y)
    (f : C(X, Y)) (g : C(Y, X))
    (Hgf : (g.comp f).Homotopy (ContinuousMap.id X))
    (Hfg : (f.comp g).Homotopy (ContinuousMap.id Y))
    (γ : Path (f x) y) :
    ∃ E : BasedEquivalence x y, ∃ A : f.Homotopy E.forward,
      ∀ t, A (t, x) = γ t := by
  obtain ⟨F, A, hA⟩ := moveMap RX f γ.toContinuousMap γ.source
  have hF : F x = y := by simpa using (A.apply_one x).symm.trans (hA 1)
  let H : (g.comp F).Homotopy (ContinuousMap.id X) :=
    ((Homotopy.refl g).comp A).symm.trans Hgf
  let β : C(I, X) := ⟨fun t => H (t, x), H.continuous.comp (by fun_prop)⟩
  have hβ0 : β 0 = g y := by simp [β, hF]
  have hβ1 : β 1 = x := by simp [β]
  obtain ⟨G, B, hB⟩ := moveMap RY g β hβ0
  have hG : G y = x := (B.apply_one y).symm.trans ((hB 1).trans hβ1)
  let L : (G.comp F).Homotopy (ContinuousMap.id X) :=
    (B.compContinuousMap F).symm.trans H
  have hL : ∀ t, L (t, x) = β (backtrack t) := by
    intro t
    rw [show L = (B.compContinuousMap F).symm.trans H from rfl, Homotopy.trans_apply]
    split_ifs with ht
    · simp only [Homotopy.symm_apply, Homotopy.compContinuousMap_apply, hF, hB]
      congr 1
      apply Subtype.ext
      simp only [unitInterval.coe_symm_eq, backtrack, ContinuousMap.coe_mk]
      rw [abs_of_nonpos (by linarith)]
      ring
    · change H (_, x) = H (backtrack t, x)
      congr 1
      apply Prod.ext
      · apply Subtype.ext
        simp only [backtrack, ContinuousMap.coe_mk]
        rw [abs_of_nonneg (by linarith)]
      · rfl
  let U : (G.comp F).HomotopyRel (ContinuousMap.id X) {x} :=
    cancelTrace RX x L β backtrack (by simp [hF, hG]) rfl hβ1
      (by apply Subtype.ext; norm_num [backtrack])
      (by apply Subtype.ext; norm_num [backtrack]) hL
  let K : (F.comp g).Homotopy (ContinuousMap.id Y) :=
    (A.compContinuousMap g).symm.trans Hfg
  let V : (F.comp G).Homotopy (ContinuousMap.id Y) :=
    ((Homotopy.refl F).comp B).symm.trans K
  let C := F.comp G
  let J : (C.comp C).Homotopy C :=
    ((Homotopy.refl F).comp (U.toHomotopy.compContinuousMap G)).cast rfl rfl
  let Q : C.Homotopy (C.comp C) := (V.compContinuousMap C).symm.cast rfl rfl
  let W : C.Homotopy (ContinuousMap.id Y) := (Q.trans J).trans V
  let δ : C(I, Y) := ⟨fun t => V (t, y), V.continuous.comp (by fun_prop)⟩
  have hC : C y = y := by simp [C, hG, hF]
  have hδ0 : δ 0 = y := (V.apply_zero y).trans hC
  have hδ1 : δ 1 = y := by simp [δ]
  have hJ (t : I) : J (t, y) = y := by
    change F (U (t, G y)) = y
    rw [hG, U.eq_snd t (mem_singleton x)]
    exact hF
  have hQ (t : I) : Q (t, y) = δ (unitInterval.symm t) := by
    change V (unitInterval.symm t, C y) = V (unitInterval.symm t, y)
    rw [hC]
  have hW : ∀ t, W (t, y) = δ (pausedBacktrack t) := by
    intro t
    rw [show W = (Q.trans J).trans V from rfl, Homotopy.trans_apply]
    split_ifs with ht
    · rw [Homotopy.trans_apply]
      split_ifs with hu
      · rw [hQ]
        change δ _ = δ (pausedBacktrack t)
        congr 1
        apply Subtype.ext
        simp only [unitInterval.coe_symm_eq] at hu ⊢
        simp only [pausedBacktrack, ContinuousMap.coe_mk]
        rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - 4 * (t : ℝ)),
          max_eq_left (by linarith : 2 * (t : ℝ) - 1 ≤ 1 - 4 * (t : ℝ))]
        ring
      · rw [hJ]
        have he : pausedBacktrack t = 0 := by
          apply Subtype.ext
          simp only [pausedBacktrack, ContinuousMap.coe_mk]
          rw [max_eq_right (by linarith : 1 - 4 * (t : ℝ) ≤ 0),
            max_eq_left (by linarith : 2 * (t : ℝ) - 1 ≤ 0)]
          rfl
        simpa [he] using hδ0.symm
    · change δ _ = δ (pausedBacktrack t)
      congr 1
      apply Subtype.ext
      simp only [pausedBacktrack, ContinuousMap.coe_mk]
      rw [max_eq_right (by linarith : 1 - 4 * (t : ℝ) ≤ 0),
        max_eq_right (by linarith : (0 : ℝ) ≤ 2 * (t : ℝ) - 1)]
  let T : C.HomotopyRel (ContinuousMap.id Y) {y} :=
    cancelTrace RY y W δ pausedBacktrack hC rfl hδ1
      (by apply Subtype.ext; norm_num [pausedBacktrack])
      (by apply Subtype.ext; norm_num [pausedBacktrack]) hW
  exact ⟨⟨F, G, hF, hG, U, T⟩, A, hA⟩

#print axioms based_inverse

end D5.S3.Geometry.SingletonRetractionBasedInverse
