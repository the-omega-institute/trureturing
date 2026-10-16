/- GID: D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Intrinsic]
   utility: none
   digest: Literal two-level barycentric stars and their complete first-parent realizations. -/

import D5.S3.Geometry.Gluing.BarycentricSubdivisionStar
import Mathlib.Order.RelSeries
import Mathlib.Data.Finset.Grade
import Mathlib.Order.Preorder.Chain
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Geometry.Gluing.BarycentricSubdivisionStar

namespace D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonempty chain of nonempty original face chains, ordered by inclusion of chains. -/
structure SecondFaceChain where
  chains : Finset (Finset (Finset (Fin 4)))
  nonempty : chains.Nonempty
  chain_nonempty : ∀ C ∈ chains, C.Nonempty
  face_nonempty : ∀ C ∈ chains, ∀ F ∈ C, F.Nonempty
  first_comparable : ∀ C ∈ chains, ∀ F ∈ C, ∀ G ∈ C, F ⊆ G ∨ G ⊆ F
  comparable : ∀ C ∈ chains, ∀ B ∈ chains, C ⊆ B ∨ B ⊆ C

/-- The literal second barycenter: an average of actual original face barycenters. -/
noncomputable def secondBarycenter (p : Fin 4 → E)
    (C : Finset (Finset (Fin 4))) : E :=
  (C.card : ℝ)⁻¹ • ∑ F ∈ C, barycenter p F

/-- Actual second subdivision hull, retaining the original chain of chains. -/
noncomputable def secondHull (p : Fin 4 → E) (D : SecondFaceChain) : Set E :=
  convexHull ℝ (secondBarycenter p '' (D.chains : Set _))

/-- Literal closed star, defined by actual point equality at an original vertex. -/
def literalClosedStar (p : Fin 4 → E) (i : Fin 4) : Set E :=
  {x | ∃ D : SecondFaceChain, p i ∈ secondBarycenter p '' (D.chains : Set _) ∧
    x ∈ secondHull p D}

/-- All-face literal open star; the interior is taken in each actual hull's affine span. -/
def literalOpenStar (p : Fin 4 → E) (i : Fin 4) : Set E :=
  {x | ∃ D : SecondFaceChain, p i ∈ secondBarycenter p '' (D.chains : Set _) ∧
    x ∈ intrinsicInterior ℝ (secondHull p D)}

private noncomputable def chainWeight (C : Finset (Finset (Fin 4))) (j : Fin 4) : ℝ :=
  (C.card : ℝ)⁻¹ * ∑ F ∈ C, faceWeight F j

private lemma chainWeight_nonneg (C : Finset (Finset (Fin 4))) (j : Fin 4) :
    0 ≤ chainWeight C j := by
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro F _
  simp only [faceWeight]
  split_ifs <;> positivity

private lemma chainWeight_sum (C : Finset (Finset (Fin 4))) (hC : C.Nonempty)
    (hne : ∀ F ∈ C, F.Nonempty) : ∑ j, chainWeight C j = 1 := by
  classical
  simp only [chainWeight, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun F hF => faceWeight_sum F (hne F hF))]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hC))

private lemma secondBarycenter_eq_sum (p : Fin 4 → E) (C : Finset (Finset (Fin 4))) :
    secondBarycenter p C = ∑ j, chainWeight C j • p j := by
  classical
  simp only [secondBarycenter, chainWeight, mul_smul, ← Finset.smul_sum]
  congr 1
  simp only [barycenter_eq_sum, Finset.sum_smul]
  exact Finset.sum_comm

private lemma secondBarycenter_vertex_iff (p : Fin 4 → E)
    (hp : AffineIndependent ℝ p) (C : Finset (Finset (Fin 4)))
    (hC : C.Nonempty) (hne : ∀ F ∈ C, F.Nonempty) (i : Fin 4) :
    secondBarycenter p C = p i ↔ C = {{i}} := by
  classical
  constructor
  · intro heq
    have hu := weights_unique p hp (chainWeight C) (fun j => if j = i then 1 else 0)
      (chainWeight_sum C hC hne) (by simp) (by
        simpa only [← secondBarycenter_eq_sum, ite_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, one_smul] using heq)
    have hsingle (F : Finset (Fin 4)) (hF : F ∈ C) : F = {i} := by
      have hsub : F ⊆ {i} := by
        intro j hj
        by_contra hji
        have hji' : j ≠ i := by simpa only [Finset.mem_singleton] using hji
        have ha : chainWeight C j = 0 := by simpa [hji'] using congrFun hu j
        have hterm : 0 < faceWeight F j := by
          simp only [faceWeight, if_pos hj]
          exact inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr (hne F hF)))
        have hsum : 0 < ∑ G ∈ C, faceWeight G j :=
          hterm.trans_le (Finset.single_le_sum (f := fun G => faceWeight G j) (fun G _ => by
            simp only [faceWeight]
            split_ifs <;> positivity) hF)
        have hpos : 0 < chainWeight C j := mul_pos
          (inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hC))) hsum
        linarith
      exact Finset.eq_singleton_iff_nonempty_unique_mem.mpr
        ⟨hne F hF, fun j hj => Finset.mem_singleton.mp (hsub hj)⟩
    obtain ⟨F, hF⟩ := hC
    have hiC : ({i} : Finset (Fin 4)) ∈ C := (hsingle F hF) ▸ hF
    ext G
    simp only [Finset.mem_singleton]
    exact ⟨hsingle G, fun h => h.symm ▸ hiC⟩
  · rintro rfl
    simp [secondBarycenter, barycenter]


private lemma cover_refinement (C : FaceChain) :
    ∃ (t : RelSeries {(a, b) : Finset (Fin 4) × Finset (Fin 4) | a ⋖ b}),
      t.head = ∅ ∧ t.last = Finset.univ ∧
      ∀ F ∈ C.faces, ∃ k, t k = F := by
  classical
  have hc : IsChain (· ≤ ·) (C.faces : Set (Finset (Fin 4))) := by
    intro F hF G hG _
    exact C.comparable F hF G hG
  letI := hc.lt_of_le.linearOrder
  let e := Fintype.orderIsoFinOfCardEq C.faces (by simp : Fintype.card C.faces = C.faces.card)
  have hn : C.faces.card - 1 + 1 = C.faces.card := by
    have := Finset.card_pos.mpr C.nonempty
    omega
  let s : LTSeries (Finset (Fin 4)) :=
    LTSeries.mk (C.faces.card - 1) (fun k => (e (Fin.cast hn k)).val)
      (by
        intro i j hij
        exact e.strictMono (by simpa using hij))
  obtain ⟨t, j, hj, hb, ht⟩ :=
    s.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
  refine ⟨t, hb, ht, ?_⟩
  intro F hF
  let k := Fin.cast hn.symm (e.symm ⟨F, hF⟩)
  refine ⟨j k, ?_⟩
  have hh := congrFun hj k
  change t (j k) = (e (Fin.cast hn k)).val at hh
  simpa [k] using hh


-- Exact bridge from the library cover series to the four actual prefix faces.
private lemma complete_original_flag (C : FaceChain) :
    ∃ π : Equiv.Perm (Fin 4),
      ∀ F ∈ C.faces, ∃ k : Fin 4, (Finset.Iic k).image π = F := by
  classical
  obtain ⟨t, hb, ht, hretain⟩ := cover_refinement C
  have hcard (k : Fin (t.length + 1)) : (t k).card = k.val := by
    induction k using Fin.induction with
    | zero => simpa only [RelSeries.head, Finset.card_empty, Fin.val_zero] using congrArg Finset.card hb
    | succ k ih =>
      have h := Nat.covBy_iff_add_one_eq.mp (t.step k).card_finset
      simpa only [ih, Fin.val_succ, Fin.val_castSucc] using h.symm
  have hlen : t.length = 4 := by
    have h := hcard (Fin.last t.length)
    rw [show t (Fin.last t.length) = Finset.univ from ht] at h
    simpa using h.symm
  let u : Fin 5 → Finset (Fin 4) := fun k => t (Fin.cast (by omega) k)
  have u0 : u 0 = ∅ := hb
  have us (k : Fin 4) : u k.castSucc ⋖ u k.succ := by
    have h := t.step (Fin.cast hlen.symm k)
    simpa [u] using h
  have um : Monotone u := Fin.monotone_iff_le_succ.mpr (fun k => (us k).le)
  choose f hnot hins using fun k => (us k).exists_finset_insert
  have hmem (k : Fin 4) : f k ∈ u k.succ := by
    rw [← hins k]
    exact Finset.mem_insert_self _ _
  have hne {i j : Fin 4} (hij : i < j) : f i ≠ f j := by
    intro h
    apply hnot j
    rw [← h]
    apply um (show i.succ ≤ j.castSucc by change i.val + 1 ≤ j.val; omega)
    exact hmem i
  have hinj : Function.Injective f := by
    intro i j h
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact (hne hlt h).elim
    · exact heq
    · exact (hne hgt h.symm).elim
  let π : Equiv.Perm (Fin 4) := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hpref (k : Fin 4) : u k.succ = (Finset.Iic k).image π := by
    induction k using Fin.induction with
    | zero =>
      rw [← hins 0]
      change insert (f 0) (u 0) = _
      rw [u0]
      have hI : Finset.Iic (0 : Fin 4) = {0} := by decide
      simp [hI, π]
      rfl
    | succ k ih =>
      have hI : Finset.Iic k.succ = insert k.succ (Finset.Iic k.castSucc) := by
        ext j
        simp only [Finset.mem_Iic, Finset.mem_insert]
        constructor
        · intro h
          by_cases he : j = k.succ
          · exact Or.inl he
          · right
            change j.val ≤ k.val
            have hneval : j.val ≠ k.val + 1 := fun heq => he (Fin.ext heq)
            change j.val ≤ k.val + 1 at h
            omega
        · rintro (rfl | h)
          · exact le_rfl
          · exact h.trans (show k.castSucc ≤ k.succ from Nat.le_succ k.val)
      rw [← hins k.succ, hI, Finset.image_insert, ← ih]
      rfl
  refine ⟨π, ?_⟩
  intro F hF
  obtain ⟨a, ha⟩ := hretain F hF
  let r : Fin 5 := Fin.cast (by omega) a
  have hr : u r = F := ha
  have hrpos : 0 < r.val := by
    by_contra h
    have hz : r = 0 := Fin.ext (by omega)
    have : F = ∅ := by rw [← hr, hz, u0]
    exact (C.face_nonempty F hF).ne_empty this
  let k : Fin 4 := ⟨r.val - 1, by have := r.isLt; omega⟩
  have heq : k.succ = r := Fin.ext (by dsimp [k]; omega)
  exact ⟨k, (hpref k).symm.trans (heq ▸ hr)⟩

private lemma prefixFace_injective (π : Equiv.Perm (Fin 4)) :
    Function.Injective (prefixFace π) := by
  intro k l h
  have hc := congrArg Finset.card h
  simp only [prefixFace, Finset.card_image_of_injective _ π.injective, Fin.card_Iic] at hc
  apply Fin.ext
  omega

private def liftFaces (π : Equiv.Perm (Fin 4)) (S : Finset (Fin 4)) :
    Finset (Finset (Fin 4)) := S.image (prefixFace π)

private def indexFaces (π : Equiv.Perm (Fin 4)) (C : Finset (Finset (Fin 4))) :
    Finset (Fin 4) := Finset.univ.filter (fun k => prefixFace π k ∈ C)

private lemma lift_index (π : Equiv.Perm (Fin 4)) (C : Finset (Finset (Fin 4)))
    (hC : C ⊆ liftFaces π Finset.univ) :
    liftFaces π (indexFaces π C) = C := by
  classical
  ext F
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hk).2
  · intro h
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (hC h)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

private lemma actual_average (p : Fin 4 → E) (π : Equiv.Perm (Fin 4))
    (S : Finset (Fin 4)) :
    secondBarycenter p (liftFaces π S) =
      barycenter (fun k => barycenter p (prefixFace π k)) S := by
  classical
  simp only [secondBarycenter, liftFaces,
    Finset.card_image_of_injective _ (prefixFace_injective π),
    Finset.sum_image (fun _ _ _ _ h => prefixFace_injective π h), barycenter]

-- Parent -> original: all dimensions; retain the nested family of original face chains.
private lemma parent_carrier_to_original (p : Fin 4 → E) (π : Equiv.Perm (Fin 4)) (T : FaceChain) :
    ∃ D : Finset (Finset (Finset (Fin 4))),
      D.Nonempty ∧
      (∀ C ∈ D, C.Nonempty ∧
        (∀ F ∈ C, F.Nonempty) ∧
        (∀ F ∈ C, ∀ G ∈ C, F ⊆ G ∨ G ⊆ F)) ∧
      (∀ C ∈ D, ∀ B ∈ D, C ⊆ B ∨ B ⊆ C) ∧
      (∀ C ∈ D, C ⊆ liftFaces π Finset.univ) ∧
      (secondBarycenter p '' (D : Set _) =
        barycenter (fun k => barycenter p (prefixFace π k)) '' (T.faces : Set _)) := by
  classical
  let D := T.faces.image (liftFaces π)
  refine ⟨D, T.nonempty.image _, ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hC
    refine ⟨(T.face_nonempty S hS).image _, ?_, ?_⟩
    · intro F hF
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hF
      exact ⟨π k, Finset.mem_image.mpr ⟨k, Finset.mem_Iic.mpr le_rfl, rfl⟩⟩
    · intro F hF G hG
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hF
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hG
      rcases le_total k l with h | h
      · exact Or.inl (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr h))
      · exact Or.inr (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr h))
  · intro C hC B hB
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hB
    exact (T.comparable S hS U hU).imp Finset.image_subset_image Finset.image_subset_image
  · intro C hC
    obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hC
    exact Finset.image_subset_image (Finset.subset_univ _)
  · ext y
    constructor
    · rintro ⟨C, hC, rfl⟩
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hC
      exact ⟨S, hS, (actual_average p π S).symm⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨liftFaces π S, Finset.mem_image.mpr ⟨S, hS, rfl⟩, actual_average p π S⟩

-- Original -> parent: the actual original carrier is kept, not flattened.
private lemma original_carrier_to_parent (p : Fin 4 → E) (π : Equiv.Perm (Fin 4))
    (D : Finset (Finset (Finset (Fin 4)))) (hD : D.Nonempty)
    (hne : ∀ C ∈ D, C.Nonempty)
    (hnest : ∀ C ∈ D, ∀ B ∈ D, C ⊆ B ∨ B ⊆ C)
    (hparent : ∀ C ∈ D, C ⊆ liftFaces π Finset.univ) :
    ∃ T : FaceChain,
      secondBarycenter p '' (D : Set _) =
        barycenter (fun k => barycenter p (prefixFace π k)) '' (T.faces : Set _) ∧
      convexHull ℝ (secondBarycenter p '' (D : Set _)) =
        chainHull (fun k => barycenter p (prefixFace π k)) T ∧
      intrinsicInterior ℝ (convexHull ℝ (secondBarycenter p '' (D : Set _))) =
        intrinsicInterior ℝ (chainHull (fun k => barycenter p (prefixFace π k)) T) := by
  classical
  let T : FaceChain := {
    faces := D.image (indexFaces π)
    nonempty := hD.image _
    face_nonempty := by
      intro S hS
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨F, hF⟩ := hne C hC
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (hparent C hC hF)
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk ▸ hF⟩⟩
    comparable := by
      intro S hS U hU
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hU
      rcases hnest C hC B hB with h | h
      · left; intro k hk
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h (Finset.mem_filter.mp hk).2⟩
      · right; intro k hk
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h (Finset.mem_filter.mp hk).2⟩ }
  have hv : secondBarycenter p '' (D : Set _) =
      barycenter (fun k => barycenter p (prefixFace π k)) '' (T.faces : Set _) := by
    ext y
    constructor
    · rintro ⟨C, hC, rfl⟩
      refine ⟨indexFaces π C, Finset.mem_image.mpr ⟨C, hC, rfl⟩, ?_⟩
      rw [← actual_average, lift_index π C (hparent C hC)]
    · rintro ⟨S, hS, rfl⟩
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hS
      refine ⟨C, hC, ?_⟩
      rw [← actual_average, lift_index π C (hparent C hC)]
  exact ⟨T, hv, congrArg (convexHull ℝ) hv,
    congrArg (fun s => intrinsicInterior ℝ (convexHull ℝ s)) hv⟩


private lemma secondHull_vertex_iff (p : Fin 4 → E) (hp : AffineIndependent ℝ p)
    (i : Fin 4) (D : SecondFaceChain) :
    p i ∈ secondHull p D ↔ ({({i} : Finset (Fin 4))} : Finset (Finset (Fin 4))) ∈ D.chains := by
  classical
  constructor
  · intro hx
    obtain ⟨I, hI, w, z, hw, hwone, hz, hzx⟩ :=
      mem_convexHull_iff_exists_fintype.mp hx
    choose C hC hCz using hz
    let a : Fin 4 → ℝ := fun j => ∑ k, w k * chainWeight (C k) j
    have hasum : ∑ j, a j = 1 := by
      dsimp [a]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum,
        chainWeight_sum _ (D.chain_nonempty _ (hC _)) (D.face_nonempty _ (hC _)),
        mul_one]
      exact hwone
    have haeq : ∑ j, a j • p j = p i := by
      calc
        ∑ j, a j • p j = ∑ k, w k • secondBarycenter p (C k) := by
          simp only [a, Finset.sum_smul, mul_smul, secondBarycenter_eq_sum,
            Finset.smul_sum]
          exact Finset.sum_comm
        _ = p i := by simp_rw [hCz]; exact hzx
    have hu := weights_unique p hp a (fun j => if j = i then 1 else 0)
      hasum (by simp) (by simpa using haeq)
    have hpossum : 0 < ∑ k, w k := by rw [hwone]; norm_num
    obtain ⟨k, _, hk⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun k _ => hw k)).mp hpossum
    have hzero (j : Fin 4) (hji : j ≠ i) : chainWeight (C k) j = 0 := by
      have haj : a j = 0 := by simpa [hji] using congrFun hu j
      have hle : w k * chainWeight (C k) j ≤ 0 := by
        rw [← haj]
        exact Finset.single_le_sum (f := fun k => w k * chainWeight (C k) j)
          (fun k _ => mul_nonneg (hw k) (chainWeight_nonneg _ j)) (Finset.mem_univ k)
      have heq : w k * chainWeight (C k) j = 0 :=
        le_antisymm hle (mul_nonneg (hw k) (chainWeight_nonneg _ j))
      exact (mul_eq_zero.mp heq).resolve_left (ne_of_gt hk)
    have hi : chainWeight (C k) i = 1 := by
      have hs := chainWeight_sum (C k) (D.chain_nonempty _ (hC k))
        (D.face_nonempty _ (hC k))
      rw [Finset.sum_eq_single i] at hs
      · exact hs
      · intro j _ hji; exact hzero j hji
      · simp
    have hb : secondBarycenter p (C k) = p i := by
      rw [secondBarycenter_eq_sum, Finset.sum_eq_single i, hi, one_smul]
      · intro j _ hji; rw [hzero j hji, zero_smul]
      · simp
    have hc := (secondBarycenter_vertex_iff p hp (C k)
      (D.chain_nonempty _ (hC k)) (D.face_nonempty _ (hC k)) i).mp hb
    simpa only [hc, Finset.mem_coe] using hC k
  · intro h
    apply subset_convexHull ℝ
    refine ⟨{{i}}, h, ?_⟩
    simp [secondBarycenter, barycenter]

private lemma incident_second_parent (p : Fin 4 → E) (hp : AffineIndependent ℝ p)
    (i : Fin 4) (D : SecondFaceChain)
    (hinc : p i ∈ secondBarycenter p '' (D.chains : Set _)) :
    ∃ π : Equiv.Perm (Fin 4), π 0 = i ∧ ∃ T : FaceChain,
      secondBarycenter p '' (D.chains : Set _) =
        barycenter (fun k => barycenter p (prefixFace π k)) '' (T.faces : Set _) ∧
      secondHull p D = chainHull (fun k => barycenter p (prefixFace π k)) T ∧
      intrinsicInterior ℝ (secondHull p D) =
        intrinsicInterior ℝ (chainHull (fun k => barycenter p (prefixFace π k)) T) := by
  classical
  obtain ⟨Ctop, htop, hmax⟩ := D.chains.exists_max_image Finset.card D.nonempty
  have hsub (C) (hC : C ∈ D.chains) : C ⊆ Ctop := by
    rcases D.comparable C hC Ctop htop with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h (hmax C hC)).ge
  let top : FaceChain := ⟨Ctop, D.chain_nonempty Ctop htop,
    D.face_nonempty Ctop htop, D.first_comparable Ctop htop⟩
  obtain ⟨π, hflag⟩ := complete_original_flag top
  have hiD := (secondHull_vertex_iff p hp i D).mp (subset_convexHull ℝ _ hinc)
  have hsingleton : ({i} : Finset (Fin 4)) ∈ Ctop :=
    hsub {{i}} hiD (Finset.mem_singleton_self _)
  obtain ⟨k, hk⟩ := hflag {i} hsingleton
  have hk0 : k = 0 := by
    have hc := congrArg Finset.card hk
    simp only [Finset.card_image_of_injective _ π.injective,
      Fin.card_Iic, Finset.card_singleton] at hc
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  have hπ : π 0 = i := by
    subst k
    have hI : Finset.Iic (0 : Fin 4) = {0} := by decide
    simpa [hI] using hk
  have hparent (C) (hC : C ∈ D.chains) : C ⊆ liftFaces π Finset.univ := by
    intro F hF
    obtain ⟨k, hk⟩ := hflag F (hsub C hC hF)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  obtain ⟨T, hv, hh, hi⟩ := original_carrier_to_parent p π D.chains
    D.nonempty D.chain_nonempty D.comparable hparent
  exact ⟨π, hπ, T, hv, hh, hi⟩

private lemma parent_second_realization (p : Fin 4 → E)
    (π : Equiv.Perm (Fin 4)) (T : FaceChain) :
    ∃ D : SecondFaceChain,
      secondBarycenter p '' (D.chains : Set _) =
        barycenter (fun k => barycenter p (prefixFace π k)) '' (T.faces : Set _) ∧
      secondHull p D = chainHull (fun k => barycenter p (prefixFace π k)) T ∧
      intrinsicInterior ℝ (secondHull p D) =
        intrinsicInterior ℝ (chainHull (fun k => barycenter p (prefixFace π k)) T) := by
  obtain ⟨d, hd, hfirst, hnest, _, hv⟩ := parent_carrier_to_original p π T
  let D : SecondFaceChain := {
    chains := d
    nonempty := hd
    chain_nonempty := fun C hC => (hfirst C hC).1
    face_nonempty := fun C hC => (hfirst C hC).2.1
    first_comparable := fun C hC => (hfirst C hC).2.2
    comparable := hnest }
  exact ⟨D, hv, congrArg (convexHull ℝ) hv,
    congrArg (fun s => intrinsicInterior ℝ (convexHull ℝ s)) hv⟩

/-- The literal original second stars equal the union of the existing actual
parent stars. Both directions retain the original face-chain carriers and
transport equal ambient hulls and their intrinsic interiors. -/
theorem literal_second_closed_and_open_star_iff (p : Fin 4 → E)
    (hp : AffineIndependent ℝ p) (i : Fin 4) (x : E) :
    (x ∈ literalClosedStar p i ↔
      ∃ π : Equiv.Perm (Fin 4), π 0 = i ∧
        x ∈ closedStar (fun k => barycenter p (prefixFace π k))) ∧
    (x ∈ literalOpenStar p i ↔
      ∃ π : Equiv.Perm (Fin 4), π 0 = i ∧
        x ∈ openStar (fun k => barycenter p (prefixFace π k))) := by
  have hzero (π : Equiv.Perm (Fin 4)) (hπ : π 0 = i) :
      barycenter p (prefixFace π 0) = p i := by
    simpa [hπ] using prefix_barycenters p π 0
  constructor
  · constructor
    · rintro ⟨D, hinc, hx⟩
      obtain ⟨π, hπ, T, hv, hh, _⟩ := incident_second_parent p hp i D hinc
      obtain ⟨ρ, hρ⟩ := complete_original_flag T
      have hsub : T.faces ⊆ (flagChain ρ).faces := by
        intro F hF
        obtain ⟨k, hk⟩ := hρ F hF
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
      have himage :
          barycenter (fun k => barycenter p (prefixFace π k)) '' (T.faces : Set _) ⊆
          barycenter (fun k => barycenter p (prefixFace π k)) ''
            ((flagChain ρ).faces : Set _) :=
        Set.image_mono hsub
      refine ⟨π, hπ, flagChain ρ, ?_, ?_⟩
      · apply himage
        change barycenter p (prefixFace π 0) ∈ _
        rw [hzero π hπ, ← hv]
        exact hinc
      · apply convexHull_mono himage
        change x ∈ chainHull (fun k => barycenter p (prefixFace π k)) T
        rwa [← hh]
    · rintro ⟨π, hπ, T, hinc, hx⟩
      obtain ⟨D, hv, hh, _⟩ := parent_second_realization p π T
      refine ⟨D, ?_, hh.symm ▸ hx⟩
      rw [hv, ← hzero π hπ]
      exact hinc
  · constructor
    · rintro ⟨D, hinc, hx⟩
      obtain ⟨π, hπ, T, hv, _, hi⟩ := incident_second_parent p hp i D hinc
      refine ⟨π, hπ, T, ?_, hi ▸ hx⟩
      change barycenter p (prefixFace π 0) ∈ _
      rw [hzero π hπ, ← hv]
      exact hinc
    · rintro ⟨π, hπ, T, hinc, hx⟩
      obtain ⟨D, hv, _, hi⟩ := parent_second_realization p π T
      refine ⟨D, ?_, hi.symm ▸ hx⟩
      rw [hv, ← hzero π hπ]
      exact hinc

end D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar
