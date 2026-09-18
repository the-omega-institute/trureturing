/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytope
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib/Analysis/Convex/Exposed,
     mathlib/module/Mathlib/LinearAlgebra/AffineSpace/AffineMap,
     mathlib/module/Mathlib/Data/Fintype/Powerset]
   utility: none
   digest: Crown inequalities give finite faces with block-constant coordinates. -/

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Combination
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytope

open scoped BigOperators

/- The zero-based even coordinates represent the odd vertices of the crown.  Each such
   coordinate is below its two neighbouring odd coordinates in the cyclic order. -/
def crownRelation (n : ℕ) (i j : Fin (2 * n)) : Prop :=
  i.val % 2 = 0 ∧
    (j.val = (i.val + 1) % (2 * n) ∨ j.val = (i.val + (2 * n) - 1) % (2 * n))

def crownOrderPolytope (n : ℕ) : Set (Fin (2 * n) → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∀ i j, crownRelation n i j → x i ≤ x j}

theorem crown_order_polytope_convex (n : ℕ) :
    Convex ℝ (crownOrderPolytope n) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro i
    constructor <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · have h₁ : 0 ≤ a * x i := mul_nonneg ha (hx.1 i).1
      have h₂ : 0 ≤ b * y i := mul_nonneg hb (hy.1 i).1
      linarith
    · have h₁ : a * x i ≤ a * 1 := mul_le_mul_of_nonneg_left (hx.1 i).2 ha
      have h₂ : b * y i ≤ b * 1 := mul_le_mul_of_nonneg_left (hy.1 i).2 hb
      linarith
  · intro i j hij
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h₁ := mul_le_mul_of_nonneg_left (hx.2 i j hij) ha
    have h₂ := mul_le_mul_of_nonneg_left (hy.2 i j hij) hb
    linarith

theorem zero_mem_crown_order_polytope (n : ℕ) :
    (0 : Fin (2 * n) → ℝ) ∈ crownOrderPolytope n := by
  constructor
  · intro i
    simp
  · intro i j hij
    simp

theorem one_mem_crown_order_polytope (n : ℕ) :
    (1 : Fin (2 * n) → ℝ) ∈ crownOrderPolytope n := by
  constructor
  · intro i
    simp
  · intro i j hij
    simp

structure AffineSlackFamily (E : Type*) [AddCommGroup E] [Module ℝ E] (m : ℕ) where
  slack : Fin m → AffineMap ℝ E ℝ

def AffineSlackFamily.feasible {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℕ} (A : AffineSlackFamily E m) : Set E :=
  {x | ∀ i, 0 ≤ A.slack i x}

def AffineSlackFamily.tightlyHolds {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℕ} (A : AffineSlackFamily E m) (F : Set E) (i : Fin m) : Prop :=
  ∀ y, y ∈ F → A.slack i y = 0

private theorem affine_map_lineMap {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ᵃ[ℝ] ℝ) (x y : E) (t : ℝ) :
    f (AffineMap.lineMap x y t) = AffineMap.lineMap (f x) (f y) t := by
  rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
  rw [f.map_vadd, map_smulₛₗ, f.linearMap_vsub]
  simp only [map_smulₛₗ, vadd_eq_add, smul_eq_mul]
  simp only [RingHom.id_apply]

theorem finite_extension_of_active_slacks
    {d m : ℕ} (A : AffineSlackFamily (Fin d → ℝ) m) (F : Set (Fin d → ℝ))
    (hF : IsExposed ℝ A.feasible F) (anchor : Fin d → ℝ) (hanchor : anchor ∈ F) :
    ∃ center, center ∈ F ∧
      ∀ z, z ∈ A.feasible →
        (∀ i, A.tightlyHolds F i → A.slack i z = 0) →
        ∃ z', z' ∈ A.feasible ∧ center ∈ openSegment ℝ z z' := by
  classical
  have hconv : Convex ℝ A.feasible := by
    intro x hx y hy a b ha hb hab
    intro i
    have hline : a • x + b • y = AffineMap.lineMap x y b := by
      rw [AffineMap.lineMap_apply_module]
      congr 1
      rw [← hab]
      module
    rw [hline, affine_map_lineMap, AffineMap.lineMap_apply_module]
    simp only [smul_eq_mul]
    have ha' : 0 ≤ 1 - b := by linarith
    exact add_nonneg (mul_nonneg ha' (hx i)) (mul_nonneg hb (hy i))
  have hFconv : Convex ℝ F := hF.convex hconv
  have witness_exists (i : Fin m) (hi : ¬ A.tightlyHolds F i) :
      ∃ y, y ∈ F ∧ A.slack i y ≠ 0 := by
    by_contra h
    apply hi
    intro y hy
    by_contra hne
    exact h ⟨y, hy, hne⟩
  let witness : Fin m → (Fin d → ℝ) := fun i =>
    if hi : A.tightlyHolds F i then anchor else Classical.choose (witness_exists i hi)
  have witness_mem (i : Fin m) : witness i ∈ F := by
    by_cases hi : A.tightlyHolds F i
    · simp [witness, hi, hanchor]
    · simpa [witness, hi] using (Classical.choose_spec (witness_exists i hi)).1
  have witness_slack_pos (i : Fin m) (hi : ¬ A.tightlyHolds F i) :
      0 < A.slack i (witness i) := by
    have hne := (Classical.choose_spec (witness_exists i hi)).2
    have hnonneg : 0 ≤ A.slack i (Classical.choose (witness_exists i hi)) :=
      (hF.subset (Classical.choose_spec (witness_exists i hi)).1) i
    simpa [witness, hi] using (lt_of_le_of_ne hnonneg (Ne.symm hne))
  let p : Option (Fin m) → (Fin d → ℝ) := fun o =>
    match o with
    | none => anchor
    | some i => witness i
  let s : Finset (Option (Fin m)) := Finset.univ
  let w : Option (Fin m) → ℝ := fun _ => (Fintype.card (Option (Fin m)) : ℝ)⁻¹
  have hcard : (Fintype.card (Option (Fin m)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Option (Fin m)) ≠ 0)
  have hsum : ∑ i ∈ s, w i = 1 := by
    simp only [s, w, Finset.sum_const, Finset.card_univ, Fintype.card_option,
      Fintype.card_fin, Nat.cast_add, Nat.cast_one, nsmul_eq_mul]
    exact mul_inv_cancel₀ (show (↑m + 1 : ℝ) ≠ 0 by positivity)
  let center : (Fin d → ℝ) := s.centerMass w p
  have hcenter_eq : center = s.affineCombination ℝ p w := by
    simp only [center]
    rw [Finset.centerMass_eq_of_sum_1 s p hsum,
      Finset.affineCombination_eq_linear_combination s p w hsum]
  have hp_mem (o : Option (Fin m)) : p o ∈ F := by
    cases o with
    | none => exact hanchor
    | some i => exact witness_mem i
  have hcenter_mem : center ∈ F := by
    apply hFconv.centerMass_mem
    · intro i hi
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · rw [show ∑ i ∈ s, w i = 1 from hsum]
      exact zero_lt_one
    · exact fun i hi => hp_mem i
  have hslack_average (i : Fin m) :
      A.slack i center = ∑ o ∈ s, w o • A.slack i (p o) := by
    rw [hcenter_eq, Finset.map_affineCombination s p w hsum (A.slack i)]
    simpa [Function.comp_def] using
      (Finset.affineCombination_eq_linear_combination s (fun o => A.slack i (p o)) w hsum)
  have hcenter_feasible : center ∈ A.feasible := hF.subset hcenter_mem
  have hcenter_inactive_pos (i : Fin m) (hi : ¬ A.tightlyHolds F i) :
      0 < A.slack i center := by
    rw [hslack_average]
    apply Finset.sum_pos'
    · intro o ho
      exact smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ((hF.subset (hp_mem o)) i)
    · refine ⟨some i, Finset.mem_univ _, ?_⟩
      simp only [p, w, smul_eq_mul, Option.some.injEq]
      exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr inferInstance)))
        (witness_slack_pos i hi)
  refine ⟨center, hcenter_mem, ?_⟩
  intro z hz hactive
  let I : Finset (Fin m) := Finset.univ.filter (fun i => ¬ A.tightlyHolds F i)
  by_cases hI : I.Nonempty
  · let values : Finset ℝ := I.image (fun i => A.slack i center)
    have hvalues : values.Nonempty := by
      rcases hI with ⟨i, hi⟩
      exact ⟨A.slack i center, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
    let δ : ℝ := values.min' hvalues
    have hδ_pos : 0 < δ := by
      have hm := values.min'_mem hvalues
      rcases Finset.mem_image.mp hm with ⟨i, hi, hval⟩
      dsimp [δ]
      rw [← hval]
      exact hcenter_inactive_pos i (Finset.mem_filter.mp hi).2
    have hδ_le (i : Fin m) (hi : i ∈ I) : δ ≤ A.slack i center := by
      exact values.min'_le _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    let Z : ℝ := ∑ i ∈ I, A.slack i z
    have hZ_nonneg : 0 ≤ Z := by
      apply Finset.sum_nonneg
      intro i hi
      exact hz i
    let ε : ℝ := δ / (1 + Z)
    have hden_pos : 0 < 1 + Z := by linarith
    have hε_pos : 0 < ε := div_pos hδ_pos hden_pos
    let z' : (Fin d → ℝ) := AffineMap.lineMap center z (-ε)
    have hz'_feasible : z' ∈ A.feasible := by
      intro i
      by_cases hi : A.tightlyHolds F i
      · have hci : A.slack i center = 0 := hi _ hcenter_mem
        have hzi : A.slack i z = 0 := hactive i hi
        dsimp [z']
        rw [affine_map_lineMap, AffineMap.lineMap_apply_module]
        simp [hci, hzi]
      · have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        have hzi_le : A.slack i z ≤ Z := by
          exact Finset.single_le_sum (fun j hj => hz j) hiI
        have hεZ : ε * Z ≤ δ := by
          dsimp [ε]
          calc
            δ / (1 + Z) * Z = (δ * Z) / (1 + Z) := by ring
            _ ≤ δ := (div_le_iff₀ hden_pos).2 (by nlinarith)
        have hεzi : ε * A.slack i z ≤ δ :=
          (mul_le_mul_of_nonneg_left hzi_le (le_of_lt hε_pos)).trans hεZ
        have hεzi_fc : ε * A.slack i z ≤ A.slack i center :=
          hεzi.trans (hδ_le i hiI)
        have hci : 0 ≤ A.slack i center := le_of_lt (hcenter_inactive_pos i hi)
        dsimp [z']
        rw [affine_map_lineMap, AffineMap.lineMap_apply_module]
        simp only [smul_eq_mul, neg_mul, sub_neg_eq_add]
        nlinarith [mul_nonneg (le_of_lt hε_pos) hci]
    have hsegment : center ∈ openSegment ℝ z z' := by
      have ht0 : 0 < (1 + ε)⁻¹ := inv_pos.mpr (by linarith)
      have ht1 : (1 + ε)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr (by linarith)
      have heq : AffineMap.lineMap z z' (1 + ε)⁻¹ = center := by
        simp only [z']
        rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
        ext j
        dsimp
        field_simp
        ring
      rw [← heq]
      exact lineMap_mem_openSegment ℝ z z' ⟨ht0, ht1⟩
    exact ⟨z', hz'_feasible, hsegment⟩
  · have hall : ∀ i, A.tightlyHolds F i := by
      intro i
      by_contra hi
      exact hI (⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
    let z' : (Fin d → ℝ) := AffineMap.lineMap center z (-1 : ℝ)
    have hz'_feasible : z' ∈ A.feasible := by
      intro i
      have hci : A.slack i center = 0 := hall i _ hcenter_mem
      have hzi : A.slack i z = 0 := hactive i (hall i)
      change 0 ≤ A.slack i (AffineMap.lineMap center z (-1 : ℝ))
      have hmap := affine_map_lineMap (A.slack i) center z (-1 : ℝ)
      have hright : 0 ≤ AffineMap.lineMap ((A.slack i) center) ((A.slack i) z) (-1 : ℝ) := by
        rw [AffineMap.lineMap_apply_module]
        simp [hci, hzi]
      calc
        0 ≤ AffineMap.lineMap ((A.slack i) center) ((A.slack i) z) (-1) := hright
        _ = (A.slack i) (AffineMap.lineMap center z (-1 : ℝ)) := hmap.symm
    have hsegment : center ∈ openSegment ℝ z z' := by
      have heq : AffineMap.lineMap z z' (2 : ℝ)⁻¹ = center := by
        simp only [z']
        rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
        ext j
        dsimp
        ring
      rw [← heq]
      exact lineMap_mem_openSegment ℝ z z' ⟨by norm_num, by norm_num⟩
    exact ⟨z', hz'_feasible, hsegment⟩

/-- A finite affine-slack face has exactly the points satisfying the slacks that vanish on it,
    provided the finite extension point exists.  The extension premise is the geometric place
    where the finite average of one fixed face anchor and inactive-constraint witnesses is proved.
    The conclusion itself uses the exposed-face extremality, so no polyhedral classification is
    hidden in a definition. -/
theorem exposed_eq_active_of_finite_extension
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    {m : ℕ} (A : AffineSlackFamily E m) (F : Set E)
    (hF : IsExposed ℝ A.feasible F) (center : E) (hcenter : center ∈ F)
    (hExtension : ∀ z, z ∈ A.feasible →
      (∀ i, A.tightlyHolds F i → A.slack i z = 0) →
      ∃ z', z' ∈ A.feasible ∧ center ∈ openSegment ℝ z z') :
    F = {z | z ∈ A.feasible ∧ ∀ i, A.tightlyHolds F i → A.slack i z = 0} := by
  apply Set.Subset.antisymm
  · intro z hz
    refine ⟨hF.subset hz, ?_⟩
    intro i hi
    exact hi z hz
  · rintro z ⟨hz, hactive⟩
    obtain ⟨z', hz', hsegment⟩ := hExtension z hz hactive
    exact hF.isExtreme.left_mem_of_mem_openSegment hz hz' hcenter hsegment

theorem exposed_eq_active_of_finite_slacks
    {d m : ℕ} (A : AffineSlackFamily (Fin d → ℝ) m) (F : Set (Fin d → ℝ))
    (hF : IsExposed ℝ A.feasible F) (anchor : Fin d → ℝ) (hanchor : anchor ∈ F) :
    F = {z | z ∈ A.feasible ∧ ∀ i, A.tightlyHolds F i → A.slack i z = 0} := by
  obtain ⟨center, hcenter, hExtension⟩ :=
    finite_extension_of_active_slacks A F hF anchor hanchor
  exact exposed_eq_active_of_finite_extension A F hF center hcenter hExtension

/-- A crown constraint is either a lower coordinate bound, an upper coordinate bound, or one
    of the defining comparable pairs. -/
abbrev CrownConstraint (n : ℕ) :=
  Fin (2 * n) ⊕ (Fin (2 * n) ⊕ {p : Fin (2 * n) × Fin (2 * n) //
    crownRelation n p.1 p.2})

noncomputable instance crownConstraintFintype (n : ℕ) : Fintype (CrownConstraint n) := by
  classical
  infer_instance

def crownConstraintSlack (n : ℕ) (c : CrownConstraint n) :
    (Fin (2 * n) → ℝ) →ᵃ[ℝ] ℝ :=
  match c with
  | Sum.inl i => (LinearMap.proj i).toAffineMap
  | Sum.inr (Sum.inl i) =>
      AffineMap.const ℝ (Fin (2 * n) → ℝ) (1 : ℝ) - (LinearMap.proj i).toAffineMap
  | Sum.inr (Sum.inr p) =>
      (LinearMap.proj p.1.2).toAffineMap - (LinearMap.proj p.1.1).toAffineMap

/-- The finite affine family consisting of every actual defining inequality of the crown order
    polytope. -/
noncomputable def crownAffineSlackFamily (n : ℕ) :
    AffineSlackFamily (Fin (2 * n) → ℝ) (Fintype.card (CrownConstraint n)) where
  slack i := crownConstraintSlack n ((Fintype.equivFin (CrownConstraint n)).symm i)

/-- The nonnegative locus of the actual lower bounds, upper bounds, and crown comparisons is the
    crown order polytope itself. -/
theorem crown_affine_slack_feasible_eq (n : ℕ) :
    (crownAffineSlackFamily n).feasible = crownOrderPolytope n := by
  classical
  ext x
  let e := Fintype.equivFin (CrownConstraint n)
  constructor
  · intro hx
    constructor
    · intro i
      constructor
      · have h := hx (e (Sum.inl i))
        simpa [crownAffineSlackFamily, crownConstraintSlack, e] using h
      · have h := hx (e (Sum.inr (Sum.inl i)))
        simpa [crownAffineSlackFamily, crownConstraintSlack, e] using h
    · intro i j hij
      let p : {p : Fin (2 * n) × Fin (2 * n) // crownRelation n p.1 p.2} :=
        ⟨(i, j), hij⟩
      have h := hx (e (Sum.inr (Sum.inr p)))
      simpa [crownAffineSlackFamily, crownConstraintSlack, e, p] using h
  · rintro ⟨hbounds, horder⟩ i
    let c := e.symm i
    have hi : i = e c := by simp [c]
    rw [hi]
    rcases c with i | i | p
    · simpa [crownAffineSlackFamily, crownConstraintSlack, e] using (hbounds i).1
    · simpa [crownAffineSlackFamily, crownConstraintSlack, e] using (hbounds i).2
    · simpa [crownAffineSlackFamily, crownConstraintSlack, e] using
        (sub_nonneg.mpr (horder p.1.1 p.1.2 p.2))

/-- The actual exposed faces of the crown order polytope, including the empty face and the whole
    polytope. -/
abbrev CrownExposedFace (n : ℕ) :=
  {F : Set (Fin (2 * n) → ℝ) // IsExposed ℝ (crownOrderPolytope n) F}

private noncomputable def crownActiveMask (n : ℕ) (F : Set (Fin (2 * n) → ℝ)) :
    Finset (Fin (Fintype.card (CrownConstraint n))) := by
  classical
  exact Finset.univ.filter fun i => (crownAffineSlackFamily n).tightlyHolds F i

private noncomputable def crownFaceCode (n : ℕ) (F : CrownExposedFace n) :
    Option (Finset (Fin (Fintype.card (CrownConstraint n)))) := by
  classical
  exact if F.1.Nonempty then some (crownActiveMask n F.1) else none

/-- Actual crown exposed faces form a finite family.  Nonempty faces inject into finite masks of
    tight defining inequalities; the empty face occupies the remaining option. -/
theorem finite_crown_exposed_faces (n : ℕ) : Finite (CrownExposedFace n) := by
  classical
  apply Finite.of_injective (crownFaceCode n)
  intro F G hcode
  apply Subtype.ext
  by_cases hF : F.1.Nonempty
  · by_cases hG : G.1.Nonempty
    · have hmask : crownActiveMask n F.1 = crownActiveMask n G.1 := by
        simpa [crownFaceCode, hF, hG] using hcode
      have htight (i : Fin (Fintype.card (CrownConstraint n))) :
          (crownAffineSlackFamily n).tightlyHolds F.1 i ↔
            (crownAffineSlackFamily n).tightlyHolds G.1 i := by
        have hi := Finset.ext_iff.mp hmask i
        simpa [crownActiveMask] using hi
      obtain ⟨f, hf⟩ := hF
      obtain ⟨g, hg⟩ := hG
      have hFex : IsExposed ℝ (crownAffineSlackFamily n).feasible F.1 := by
        simpa [crown_affine_slack_feasible_eq] using F.2
      have hGex : IsExposed ℝ (crownAffineSlackFamily n).feasible G.1 := by
        simpa [crown_affine_slack_feasible_eq] using G.2
      have hFact := exposed_eq_active_of_finite_slacks
        (crownAffineSlackFamily n) F.1 hFex f hf
      have hGact := exposed_eq_active_of_finite_slacks
        (crownAffineSlackFamily n) G.1 hGex g hg
      rw [hFact, hGact]
      ext z
      constructor
      · rintro ⟨hz, hactive⟩
        refine ⟨hz, ?_⟩
        intro i hi
        exact hactive i ((htight i).mpr hi)
      · rintro ⟨hz, hactive⟩
        refine ⟨hz, ?_⟩
        intro i hi
        exact hactive i ((htight i).mp hi)
    · simp [crownFaceCode, hF, hG] at hcode
  · by_cases hG : G.1.Nonempty
    · simp [crownFaceCode, hF, hG] at hcode
    · have hFempty : F.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hF
      have hGempty : G.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hG
      exact hFempty.trans hGempty.symm

/-- The crown augmented by a bottom and a top vertex. -/
inductive CrownAugmentedVertex (n : ℕ)
  | bottom
  | vertex (i : Fin (2 * n))
  | top
  deriving DecidableEq, Fintype

/-- Extend crown coordinates by the fixed bottom coordinate zero and top coordinate one. -/
def augmentedCoordinate {n : ℕ} (x : Fin (2 * n) → ℝ) : CrownAugmentedVertex n → ℝ
  | .bottom => 0
  | .vertex i => x i
  | .top => 1

/-- The source-specific order on the augmented crown.  Since the crown has height two, its only
    nontrivial interior comparisons are the defining crown relations. -/
def crownAugmentedLE {n : ℕ} : CrownAugmentedVertex n → CrownAugmentedVertex n → Prop
  | .bottom, _ => True
  | _, .top => True
  | .vertex i, .vertex j => i = j ∨ crownRelation n i j
  | _, _ => False

/-- Every feasible crown point, extended by zero and one, respects the augmented crown order. -/
theorem augmentedCoordinate_mono {n : ℕ} {x : Fin (2 * n) → ℝ}
    (hx : x ∈ crownOrderPolytope n) {u v : CrownAugmentedVertex n}
    (huv : crownAugmentedLE u v) : augmentedCoordinate x u ≤ augmentedCoordinate x v := by
  cases u with
  | bottom =>
      cases v with
      | bottom => simp [augmentedCoordinate]
      | vertex j => exact (hx.1 j).1
      | top => norm_num [augmentedCoordinate]
  | top =>
      cases v with
      | bottom => simp [crownAugmentedLE] at huv
      | vertex j => simp [crownAugmentedLE] at huv
      | top => simp [augmentedCoordinate]
  | vertex i =>
      cases v with
      | bottom => simp [crownAugmentedLE] at huv
      | top => exact (hx.1 i).2
      | vertex j =>
          rcases huv with hij | hij
          · simpa [hij]
          · exact hx.2 i j hij

/-- Two augmented vertices are tightly related on a face when they are comparable and their
    extended coordinates agree at every point of the face. -/
def crownFaceTightRel {n : ℕ} (F : CrownExposedFace n)
    (u v : CrownAugmentedVertex n) : Prop :=
  crownAugmentedLE u v ∧ ∀ x, x ∈ F.1 → augmentedCoordinate x u = augmentedCoordinate x v

/-- The tight comparable-pair graph of an actual crown exposed face. -/
def crownFaceTightGraph {n : ℕ} (F : CrownExposedFace n) :
    SimpleGraph (CrownAugmentedVertex n) :=
  SimpleGraph.fromRel (crownFaceTightRel F)

theorem crownFaceTightGraph_adj_eq {n : ℕ} (F : CrownExposedFace n)
    {u v : CrownAugmentedVertex n} (huv : (crownFaceTightGraph F).Adj u v)
    {x : Fin (2 * n) → ℝ} (hx : x ∈ F.1) :
    augmentedCoordinate x u = augmentedCoordinate x v := by
  rcases (SimpleGraph.fromRel_adj _ _ _).mp huv with ⟨_, h | h⟩
  · exact h.2 x hx
  · exact (h.2 x hx).symm

/-- Every point of an actual exposed face is constant on each connected block of its tight
    comparable-pair graph. -/
theorem augmentedCoordinate_eq_of_tightComponent {n : ℕ} (F : CrownExposedFace n)
    {u v : CrownAugmentedVertex n}
    (hcomponent : (crownFaceTightGraph F).connectedComponentMk u =
      (crownFaceTightGraph F).connectedComponentMk v)
    {x : Fin (2 * n) → ℝ} (hx : x ∈ F.1) :
    augmentedCoordinate x u = augmentedCoordinate x v := by
  have hreach : (crownFaceTightGraph F).Reachable u v :=
    SimpleGraph.ConnectedComponent.exact hcomponent
  have walk_eq {a b : CrownAugmentedVertex n}
      (p : (crownFaceTightGraph F).Walk a b) :
      augmentedCoordinate x a = augmentedCoordinate x b := by
    induction p with
    | nil => rfl
    | cons h p ih => exact (crownFaceTightGraph_adj_eq F h hx).trans ih
  exact walk_eq hreach.some

end D5.S3.Combinatorics.Geometry.CrownOrderPolytope
