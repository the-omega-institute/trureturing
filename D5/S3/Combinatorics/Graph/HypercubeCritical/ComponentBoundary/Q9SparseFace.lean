/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseFace
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseFace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Universal sparse-weight singularity passes to one actual masked component. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedSpectrum
import Mathlib.Algebra.MvPolynomial.Funext

/-! A fixed masked component for the weighted parity defect in the nine-cube. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q)
open BalancedCubeComponentBoundary (directions mem_directions)
open TwoBalancedComponents (componentFinset)
open Q9IsotropicHuang (parity)
open Q9WeightedBoundaryGram (signed)
open Q9WeightedSaturation (defect)
open Q9ComponentSaturation (componentDefect componentDefect_det_eq componentParityFinset)
open Q9MaskedSpectrum (maskedGraph)

local notation "flip" => BalancedCriticalSpectrum.flip

private abbrev MaskedComponent (I : Finset (Fin 9)) (S : Finset (Q 9)) :=
  ((maskedGraph I).induce (S : Set (Q 9))).ConnectedComponent

open Classical in
/-- The support of a masked component, projected to the ambient nine-cube. -/
def maskedComponentFinset (I : Finset (Fin 9)) (S : Finset (Q 9))
    (K : MaskedComponent I S) : Finset (Q 9) :=
  K.supp.toFinset.image (fun x : (S : Set (Q 9)) => x.val)

private theorem mem_maskedComponentFinset (I : Finset (Fin 9)) (S : Finset (Q 9))
    (K : MaskedComponent I S) (x : Q 9) :
    x ∈ maskedComponentFinset I S K ↔ ∃ hx : x ∈ S, (⟨x, hx⟩ : (S : Set (Q 9))) ∈ K.supp := by
  classical
  simp only [maskedComponentFinset, Finset.mem_image, Set.mem_toFinset]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.property, hv⟩
  · rintro ⟨hx, hxK⟩
    exact ⟨⟨x, hx⟩, hxK, rfl⟩

private abbrev ParitySide (S : Finset (Q 9)) (b : Bool) :=
  ↥(S.filter fun x => parity x = b)

private abbrev inducedVertex {S : Finset (Q 9)} {b : Bool} (x : ParitySide S b) :
    (S : Set (Q 9)) :=
  ⟨x.val, (Finset.mem_filter.mp x.property).1⟩

private def label (I : Finset (Fin 9)) {S : Finset (Q 9)} {b : Bool}
    (x : ParitySide S b) : MaskedComponent I S :=
  ((maskedGraph I).induce (S : Set (Q 9))).connectedComponentMk (inducedVertex x)

/-- The weighted Huang parity defect formed using only the vertices of the given support. -/
def parityDefect {R : Type*} [CommRing R] (w : Fin 9 → R) (S : Finset (Q 9)) (b : Bool) :
    Matrix (ParitySide S b) (ParitySide S b) R :=
  defect w ((signed w).submatrix
    (Subtype.val : ParitySide S b → Q 9) (Subtype.val : ParitySide S (!b) → Q 9))

private theorem eval_parityDefect_det (v : Fin 9 → ℝ)
    (w : Fin 9 → MvPolynomial (Fin 9) ℝ) (S : Finset (Q 9)) (b : Bool) :
    MvPolynomial.eval v (parityDefect w S b).det =
      (parityDefect (fun a => MvPolynomial.eval v (w a)) S b).det := by
  let e := MvPolynomial.eval v
  have hs : (signed w).map e = signed (fun a => e (w a)) := by
    ext x y
    change e (signed w x y) = signed (fun a => e (w a)) x y
    simp only [signed, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  change e _ = _
  rw [RingHom.map_det]
  congr 1
  change (parityDefect w S b).map e = _
  unfold parityDefect defect
  rw [Matrix.map_sub e (map_sub e), Matrix.map_smul' e _ _ (map_mul e),
    Matrix.map_one e (map_zero e) (map_one e), Matrix.map_mul, Matrix.transpose_map]
  simp only [← Matrix.submatrix_map, hs, map_sum, map_pow]
  rfl

private theorem signed_eq_zero_of_not_adj {R : Type*} [CommRing R] {I : Finset (Fin 9)}
    {w : Fin 9 → R} (hw : ∀ a ∉ I, w a = 0) {x y : Q 9}
    (hxy : ¬ (maskedGraph I).Adj x y) : signed w x y = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  by_cases h : flip x a = y
  · have ha : a ∉ I := fun ha => hxy ⟨a, ha, h⟩
    simp [h, hw a ha]
  · simp [h]

private theorem signed_eq_zero_of_ne_label {R : Type*} [CommRing R] {I : Finset (Fin 9)}
    {w : Fin 9 → R} (hw : ∀ a ∉ I, w a = 0) {S : Finset (Q 9)} {b c : Bool}
    {x : ParitySide S b} {y : ParitySide S c} (h : label I x ≠ label I y) :
    signed w x.val y.val = 0 := by
  apply signed_eq_zero_of_not_adj hw
  intro hadj
  apply h
  exact SimpleGraph.ConnectedComponent.sound
    (show ((maskedGraph I).induce (S : Set (Q 9))).Reachable (inducedVertex x) (inducedVertex y)
      from (show ((maskedGraph I).induce (S : Set (Q 9))).Adj (inducedVertex x) (inducedVertex y)
        from hadj).reachable)

private theorem defect_eq_zero_of_ne_label {R : Type*} [CommRing R] {I : Finset (Fin 9)}
    {w : Fin 9 → R} (hw : ∀ a ∉ I, w a = 0) {S : Finset (Q 9)} {b : Bool}
    {x y : ParitySide S b} (h : label I x ≠ label I y) : parityDefect w S b x y = 0 := by
  have hxy : x ≠ y := fun he => h (congrArg (label I) he)
  simp only [parityDefect, defect, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    ite_eq_right hxy, smul_zero, zero_sub, neg_eq_zero, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hx : label I x = label I z
  · rw [signed_eq_zero_of_ne_label hw (fun hy => h (hx.trans hy.symm)), mul_zero]
  · rw [signed_eq_zero_of_ne_label hw hx, zero_mul]

private def parityBlockEquiv (I : Finset (Fin 9)) (S : Finset (Q 9)) (b : Bool)
    (K : MaskedComponent I S) :
    ParitySide (maskedComponentFinset I S K) b ≃ {x : ParitySide S b // label I x = K} where
  toFun x :=
    let h := Finset.mem_filter.mp x.property
    let hx := (mem_maskedComponentFinset I S K x.val).mp h.1
    ⟨⟨x.val, Finset.mem_filter.mpr ⟨hx.choose, h.2⟩⟩, hx.choose_spec⟩
  invFun x := ⟨x.val.val, Finset.mem_filter.mpr
    ⟨(mem_maskedComponentFinset I S K x.val.val).mpr ⟨(inducedVertex x.val).property, x.property⟩,
      (Finset.mem_filter.mp x.val.property).2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

open Classical in
private theorem parityBlock_det {R : Type*} [CommRing R] {I : Finset (Fin 9)}
    {w : Fin 9 → R} (hw : ∀ a ∉ I, w a = 0) (S : Finset (Q 9)) (b : Bool)
    (K : MaskedComponent I S) :
    ((parityDefect w S b).toSquareBlock (label I) K).det =
      (parityDefect w (maskedComponentFinset I S K) b).det := by
  let e := parityBlockEquiv I S b K
  let f := parityBlockEquiv I S (!b) K
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext x y
  simp only [Matrix.toSquareBlock_def, Matrix.submatrix_apply, Matrix.of_apply, parityDefect,
    defect, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  have he : (e x).val = (e y).val ↔ x = y :=
    Subtype.val_injective.eq_iff.trans e.injective.eq_iff
  simp only [he]
  congr 1
  refine (Fintype.sum_of_injective (fun z => (f z).val)
    (fun _ _ hz => f.injective (Subtype.ext hz)) _ _ ?_ (fun _ => rfl)).symm
  intro z hz
  have hne : label I z ≠ K := by
    intro h
    apply hz
    exact ⟨f.symm ⟨z, h⟩, congrArg Subtype.val (f.apply_symm_apply ⟨z, h⟩)⟩
  rw [signed_eq_zero_of_ne_label hw (fun h => hne (h.symm.trans (e x).property)), zero_mul]

private theorem eq_off_mask (I : Finset (Fin 9)) (S : Finset (Q 9))
    (K : MaskedComponent I S) {x y : Q 9}
    (hx : x ∈ maskedComponentFinset I S K) (hy : y ∈ maskedComponentFinset I S K)
    {a : Fin 9} (ha : a ∉ I) : x a = y a := by
  obtain ⟨hxS, hxK⟩ := (mem_maskedComponentFinset I S K x).mp hx
  obtain ⟨hyS, hyK⟩ := (mem_maskedComponentFinset I S K y).mp hy
  let G := (maskedGraph I).induce (S : Set (Q 9))
  let v : (S : Set (Q 9)) := ⟨x, hxS⟩
  let u : (S : Set (Q 9)) := ⟨y, hyS⟩
  have hr : G.Reachable v u := SimpleGraph.ConnectedComponent.exact (hxK.trans hyK.symm)
  have walk_eq {z : (S : Set (Q 9))} (hz : Relation.ReflTransGen G.Adj v z) :
      x a = z.val a := by
    induction hz with
    | refl => rfl
    | @tail z z' _ hstep ih =>
      obtain ⟨i, hi, hflip⟩ := (show (maskedGraph I).Adj z.val z'.val from hstep)
      have hai : a ≠ i := fun h => ha (h.symm ▸ hi)
      rw [← hflip, BalancedCriticalSpectrum.flip, Function.update_of_ne hai]
      exact ih
  exact walk_eq ((SimpleGraph.reachable_iff_reflTransGen v u).mp hr)

private theorem directions_eq_inter (I : Finset (Fin 9)) (S : Finset (Q 9))
    (K : MaskedComponent I S) {x : Q 9} (hx : x ∈ maskedComponentFinset I S K) :
    directions (maskedComponentFinset I S K) x = directions S x ∩ I := by
  obtain ⟨hxS, hxK⟩ := (mem_maskedComponentFinset I S K x).mp hx
  ext a
  simp only [Finset.mem_inter, mem_directions]
  constructor
  · intro h
    refine ⟨((mem_maskedComponentFinset I S K _).mp h).choose, ?_⟩
    by_contra ha
    have he := eq_off_mask I S K hx h ha
    simp [BalancedCriticalSpectrum.flip] at he
  · rintro ⟨haS, haI⟩
    have hadj : ((maskedGraph I).induce (S : Set (Q 9))).Adj
        ⟨x, hxS⟩ ⟨flip x a, haS⟩ := ⟨a, haI, rfl⟩
    exact (mem_maskedComponentFinset I S K _).mpr ⟨haS, (K.mem_supp_congr_adj hadj).mp hxK⟩

private theorem exists_singular_block {R : Type*} [CommRing R] [IsDomain R]
    (I : Finset (Fin 9)) (S : Finset (Q 9)) (b : Bool) (w : Fin 9 → R)
    (hw : ∀ a ∉ I, w a = 0) (hdet : (parityDefect w S b).det = 0) :
    ∃ K : MaskedComponent I S, (parityDefect w (maskedComponentFinset I S K) b).det = 0 := by
  classical
  let e := Finite.equivFin (MaskedComponent I S)
  let : LinearOrder (MaskedComponent I S) := LinearOrder.lift' e e.injective
  let : DecidableEq (MaskedComponent I S) := Classical.decEq _
  have htri : (parityDefect w S b).BlockTriangular (label I) :=
    fun _ _ h => defect_eq_zero_of_ne_label hw (ne_of_gt h)
  have hprod := htri.det.symm.trans hdet
  obtain ⟨K, _, hblock⟩ := Finset.prod_eq_zero_iff.mp hprod
  exact ⟨K, (parityBlock_det hw S b K).symm.trans hblock⟩

open Classical in
private theorem parityDefect_det_eq_component (w : Fin 9 → ℝ) (U : Finset (Q 9)) (b : Bool)
    (C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) :
    (parityDefect w (componentFinset U C) b).det = (componentDefect w U b C).det :=
  (componentDefect_det_eq w U b C).symm

set_option maxHeartbeats 500000 in
-- The matrix indices are finite subtypes of the nine-cube on each parity side.
open Classical in
/-- A single actual masked component inherits singularity for all supported weights.
Its two parity sides are the restrictions of the original sides to its support. -/
theorem exists_fixed_singular_masked_component (U : Finset (Q 9)) (b : Bool)
    (C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) (I : Finset (Fin 9))
    (hdet : ∀ w : Fin 9 → ℝ, (∀ a ∉ I, w a = 0) → (componentDefect w U b C).det = 0) :
    let S := componentFinset U C
    ∃ K : ((maskedGraph I).induce (S : Set (Q 9))).ConnectedComponent,
      let T := maskedComponentFinset I S K
      (∀ w : Fin 9 → ℝ, (∀ a ∉ I, w a = 0) → (parityDefect w T b).det = 0) ∧
      (∀ x ∈ T, directions T x = directions S x ∩ I) ∧
      (∀ p : Bool, T.filter (fun x => parity x = p) = componentParityFinset U p C ∩ T) ∧
      (∀ x ∈ T, ∀ y ∈ T, ∀ a ∉ I, x a = y a) := by
  classical
  let S := componentFinset U C
  let w : Fin 9 → MvPolynomial (Fin 9) ℝ := fun a => if a ∈ I then MvPolynomial.X a else 0
  have hw : ∀ a ∉ I, w a = 0 := fun a ha => ite_eq_right ha
  have hall : (parityDefect w S b).det = 0 := by
    apply MvPolynomial.funext
    intro v
    let u : Fin 9 → ℝ := fun a => MvPolynomial.eval v (w a)
    have hu : ∀ a ∉ I, u a = 0 := fun a ha => by simp [u, hw a ha]
    calc
      _ = (parityDefect u S b).det := eval_parityDefect_det v w S b
      _ = (componentDefect u U b C).det := parityDefect_det_eq_component u U b C
      _ = 0 := hdet u hu
      _ = _ := (map_zero (MvPolynomial.eval v)).symm
  obtain ⟨K, hK⟩ := exists_singular_block I S b w hw hall
  let T := maskedComponentFinset I S K
  refine ⟨K, ?_, fun _ hx => directions_eq_inter I S K hx, ?_,
    fun _ hx _ hy _ ha => eq_off_mask I S K hx hy ha⟩
  · intro v hv
    have he : (fun a => MvPolynomial.eval v (w a)) = v := by
      funext a
      by_cases ha : a ∈ I <;> simp [w, ha, hv]
    calc
      _ = (parityDefect (fun a => MvPolynomial.eval v (w a)) T b).det := by rw [he]
      _ = MvPolynomial.eval v (parityDefect w T b).det := (eval_parityDefect_det v w T b).symm
      _ = 0 := by rw [hK, map_zero]
  · intro p
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter, componentParityFinset]
    exact ⟨fun ⟨hx, hp⟩ =>
      ⟨⟨((mem_maskedComponentFinset I S K _).mp hx).choose, hp⟩, hx⟩,
      fun ⟨⟨_, hp⟩, hx⟩ => ⟨hx, hp⟩⟩

#print axioms exists_fixed_singular_masked_component

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace
