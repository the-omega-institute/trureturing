/- GID: D5/S3/Quantum/Foundation/WeightedRelationConfirmation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/WeightedRelationConfirmation
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Weighted full-pure relations force an attained original mixed-state gap. -/

import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-! Weighted relations and comparison on the original finite pure carrier. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.WeightedRelationConfirmation

open CircuitBalancedConfirmation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

/-- The coordinate map uses every extreme point of the original normalized base. -/
def coordinates (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) [Fintype (pure C u)] :
    (pure C u → ℝ) →ₗ[ℝ] A :=
  Fintype.linearCombination ℝ (fun p : pure C u => (p : A))

/-- Original midpoint gluing of actual proper-effect exclusions, for all mixed states. -/
def zeroGluing (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) : Prop :=
  ∀ (p : pure C u) (x y : A), x ∈ base C u → y ∈ base C u →
    (∃ f, confirms C u p f ∧ f x = 0) →
    (∃ f, confirms C u p f ∧ f y = 0) →
    ∃ f, confirms C u p f ∧ f ((1 / 2 : ℝ) • (x + y)) = 0

private theorem extension_sum {I M : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid M]
    [Module ℝ M] (s : Finset I) (c : s → ℝ) (f : I → M) :
    (∑ q, (if h : q ∈ s then c ⟨q,h⟩ else 0) • f q) =
      ∑ q : s, c q • f q := by
  classical
  calc
    _ = ∑ q ∈ s, (if h : q ∈ s then c ⟨q,h⟩ else 0) • f q := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro q _ hq
      simp [hq]
    _ = ∑ q : s, (if h : (q : I) ∈ s then c ⟨q,h⟩ else 0) • f q :=
      (Finset.sum_coe_sort s _).symm
    _ = _ := Finset.sum_congr rfl (fun q _ => by rw [dif_pos q.property])

/-- Original closedness, strict normalization and generation imply surjectivity;
finite pure spanning is a conclusion. -/
theorem coordinates_surjective (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    [Fintype (pure C u)] (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) :
    Function.Surjective (coordinates C u) := by
  apply LinearMap.range_eq_top.mp
  simpa [coordinates, Fintype.range_linearCombination, Subtype.range_coe_subtype] using
    pure_span (base_compact hclosed hstrict) hstrict hspan

/-- Every full-kernel-annihilating assignment in the unit cube descends to an
original proper effect, and every original proper effect has these properties. -/
theorem full_effect_iff (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    [Fintype (pure C u)] (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) (v : pure C u → ℝ) :
    (∃! f : A →ₗ[ℝ] ℝ, proper C u f ∧ ∀ p : pure C u, f p = v p) ↔
      (∀ p, 0 ≤ v p ∧ v p ≤ 1) ∧
      (∀ w, coordinates C u w = 0 → ∑ p, w p * v p = 0) := by
  classical
  constructor
  · rintro ⟨f, ⟨hf, he⟩, _⟩
    refine ⟨fun p => ?_, fun w hw => ?_⟩
    · simpa [he p, (pure_mem p).2] using hf p (pure_mem p).1
    · have hh := congrArg f hw
      simpa [coordinates, Fintype.linearCombination_apply, map_sum, map_smul,
        smul_eq_mul, he] using hh
  · rintro ⟨hbound, hker⟩
    have hbal : balanced (pure C u) v := by
      intro s c hc
      let w : pure C u → ℝ := fun q => if h : q ∈ s then c ⟨q,h⟩ else 0
      have hw : coordinates C u w = 0 := by
        change (∑ q, w q • (q : A)) = 0
        rw [show (∑ q, w q • (q : A)) = ∑ q : s, c q • (q.1 : A) from
          extension_sum s c (fun q : pure C u => (q : A))]
        exact hc.2.1
      have hh := hker w hw
      have hE := extension_sum s c v
      change (∑ q, w q * v q) = ∑ q : s, c q * v q.1 at hE
      rw [hE] at hh
      exact hh
    obtain ⟨f, hf⟩ := descends hbal (pure_span (base_compact hclosed hstrict) hstrict hspan)
    refine ⟨f, ⟨cone_bound (base_compact hclosed hstrict) hstrict ?_, hf⟩, ?_⟩
    · intro p
      rw [hf]
      exact hbound p
    · intro g hg
      apply LinearMap.ext
      intro x
      obtain ⟨w,rfl⟩ := coordinates_surjective C u hclosed hstrict hspan x
      simp only [coordinates, Fintype.linearCombination_apply, map_sum, map_smul,
        smul_eq_mul, hf, hg.2]

omit [FiniteDimensional ℝ A] in
/-- Applying the original unit detects the affine normalization of every relation. -/
theorem relation_sum_zero {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Fintype (pure C u)] (w : pure C u → ℝ) (hw : coordinates C u w = 0) :
    ∑ p, w p = 0 := by
  have hh := congrArg u hw
  simpa [coordinates, Fintype.linearCombination_apply, map_sum, map_smul,
    (pure_mem _).2] using hh

omit [FiniteDimensional ℝ A] in
/-- A lower bound witnessed by an original confirmer is the attained original
comparison, for any original state, including mixed barycenters. -/
theorem attained_comparison {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    {p x : A} (hx : x ∈ C) (f : A →ₗ[ℝ] ℝ) (hf : confirms C u p f)
    (hlower : ∀ g, confirms C u p g → f x ≤ g x) :
    comparison C u p x = f x := by
  apply le_antisymm
  · exact csInf_le ⟨0, by rintro r ⟨g,hg,rfl⟩; exact (hg.1 x hx).1⟩ ⟨f,hf,rfl⟩
  · exact le_csInf ⟨f x,f,hf,rfl⟩ (by rintro r ⟨g,hg,rfl⟩; exact hlower g hg)


omit [FiniteDimensional ℝ A] in
/-- Extremality forbids a full preparation relation with only one positive vertex. -/
theorem no_single_positive {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Fintype (pure C u)] (w : pure C u → ℝ)
    (hw : coordinates C u w = 0) (q : pure C u) (hq : 0 < w q)
    (hother : ∀ i, i ≠ q → w i ≤ 0) : False := by
  classical
  let s := Finset.univ.erase q
  have hmass : (∑ i ∈ s, -w i) = w q := by
    have hz := relation_sum_zero w hw
    have hh := Finset.sum_erase_add (s := Finset.univ) w (Finset.mem_univ q)
    simp only [Finset.sum_neg_distrib]
    dsimp [s]
    linarith
  have hvec : (∑ i ∈ s, (-w i) • (i : A)) = w q • (q : A) := by
    have hh := Finset.sum_erase_add (s := Finset.univ)
      (fun i : pure C u => w i • (i : A)) (Finset.mem_univ q)
    change (∑ i, w i • (i : A)) = 0 at hw
    rw [hw] at hh
    dsimp [s]
    simp only [neg_smul,Finset.sum_neg_distrib]
    exact neg_eq_iff_add_eq_zero.mpr hh
  have hmem : (q : A) ∈ convexHull ℝ (base C u \ {(q : A)}) := by
    have h := s.centerMass_mem_convexHull (s := base C u \ {(q : A)})
      (z := fun i : pure C u => (i : A))
      (fun i hi => neg_nonneg.mpr (hother i (Finset.ne_of_mem_erase hi)))
      (by simpa [hmass] using hq)
      (fun i hi => ⟨pure_mem i,by
        simpa only [Set.mem_singleton_iff,ne_eq,Subtype.coe_inj] using Finset.ne_of_mem_erase hi⟩)
    simpa only [Finset.centerMass,hmass,hvec,inv_smul_smul₀ hq.ne'] using h
  exact ((base_convex C u).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.mp q.property).2 hmem

/-- A normalized signed relation, including every zero-coefficient original vertex. -/
def relationVector {L R Z : Type*} (α : L → ℝ) (β : R → ℝ) : L ⊕ (R ⊕ Z) → ℝ :=
  Sum.elim α (Sum.elim (fun j => -β j) (fun _ => 0))

private theorem partition_sum {R : Type*} [Fintype R] [DecidableEq R] (β : R → ℝ)
    (J : Finset R) (hβ : ∑ j, β j = 1) :
    ∑ j ∈ Finset.univ \ J, β j = 1 - ∑ j ∈ J, β j := by
  classical
  have h := Finset.sum_sdiff (Finset.subset_univ J) (f := β)
  rw [hβ] at h
  linarith

/-- The full kernel, rather than a relation on a selected subconfiguration,
is the exact condition for transporting a bounded assignment to the original cone. -/
theorem relation_effect {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Fintype (pure C u)] {L R Z : Type*} [Fintype L] [Fintype R] [Fintype Z] [DecidableEq R]
    (e : (L ⊕ (R ⊕ Z)) ≃ pure C u) (α : L → ℝ) (β : R → ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (hkernel : ∀ w : L ⊕ (R ⊕ Z) → ℝ,
      (∑ i, w i • (e i : A)) = 0 ↔ ∃ k : ℝ, w = k • relationVector (Z := Z) α β)
    (v : L ⊕ (R ⊕ Z) → ℝ) (hbound : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hbalance : (∑ i, α i * v (.inl i)) = ∑ j, β j * v (.inr (.inl j))) :
    ∃ f : A →ₗ[ℝ] ℝ, proper C u f ∧ ∀ i, f (e i) = v i := by
  classical
  have hker : ∀ w, coordinates C u w = 0 → ∑ q, w q * v (e.symm q) = 0 := by
    intro w hw
    have hw' : (∑ i, w (e i) • (e i : A)) = 0 := by
      rw [e.sum_comp (fun q : pure C u => w q • (q : A))]
      exact hw
    obtain ⟨k,hk⟩ := (hkernel (fun i => w (e i))).mp hw'
    have hkval (i) : w (e i) = k * relationVector (Z := Z) α β i := by
      simpa using congrFun hk i
    have hh : (∑ i, w (e i) * v i) = 0 := by
      calc
        _ = k * ∑ i, relationVector (Z := Z) α β i * v i := by
          simp only [hkval,Finset.mul_sum,mul_assoc]
        _ = 0 := by
          simp [relationVector,Fintype.sum_sum_type,neg_mul,Finset.sum_neg_distrib,hbalance]
    have hs := e.sum_comp (fun q : pure C u => w q * v (e.symm q))
    have hs' : (∑ i, w (e i) * v i) = ∑ q, w q * v (e.symm q) := by simpa using hs
    exact hs'.symm.trans hh
  obtain ⟨f,⟨hf,he⟩,_⟩ := (full_effect_iff C u hclosed hstrict hspan
    (fun q => v (e.symm q))).mpr ⟨fun q => hbound _, hker⟩
  exact ⟨f,hf,fun i => by simpa using he (e i)⟩

/-- Source barycenters retain their entire weighted groups of right-side vertices. -/
def barycenter {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ} {R : Type*}
    (b : R → pure C u) (β : R → ℝ) (J : Finset R) : A :=
  (∑ j ∈ J, β j)⁻¹ • ∑ j ∈ J, β j • (b j : A)

omit [FiniteDimensional ℝ A] in
private theorem barycenter_mem {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    {R : Type*} (b : R → pure C u) (β : R → ℝ) (J : Finset R)
    (hβ : ∀ j, 0 ≤ β j) (hmass : 0 < ∑ j ∈ J, β j) :
    barycenter b β J ∈ base C u := by
  refine ⟨C.smul_mem (inv_nonneg.mpr hmass.le) ?_, ?_⟩
  · exact C.sum_mem (fun j hj => C.smul_mem (hβ j) (pure_mem (b j)).1)
  · simp [barycenter, map_smul, map_sum, (pure_mem _).2, hmass.ne']

omit [FiniteDimensional ℝ A] in
private theorem normalized_full_kernel {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Fintype (pure C u)] {L R Z : Type*} [Fintype L] [Fintype R] [Fintype Z]
    (e : (L ⊕ (R ⊕ Z)) ≃ pure C u) (α : L → ℝ) (β : R → ℝ)
    (hnullity : Module.finrank ℝ (LinearMap.ker (coordinates C u)) = 1)
    (hrelation : (∑ i, α i • (e (.inl i) : A)) = ∑ j, β j • (e (.inr (.inl j)) : A))
    (p : L) (hp : α p ≠ 0) :
    ∀ w : L ⊕ (R ⊕ Z) → ℝ, (∑ i, w i • (e i : A)) = 0 ↔
      ∃ k : ℝ, w = k • relationVector (Z := Z) α β := by
  classical
  let r : pure C u → ℝ := fun q => relationVector (Z := Z) α β (e.symm q)
  have hr : coordinates C u r = 0 := by
    change (∑ q, r q • (q : A)) = 0
    rw [← e.sum_comp (fun q : pure C u => r q • (q : A))]
    simp [r,relationVector,Fintype.sum_sum_type,neg_smul,Finset.sum_neg_distrib,hrelation]
  have hrne : (⟨r,hr⟩ : LinearMap.ker (coordinates C u)) ≠ 0 := by
    intro he
    have hh := congrFun (congrArg Subtype.val he) (e (.inl p))
    exact hp (by simpa [r,relationVector] using hh)
  have hgenerate := (finrank_eq_one_iff_of_nonzero'
    (⟨r,hr⟩ : LinearMap.ker (coordinates C u)) hrne).mp hnullity
  intro w
  constructor
  · intro hw
    have hw' : coordinates C u (fun q => w (e.symm q)) = 0 := by
      change (∑ q, w (e.symm q) • (q : A)) = 0
      rw [← e.sum_comp (fun q : pure C u => w (e.symm q) • (q : A))]
      simpa using hw
    obtain ⟨k,hk⟩ := hgenerate ⟨_,hw'⟩
    refine ⟨k,funext (fun i => ?_)⟩
    have hh := congrFun (congrArg Subtype.val hk) (e i)
    simpa [r] using hh.symm
  · rintro ⟨k,rfl⟩
    have hrI : (∑ i, relationVector (Z := Z) α β i • (e i : A)) = 0 := by
      simp [relationVector,Fintype.sum_sum_type,neg_smul,Finset.sum_neg_distrib,hrelation]
    change (∑ i, (k * relationVector (Z := Z) α β i) • (e i : A)) = 0
    simp only [mul_smul,← Finset.smul_sum,hrI,smul_zero]

/-- The full source comparison and its three original attaining effects. -/
def partitionGap {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    {L R Z : Type*} [Fintype R] [DecidableEq R]
    (e : (L ⊕ (R ⊕ Z)) ≃ pure C u) (α : L → ℝ) (β : R → ℝ)
    (p : L) (J : Finset R) : Prop :=
    let t := α p
    let b := ∑ j ∈ J, β j
    let x := barycenter (fun j => e (.inr (.inl j))) β J
    let y := barycenter (fun j => e (.inr (.inl j))) β (Finset.univ \ J)
    x ∈ base C u ∧ y ∈ base C u ∧
    comparison C u (e (.inl p)) x = 0 ∧ comparison C u (e (.inl p)) y = 0 ∧
    comparison C u (e (.inl p)) ((1 / 2 : ℝ) • (x + y)) =
      t / (2 * max b (1 - b)) ∧
    0 < t / (2 * max b (1 - b)) ∧
    (∃ f, confirms C u (e (.inl p)) f ∧ f x = 0) ∧
    (∃ f, confirms C u (e (.inl p)) f ∧ f y = 0) ∧
    (∃ f, confirms C u (e (.inl p)) f ∧
      f ((1 / 2 : ℝ) • (x + y)) = t / (2 * max b (1 - b)))

/-- The exact attained comparison gap holds on the original carrier and full
proper interval for every nonempty proper partition, with all free vertices retained. -/
private theorem weighted_partition_gap {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Fintype (pure C u)] {L R Z : Type*} [Fintype L] [Fintype R] [Fintype Z] [DecidableEq R]
    (e : (L ⊕ (R ⊕ Z)) ≃ pure C u) (α : L → ℝ) (β : R → ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (hnullity : Module.finrank ℝ (LinearMap.ker (coordinates C u)) = 1)
    (hrelation : (∑ i, α i • (e (.inl i) : A)) = ∑ j, β j • (e (.inr (.inl j)) : A))
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hβsum : ∑ j, β j = 1)
    (p : L) (hmin : ∀ j, α p ≤ β j)
    (J : Finset R) (hJ : J.Nonempty) (hJc : (Finset.univ \ J).Nonempty) :
    partitionGap e α β p J := by
  classical
  dsimp only [partitionGap]
  have hkernel := normalized_full_kernel e α β hnullity hrelation p (hα p).ne'
  let t := α p
  let b := ∑ j ∈ J, β j
  let d := ∑ j ∈ Finset.univ \ J, β j
  let right : R → pure C u := fun j => e (.inr (.inl j))
  let x := barycenter right β J
  let y := barycenter right β (Finset.univ \ J)
  have ht : 0 < t := hα p
  have hb : 0 < b := Finset.sum_pos (fun j _ => hβ j) hJ
  have hd : 0 < d := Finset.sum_pos (fun j _ => hβ j) hJc
  have hdb : d = 1 - b := partition_sum β J hβsum
  have htb : t ≤ b := by
    obtain ⟨j,hj⟩ := hJ
    exact (hmin j).trans (Finset.single_le_sum (fun i _ => (hβ i).le) hj)
  have htd : t ≤ d := by
    obtain ⟨j,hj⟩ := hJc
    exact (hmin j).trans (Finset.single_le_sum (fun i _ => (hβ i).le) hj)
  have hx := barycenter_mem right β J (fun j => (hβ j).le) hb
  have hy := barycenter_mem right β (Finset.univ \ J) (fun j => (hβ j).le) hd
  let table : ℝ → ℝ → L ⊕ (R ⊕ Z) → ℝ := fun a c =>
    Sum.elim (fun i => if i = p then 1 else 0)
      (Sum.elim (fun j => if j ∈ J then a else c) (fun _ => 0))
  have htable (a c : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
      (hmass : b * a + d * c = t) :
      ∃ f : A →ₗ[ℝ] ℝ, confirms C u (e (.inl p)) f ∧
        f x = a ∧ f y = c := by
    obtain ⟨f,hf,he⟩ := relation_effect e α β hclosed hstrict hspan hkernel
      (table a c) (by
        intro i
        rcases i with i | j
        · by_cases hi : i = p <;> simp [table,hi]
        · rcases j with j | z
          · by_cases hj : j ∈ J <;> simp [table,hj,ha,hc]
          · simp [table]) (by
        have hright : (∑ j, β j * (if j ∈ J then a else c)) = b * a + d * c := by
          simp only [mul_ite, Finset.sum_ite]
          simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
          rw [← Finset.sum_mul,← Finset.sum_mul]
          have hcompl : Finset.univ.filter (fun j : R => j ∉ J) = Finset.univ \ J := by
            ext j
            simp
          rw [hcompl]
        change (∑ i, α i * (if i = p then 1 else 0)) =
          ∑ j, β j * (if j ∈ J then a else c)
        rw [hright]
        simpa [t] using hmass.symm)
    refine ⟨f,⟨hf,by simpa [table] using he (.inl p)⟩,?_,?_⟩
    · have hev (j : R) (hj : j ∈ J) : f (right j) = a := by
        simpa [right,table,hj] using he (.inr (.inl j))
      change f ((∑ j ∈ J, β j)⁻¹ • ∑ j ∈ J, β j • (right j : A)) = a
      simp only [map_smul,map_sum,smul_eq_mul]
      have hsval : (∑ j ∈ J, β j * f (right j)) = (∑ j ∈ J, β j) * a := by
        calc
          _ = ∑ j ∈ J, β j * a := Finset.sum_congr rfl (fun j hj => by rw [hev j hj])
          _ = _ := (Finset.sum_mul _ _ _).symm
      rw [hsval]
      change b⁻¹ * (b*a) = a
      rw [← mul_assoc,inv_mul_cancel₀ hb.ne',one_mul]
    · have hev (j : R) (hj : j ∈ Finset.univ \ J) : f (right j) = c := by
        simpa [right,table,(Finset.mem_sdiff.mp hj).2] using he (.inr (.inl j))
      change f ((∑ j ∈ Finset.univ \ J, β j)⁻¹ • ∑ j ∈ Finset.univ \ J, β j • (right j : A)) = c
      simp only [map_smul,map_sum,smul_eq_mul]
      have hsval : (∑ j ∈ Finset.univ \ J, β j * f (right j)) = (∑ j ∈ Finset.univ \ J, β j) * c := by
        calc
          _ = ∑ j ∈ Finset.univ \ J, β j * c := Finset.sum_congr rfl (fun j hj => by rw [hev j hj])
          _ = _ := (Finset.sum_mul _ _ _).symm
      rw [hsval]
      change d⁻¹ * (d*c) = c
      rw [← mul_assoc,inv_mul_cancel₀ hd.ne',one_mul]
  obtain ⟨fx,hfx,hfxx,hfxy⟩ := htable 0 (t/d) ⟨le_rfl,zero_le_one⟩
    ⟨(div_pos ht hd).le,(div_le_one hd).mpr htd⟩ (by field_simp; ring)
  obtain ⟨fy,hfy,hfyx,hfyy⟩ := htable (t/b) 0
    ⟨(div_pos ht hb).le,(div_le_one hb).mpr htb⟩ ⟨le_rfl,zero_le_one⟩
    (by field_simp; ring)
  have hTx : comparison C u (e (.inl p)) x = 0 := by
    rw [attained_comparison hx.1 fx hfx (fun g hg => by rw [hfxx]; exact (hg.1 x hx.1).1),hfxx]
  have hTy : comparison C u (e (.inl p)) y = 0 := by
    rw [attained_comparison hy.1 fy hfy (fun g hg => by rw [hfyy]; exact (hg.1 y hy.1).1),hfyy]
  have hmid : (1 / 2 : ℝ) • (x+y) ∈ C :=
    C.smul_mem (by norm_num) (C.add_mem hx.1 hy.1)
  have hbound (f : A →ₗ[ℝ] ℝ) (hf : confirms C u (e (.inl p)) f) :
      t / (2 * max b d) ≤ f ((1 / 2 : ℝ) • (x+y)) := by
    let s := ∑ j ∈ J, β j * f (right j)
    let q := ∑ j ∈ Finset.univ \ J, β j * f (right j)
    have hs : 0 ≤ s := Finset.sum_nonneg (fun j _ => mul_nonneg (hβ j).le (hf.1 _ (pure_mem (right j)).1).1)
    have hq : 0 ≤ q := Finset.sum_nonneg (fun j _ => mul_nonneg (hβ j).le (hf.1 _ (pure_mem (right j)).1).1)
    have hrel : (∑ i, α i * f (e (.inl i))) = ∑ j, β j * f (right j) := by
      have hk := (hkernel (relationVector (Z := Z) α β)).mpr ⟨1,by simp⟩
      have hh := congrArg f hk
      simp [relationVector,Fintype.sum_sum_type,map_sum,map_smul,smul_eq_mul,
        Finset.sum_neg_distrib] at hh
      linarith
    have htq : t ≤ s+q := by
      have hi := Finset.single_le_sum (s := Finset.univ) (a := p)
        (fun i _ => mul_nonneg (hα i).le (hf.1 _ (pure_mem (e (.inl i))).1).1) (Finset.mem_univ p)
      rw [hf.2,mul_one,hrel] at hi
      have hsplit := Finset.sum_sdiff (Finset.subset_univ J)
        (f := fun j => β j * f (right j))
      dsimp [s,q]
      linarith
    have hM : 0 < max b d := hb.trans_le (le_max_left _ _)
    have hsdiv := div_le_div_of_nonneg_left hs hb (le_max_left b d)
    have hqdiv := div_le_div_of_nonneg_left hq hd (le_max_right b d)
    have hmass := (div_le_div_iff_of_pos_right hM).mpr htq
    have hfx : f x = s/b := by simp [x,barycenter,map_smul,map_sum,s,b,div_eq_inv_mul]
    have hfy : f y = q/d := by simp [y,barycenter,map_smul,map_sum,q,d,div_eq_inv_mul]
    rw [map_smul,map_add,smul_eq_mul,hfx,hfy]
    rw [add_div] at hmass
    have hhalf : t / (2 * max b d) = (1/2:ℝ) * (t / max b d) := by ring
    rw [hhalf]
    exact mul_le_mul_of_nonneg_left (hmass.trans (add_le_add hsdiv hqdiv)) (by norm_num)
  have hattain : ∃ f, confirms C u (e (.inl p)) f ∧
      f ((1 / 2 : ℝ) • (x+y)) = t/(2*max b d) := by
    by_cases hbd : b ≤ d
    · refine ⟨fx,hfx,?_⟩
      rw [map_smul,map_add,smul_eq_mul,hfxx,hfxy,max_eq_right hbd]
      ring
    · refine ⟨fy,hfy,?_⟩
      rw [map_smul,map_add,smul_eq_mul,hfyx,hfyy,max_eq_left (le_of_not_ge hbd)]
      ring
  obtain ⟨fm,hfm,hfmval⟩ := hattain
  have hTm : comparison C u (e (.inl p)) ((1/2:ℝ) • (x+y)) = t/(2*max b d) := by
    rw [attained_comparison hmid fm hfm (fun g hg => by rw [hfmval]; exact hbound g hg),hfmval]
  have hpos : 0 < t/(2*max b d) := div_pos ht (mul_pos (by norm_num) (hb.trans_le (le_max_left _ _)))
  exact ⟨hx,hy,hTx,hTy,by simpa [hdb] using hTm,by simpa [hdb] using hpos,
    ⟨fx,hfx,hfxx⟩,⟨fy,hfy,hfyy⟩,⟨fm,hfm,by simpa [hdb] using hfmval⟩⟩

/-- Exchange the two nonzero coefficient sides while retaining every free vertex. -/
def exchange {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ} {L R Z : Type*}
    (e : (L ⊕ (R ⊕ Z)) ≃ pure C u) : (R ⊕ (L ⊕ Z)) ≃ pure C u :=
  ({ toFun := Sum.elim (fun j => Sum.inr (Sum.inl j))
        (Sum.elim Sum.inl (fun z => Sum.inr (Sum.inr z)))
     invFun := Sum.elim (fun i => Sum.inr (Sum.inl i))
        (Sum.elim Sum.inl (fun z => Sum.inr (Sum.inr z)))
     left_inv := by intro i; rcases i with i | (i | i) <;> rfl
     right_inv := by intro i; rcases i with i | (i | i) <;> rfl } :
     (R ⊕ (L ⊕ Z)) ≃ (L ⊕ (R ⊕ Z))).trans e

omit [FiniteDimensional ℝ A] in
private theorem normalized_side_size {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Fintype (pure C u)] {L R Z : Type*} [Fintype L] [Fintype R] [Fintype Z]
    (e : (L ⊕ (R ⊕ Z)) ≃ pure C u) (α : L → ℝ) (β : R → ℝ)
    (hrelation : (∑ i, α i • (e (.inl i) : A)) = ∑ j, β j • (e (.inr (.inl j)) : A))
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) (hαsum : ∑ i, α i = 1) :
    2 ≤ Fintype.card L := by
  classical
  by_contra hn
  have hcard : Fintype.card L ≤ 1 := by omega
  have hsingle := Fintype.card_le_one_iff.mp hcard
  have hL : (Finset.univ : Finset L).Nonempty := by
    by_contra hn
    have hz : ∑ i, α i = 0 := Finset.sum_eq_zero (fun i hi => (hn ⟨i,hi⟩).elim)
    linarith
  obtain ⟨p,_⟩ := hL
  let w : pure C u → ℝ := fun q => relationVector (Z := Z) α β (e.symm q)
  have hw : coordinates C u w = 0 := by
    change (∑ q, w q • (q : A)) = 0
    rw [← e.sum_comp (fun q : pure C u => w q • (q : A))]
    simp [w,relationVector,Fintype.sum_sum_type,neg_smul,Finset.sum_neg_distrib,hrelation]
  apply no_single_positive w hw (e (.inl p)) (by simpa [w,relationVector] using hα p)
  intro q hq
  obtain ⟨i,rfl⟩ := e.surjective q
  rcases i with i | (j | z)
  · exact (hq (by rw [hsingle i p])).elim
  · simpa [w,relationVector] using (hβ j).le
  · simp [w,relationVector]

/-- A globally minimal positive coefficient can be placed on the left by exchanging
sides; every nonempty proper right partition then has the attained original gap. -/
theorem weighted_gap_after_exchange {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Fintype (pure C u)] {L R Z : Type*} [Fintype L] [Fintype R] [Fintype Z]
    [DecidableEq L] [DecidableEq R]
    (e : (L ⊕ (R ⊕ Z)) ≃ pure C u) (α : L → ℝ) (β : R → ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (hnullity : Module.finrank ℝ (LinearMap.ker (coordinates C u)) = 1)
    (hrelation : (∑ i, α i • (e (.inl i) : A)) = ∑ j, β j • (e (.inr (.inl j)) : A))
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (hαsum : ∑ i, α i = 1) (hβsum : ∑ j, β j = 1) :
    2 ≤ Fintype.card L ∧ 2 ≤ Fintype.card R ∧
    ∃ p : L ⊕ R, 0 < Sum.elim α β p ∧
      (∀ q, Sum.elim α β p ≤ Sum.elim α β q) ∧
      match p with
      | .inl i => ∀ J : Finset R, J.Nonempty → (Finset.univ \ J).Nonempty →
          partitionGap e α β i J
      | .inr j => ∀ J : Finset L, J.Nonempty → (Finset.univ \ J).Nonempty →
          partitionGap (exchange e) β α j J := by
  classical
  have hrel : (∑ j, β j • (exchange e (.inl j) : A)) =
      ∑ i, α i • (exchange e (.inr (.inl i)) : A) := by
    simpa [exchange] using hrelation.symm
  refine ⟨normalized_side_size e α β hrelation hα hβ hαsum,
    normalized_side_size (exchange e) β α hrel hβ hα hβsum,?_⟩
  have hL : (Finset.univ : Finset L).Nonempty := by
    by_contra hn
    have hz : ∑ i, α i = 0 := Finset.sum_eq_zero (fun i hi => (hn ⟨i,hi⟩).elim)
    linarith
  obtain ⟨i,hi⟩ := hL
  obtain ⟨p,_,hp⟩ := Finset.exists_min_image (Finset.univ : Finset (L ⊕ R))
    (Sum.elim α β) ⟨.inl i,Finset.mem_univ _⟩
  have hmin : ∀ q, Sum.elim α β p ≤ Sum.elim α β q := fun q => hp q (Finset.mem_univ q)
  rcases p with p | p
  · refine ⟨.inl p,hα p,hmin,?_⟩
    intro J hJ hJc
    exact weighted_partition_gap e α β hclosed hstrict hspan hnullity hrelation
      hα hβ hβsum p (fun j => hmin (.inr j)) J hJ hJc
  · refine ⟨.inr p,hβ p,hmin,?_⟩
    intro J hJ hJc
    exact weighted_partition_gap (exchange e) β α hclosed hstrict hspan hnullity hrel
      hβ hα hαsum p (fun i => hmin (.inl i)) J hJ hJc

end D5.S3.Quantum.Foundation.WeightedRelationConfirmation
