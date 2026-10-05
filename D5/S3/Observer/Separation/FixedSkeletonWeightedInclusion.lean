/- GID: D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/FixedSkeletonWeightedInclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: nonnested common-suffix replay
   digest: Suffix replay across nonnested cuts. -/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion

/-- Assignments to the two separately labelled endpoint subsets. -/
def Values {I : Type*} (X Y : I → Type*) (l r : I → Prop) :=
  (∀ i : {i // l i}, X i.val) × (∀ i : {i // r i}, Y i.val)

noncomputable def outputs {I : Type*} {X Y Z : I → Type*}
    (φ : ∀ i, X i → Y i → Z i) (l r : I → Prop)
    (b : Values X Y l r) (s : Values X Y (fun i => ¬l i) (fun i => ¬r i)) :
    ∀ i, Z i := by
  classical
  exact fun i => φ i (if h : l i then b.1 ⟨i,h⟩ else s.1 ⟨i,h⟩)
    (if h : r i then b.2 ⟨i,h⟩ else s.2 ⟨i,h⟩)

noncomputable def response {I O : Type*} {X Y Z : I → Type*}
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i, Z i) → O) (l r : I → Prop)
    (b : Values X Y l r) (s : Values X Y (fun i => ¬l i) (fun i => ¬r i)) : O :=
  G (outputs φ l r b s)

/-- Designated pairs opened by the second cut and untouched by the first. -/
def extra {I : Type*} (designated B₁ P₁ : I → Prop) (i : I) : Prop :=
  designated i ∧ ¬B₁ i ∧ P₁ i

noncomputable def residualOutputs {I : Type*} {X Y Z : I → Type*}
    (φ : ∀ i, X i → Y i → Z i) (B₁ B₂ E : I → Prop)
    (b : Values X Y B₁ B₂) (z : ∀ i : {i // E i}, Z i.val)
    (d : Values X Y (fun i => ¬B₁ i ∧ ¬E i) (fun i => ¬B₂ i ∧ ¬E i)) :
    ∀ i, Z i := by
  classical
  exact fun i => if he : E i then z ⟨i,he⟩ else
    φ i (if h : B₁ i then b.1 ⟨i,h⟩ else d.1 ⟨i,h,he⟩)
      (if h : B₂ i then b.2 ⟨i,h⟩ else d.2 ⟨i,h,he⟩)

/-- Group only designated endpoints read in B and absent from P. -/
def InGroup {I : Type*} {X Y : I → Type*}
    (designated B₁ B₂ P₁ P₂ : I → Prop) (b : Values X Y B₁ B₂)
    (c : Values X Y (fun i => designated i ∧ B₁ i ∧ ¬P₁ i)
      (fun i => designated i ∧ B₂ i ∧ ¬P₂ i)) : Prop :=
  (∀ i (h : designated i ∧ B₁ i ∧ ¬P₁ i), b.1 ⟨i,h.2.1⟩ = c.1 ⟨i,h⟩) ∧
  (∀ i (h : designated i ∧ B₂ i ∧ ¬P₂ i), b.2 ⟨i,h.2.1⟩ = c.2 ⟨i,h⟩)

/-- A single P suffix works for every B prefix in its designated-coordinate group.
The cuts need not be nested. Ordinary completed pairs are encoded through a
surjective column; ordinary untouched pairs opened by P use a surjective row. -/
theorem nonnested_common_suffix_replay
    {I O : Type*} {X Y Z : I → Type*}
    [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)]
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i, Z i) → O)
    (designated B₁ B₂ P₁ P₂ : I → Prop)
    (hB : ∀ i, B₂ i → B₁ i) (hP : ∀ i, P₂ i → P₁ i)
    (hsecond : ∀ i, P₂ i → B₂ i)
    (hfirst : ∀ i, ¬designated i → B₁ i → P₁ i)
    (hordinary : ∀ i, ¬designated i →
      (∃ a : X i, Function.Surjective (φ i a)) ∧
      (∃ b : Y i, Function.Surjective (fun a => φ i a b))) :
    let E := extra designated B₁ P₁
    ∃ q : (∀ i : {i // E i}, X i.val) → Values X Y B₁ B₂ → Values X Y P₁ P₂,
      ∀ (c : Values X Y (fun i => designated i ∧ B₁ i ∧ ¬P₁ i)
          (fun i => designated i ∧ B₂ i ∧ ¬P₂ i))
        (x : ∀ i : {i // E i}, X i.val)
        (z : ∀ i : {i // E i}, Z i.val)
        (d : Values X Y (fun i => ¬B₁ i ∧ ¬E i) (fun i => ¬B₂ i ∧ ¬E i)),
      (∀ i : {i // E i}, ∃ y : Y i.val, φ i.val (x i) y = z i) →
      ∃ s : Values X Y (fun i => ¬P₁ i) (fun i => ¬P₂ i),
        ∀ b : Values X Y B₁ B₂, InGroup designated B₁ B₂ P₁ P₂ b c →
          response φ G P₁ P₂ (q x b) s = G (residualOutputs φ B₁ B₂ E b z d) := by
  classical
  let E := extra designated B₁ P₁
  let aR : ∀ i, X i := fun i => if h : designated i then Classical.choice inferInstance
    else Classical.choose (hordinary i h).1
  let bC : ∀ i, Y i := fun i => if h : designated i then Classical.choice inferInstance
    else Classical.choose (hordinary i h).2
  have row : ∀ i, ¬designated i → Function.Surjective (φ i (aR i)) := by
    intro i hi
    simpa [aR,hi] using Classical.choose_spec (hordinary i hi).1
  have col : ∀ i, ¬designated i → Function.Surjective (fun a => φ i a (bC i)) := by
    intro i hi
    simpa [bC,hi] using Classical.choose_spec (hordinary i hi).2
  let R : ∀ i, Z i → Y i := fun i z => if h : designated i then Classical.choice inferInstance
    else Classical.choose (row i h z)
  let C : ∀ i, Z i → X i := fun i z => if h : designated i then Classical.choice inferInstance
    else Classical.choose (col i h z)
  have row_spec : ∀ i, ¬designated i → ∀ z, φ i (aR i) (R i z) = z := by
    intro i hi z
    simpa [R,hi] using Classical.choose_spec (row i hi z)
  have col_spec : ∀ i, ¬designated i → ∀ z, φ i (C i z) (bC i) = z := by
    intro i hi z
    simpa [C,hi] using Classical.choose_spec (col i hi z)
  let q : (∀ i : {i // E i}, X i.val) → Values X Y B₁ B₂ → Values X Y P₁ P₂ :=
    fun x b =>
      (fun i => if hd : designated i.val then
          if hb : B₁ i.val then b.1 ⟨i.val,hb⟩ else x ⟨i.val,hd,hb,i.property⟩
        else if hb : B₂ i.val then
          if hp : P₂ i.val then b.1 ⟨i.val,hB i.val hb⟩
          else C i.val (φ i.val (b.1 ⟨i.val,hB i.val hb⟩) (b.2 ⟨i.val,hb⟩))
        else if hb : B₁ i.val then b.1 ⟨i.val,hb⟩ else aR i.val,
       fun i => b.2 ⟨i.val,hsecond i.val i.property⟩)
  refine ⟨q, ?_⟩
  intro c x z d hz
  let y : ∀ i : {i // E i}, Y i.val := fun i => Classical.choose (hz i)
  have y_spec : ∀ i : {i // E i}, φ i.val (x i) (y i) = z i :=
    fun i => Classical.choose_spec (hz i)
  let s : Values X Y (fun i => ¬P₁ i) (fun i => ¬P₂ i) :=
    (fun i => if hd : designated i.val then
        if hb : B₁ i.val then c.1 ⟨i.val,hd,hb,i.property⟩
        else d.1 ⟨i.val,hb,fun he => i.property he.2.2⟩
      else d.1 ⟨i.val,fun hb => i.property (hfirst i.val hd hb),fun he => hd he.1⟩,
     fun i => if he : E i.val then y ⟨i.val,he⟩
      else if hd : designated i.val then
        if hb : B₂ i.val then c.2 ⟨i.val,hd,hb,i.property⟩ else d.2 ⟨i.val,hb,he⟩
      else if hb₂ : B₂ i.val then bC i.val
      else if hb₁ : B₁ i.val then d.2 ⟨i.val,hb₂,he⟩
      else if hp : P₁ i.val then
        R i.val (φ i.val (d.1 ⟨i.val,hb₁,he⟩) (d.2 ⟨i.val,hb₂,he⟩))
      else d.2 ⟨i.val,hb₂,he⟩)
  refine ⟨s, ?_⟩
  intro b hg
  apply congrArg G
  funext i
  by_cases hd : designated i
  · by_cases hb₁ : B₁ i
    · have he : ¬E i := fun he => he.2.1 hb₁
      have hc₁ : ∀ hp : ¬P₁ i, c.1 ⟨i,hd,hb₁,hp⟩ = b.1 ⟨i,hb₁⟩ :=
        fun hp => (hg.1 i ⟨hd,hb₁,hp⟩).symm
      have hc₂ : ∀ hb : B₂ i, ∀ hp : ¬P₂ i, c.2 ⟨i,hd,hb,hp⟩ = b.2 ⟨i,hb⟩ :=
        fun hb hp => (hg.2 i ⟨hd,hb,hp⟩).symm
      by_cases hp₁ : P₁ i <;> by_cases hb₂ : B₂ i <;> by_cases hp₂ : P₂ i
      all_goals try { exfalso; exact hp₁ (hP i hp₂) }
      all_goals try { exfalso; exact hb₂ (hsecond i hp₂) }
      all_goals simp [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,hc₁,hc₂]
    · have hb₂ : ¬B₂ i := fun h => hb₁ (hB i h)
      have hp₂ : ¬P₂ i := fun h => hb₂ (hsecond i h)
      by_cases hp₁ : P₁ i
      · have he : E i := ⟨hd,hb₁,hp₁⟩
        simpa [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he] using y_spec ⟨i,he⟩
      · have he : ¬E i := fun h => hp₁ h.2.2
        simp [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he]
  · have he : ¬E i := fun h => hd h.1
    by_cases hb₂ : B₂ i
    · have hb₁ : B₁ i := hB i hb₂
      have hp₁ : P₁ i := hfirst i hd hb₁
      by_cases hp₂ : P₂ i
      · simp [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he]
      · simpa [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he] using
          col_spec i hd (φ i (b.1 ⟨i,hb₁⟩) (b.2 ⟨i,hb₂⟩))
    · have hp₂ : ¬P₂ i := fun h => hb₂ (hsecond i h)
      by_cases hb₁ : B₁ i
      · have hp₁ : P₁ i := hfirst i hd hb₁
        simp [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he]
      · by_cases hp₁ : P₁ i
        · simpa [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he] using
            row_spec i hd (φ i (d.1 ⟨i,hb₁,he⟩) (d.2 ⟨i,hb₂,he⟩))
        · simp [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he]

open Classical in
/-- Actual row-image covering and packing have real extrema against all real feasible vectors.
The two extrema are separate; this statement does not identify their objective values. -/
theorem row_image_real_extrema {X Y Z : Type*} [Fintype X] [Fintype Z]
    (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) :
    (∃ lam : X → ℝ,
      (∀ x, 0 ≤ lam x ∧ lam x ≤ 1) ∧
      (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then lam x else 0) ∧
      ∀ μ : X → ℝ, (∀ x, 0 ≤ μ x) →
        (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then μ x else 0) →
        (∑ x, lam x) ≤ ∑ x, μ x) ∧
    (∃ w : Z → ℝ,
      (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
      (∀ x, (∑ z, if (∃ y, φ x y = z) then w z else 0) ≤ 1) ∧
      ∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
        (∀ x, (∑ z, if (∃ y, φ x y = z) then v z else 0) ≤ 1) →
        (∑ z, v z) ≤ ∑ z, w z) := by
  constructor
  · classical
    let A : X → Z → Prop := fun x z => ∃ y, φ x y = z
    let K : Set (X → ℝ) := {lam | (∀ x, 0 ≤ lam x ∧ lam x ≤ 1) ∧
      ∀ z, 1 ≤ ∑ x, if A x z then lam x else 0}
    have hc : IsClosed K := by
      have heq : K = (⋂ x, {lam : X → ℝ | 0 ≤ lam x ∧ lam x ≤ 1}) ∩
          (⋂ z, {lam : X → ℝ | 1 ≤ ∑ x, if A x z then lam x else 0}) := by
        ext lam
        simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      rw [heq]
      apply IsClosed.inter
      · apply isClosed_iInter
        intro x
        exact (isClosed_le continuous_const (continuous_apply x)).inter
          (isClosed_le (continuous_apply x) continuous_const)
      · apply isClosed_iInter
        intro z
        apply isClosed_le continuous_const
        apply continuous_finsetSum
        intro x hx
        by_cases h : A x z <;> simp only [h, if_true, if_false]
        · exact continuous_apply x
        · exact continuous_const
    have hk : IsCompact K := isCompact_Icc.of_isClosed_subset hc (by
      intro lam hlam
      exact ⟨fun x => (hlam.1 x).1, fun x => (hlam.1 x).2⟩)
    have hn : K.Nonempty := by
      refine ⟨fun _ => 1, (fun x => ⟨zero_le_one, le_rfl⟩), ?_⟩
      intro z
      obtain ⟨x,y,hxy⟩ := hφ z
      have ha : A x z := ⟨y,hxy⟩
      calc
        (1 : ℝ) = (if A x z then 1 else 0) := by simp [ha]
        _ ≤ ∑ u : X, if A u z then (1 : ℝ) else 0 :=
          by
            simpa using (Finset.single_le_sum (s := Finset.univ)
              (f := fun u : X => if A u z then (1 : ℝ) else 0)
              (fun u _ => by split_ifs <;> positivity) (Finset.mem_univ x))
    obtain ⟨lam,hlam,hmin⟩ := hk.exists_isMinOn hn
      (show Continuous (fun lam : X → ℝ => ∑ x, lam x) by fun_prop).continuousOn
    refine ⟨lam,hlam.1,hlam.2,?_⟩
    intro μ hμ hcover
    let ν : X → ℝ := fun x => min (μ x) 1
    have hν : ν ∈ K := by
      refine ⟨fun x => ⟨le_min (hμ x) zero_le_one, min_le_right _ _⟩,?_⟩
      intro z
      by_cases hlarge : ∃ x, A x z ∧ 1 ≤ μ x
      · obtain ⟨x,ha,hx⟩ := hlarge
        calc
          (1 : ℝ) = (if A x z then ν x else 0) := by simp [ha,ν,min_eq_right hx]
          _ ≤ ∑ u : X, if A u z then ν u else 0 :=
            by
              simpa using (Finset.single_le_sum (s := Finset.univ)
                (f := fun u : X => if A u z then ν u else 0)
                (fun u _ => by
                  split_ifs
                  · exact le_min (hμ u) zero_le_one
                  · exact le_rfl) (Finset.mem_univ x))
      · have he : (∑ x, if A x z then ν x else 0) =
            ∑ x, if A x z then μ x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases ha : A x z
          · have hlt : μ x < 1 := lt_of_not_ge (fun h => hlarge ⟨x,ha,h⟩)
            simp [ha,ν,min_eq_left hlt.le]
          · simp [ha]
        rw [he]
        exact hcover z
    exact (hmin hν).trans (Finset.sum_le_sum (fun x _ => min_le_left (μ x) 1))
  · classical
    let A : X → Z → Prop := fun x z => ∃ y, φ x y = z
    let K : Set (Z → ℝ) := {w | (∀ z, 0 ≤ w z) ∧
      ∀ x, (∑ z, if A x z then w z else 0) ≤ 1}
    have hc : IsClosed K := by
      have heq : K = (⋂ z, {w : Z → ℝ | 0 ≤ w z}) ∩
          (⋂ x, {w : Z → ℝ | (∑ z, if A x z then w z else 0) ≤ 1}) := by
        ext w
        simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      rw [heq]
      apply IsClosed.inter
      · exact isClosed_iInter (fun z => isClosed_le continuous_const (continuous_apply z))
      · apply isClosed_iInter
        intro x
        apply isClosed_le _ continuous_const
        apply continuous_finsetSum
        intro z hz
        by_cases h : A x z <;> simp only [h, if_true, if_false]
        · exact continuous_apply z
        · exact continuous_const
    have hbound : ∀ w ∈ K, ∀ z, w z ≤ 1 := by
      intro w hw z
      obtain ⟨x,y,hxy⟩ := hφ z
      have ha : A x z := ⟨y,hxy⟩
      calc
        w z = (if A x z then w z else 0) := by simp [ha]
        _ ≤ ∑ u : Z, if A x u then w u else 0 :=
          by
            simpa using (Finset.single_le_sum (s := Finset.univ)
              (f := fun u : Z => if A x u then w u else 0)
              (fun u _ => by
              split_ifs
              · exact hw.1 u
              · exact le_rfl) (Finset.mem_univ z))
        _ ≤ 1 := hw.2 x
    have hk : IsCompact K := isCompact_Icc.of_isClosed_subset hc (by
      intro w hw
      exact ⟨hw.1, hbound w hw⟩)
    have hn : K.Nonempty := ⟨fun _ => 0, (fun _ => le_rfl), by simp⟩
    obtain ⟨w,hw,hmax⟩ := hk.exists_isMaxOn hn
      (show Continuous (fun w : Z → ℝ => ∑ z, w z) by fun_prop).continuousOn
    exact ⟨w,(fun z => ⟨hw.1 z,hbound w hw z⟩),hw.2,
      fun v hv hc => hmax ⟨hv,hc⟩⟩

open Classical in
/-- Actual row-image incidence admits equal real cover and packing optima.
Both optimizing comparisons range over every real feasible competitor. -/
theorem row_image_real_duality {X Y Z : Type*} [Fintype X] [Fintype Z] [Nonempty Z]
    (φ : X → Y → Z) (hφ : ∀ z, ∃ x y, φ x y = z) :
    ∃ lam : X → ℝ, ∃ w : Z → ℝ,
      (∀ x, 0 ≤ lam x) ∧
      (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then lam x else 0) ∧
      (∀ z, 0 ≤ w z) ∧
      (∀ x, (∑ z, if (∃ y, φ x y = z) then w z else 0) ≤ 1) ∧
      (∑ x, lam x) = (∑ z, w z) ∧
      (∀ μ : X → ℝ, (∀ x, 0 ≤ μ x) →
        (∀ z, 1 ≤ ∑ x, if (∃ y, φ x y = z) then μ x else 0) →
        (∑ x, lam x) ≤ ∑ x, μ x) ∧
      (∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
        (∀ x, (∑ z, if (∃ y, φ x y = z) then v z else 0) ≤ 1) →
        (∑ z, v z) ≤ ∑ z, w z) := by
  classical
  obtain ⟨lam,hlam,hcover,hmin⟩ := (row_image_real_extrema φ hφ).1
  let A : X → Z → Prop := fun x z => ∃ y, φ x y = z
  let τ : ℝ := ∑ x, lam x
  have hτ : 0 < τ := by
    have hz := hcover (Classical.arbitrary Z)
    have hs : (∑ x, if A x (Classical.arbitrary Z) then lam x else 0) ≤ τ := by
      apply Finset.sum_le_sum
      intro x hx
      split_ifs
      · exact le_rfl
      · exact (hlam x).1
    linarith
  let γ := τ⁻¹
  have hγ : 0 < γ := inv_pos.mpr hτ
  let L : (X → ℝ) →ₗ[ℝ] (Z → ℝ) := {
    toFun := fun p z => ∑ x, if A x z then p x else 0
    map_add' := by
      intro p q
      funext z
      change (∑ x, if A x z then p x + q x else 0) =
        (∑ x, if A x z then p x else 0) + ∑ x, if A x z then q x else 0
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp
    map_smul' := by
      intro c p
      funext z
      change (∑ x, if A x z then c * p x else 0) =
        c * ∑ x, if A x z then p x else 0
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp }
  let K := L '' stdSimplex ℝ X
  let U : Set (Z → ℝ) := {v | ∀ z, γ < v z}
  have hUeq : U = ⋂ z, {v : Z → ℝ | γ < v z} := by
    ext v; simp [U]
  have hUconv : Convex ℝ U := by
    rw [hUeq]
    apply convex_iInter
    intro z
    exact (show Convex ℝ (Set.Ioi γ) from convex_Ioi γ).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Z => ℝ) z)
  have hUopen : IsOpen U := by
    rw [hUeq]
    exact isOpen_iInter_of_finite (fun z => isOpen_lt continuous_const (continuous_apply z))
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ X).linear_image L
  have hdisj : Disjoint U K := by
    apply Set.disjoint_left.mpr
    intro k hkU hkK
    obtain ⟨p,hp,rfl⟩ := hkK
    let V := Finset.univ.image (L p)
    have hV : V.Nonempty := ⟨L p (Classical.arbitrary Z), Finset.mem_image.mpr
      ⟨Classical.arbitrary Z,Finset.mem_univ _,rfl⟩⟩
    let β := V.min' hV
    have hγβ : γ < β := by
      obtain ⟨z,hz,hval⟩ := Finset.mem_image.mp (Finset.min'_mem V hV)
      change γ < V.min' hV
      rw [← hval]
      exact hkU z
    have hβ : 0 < β := hγ.trans hγβ
    have hβle : ∀ z, β ≤ L p z := fun z => Finset.min'_le V _
      (Finset.mem_image.mpr ⟨z,Finset.mem_univ z,rfl⟩)
    have hμcover : ∀ z, 1 ≤ ∑ x, if A x z then p x / β else 0 := by
      intro z
      have he : (∑ x, if A x z then p x / β else 0) = L p z / β := by
        dsimp [L]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs <;> simp
      rw [he]
      exact (le_div_iff₀ hβ).mpr (by simpa using hβle z)
    have hm := hmin (fun x => p x / β) (fun x => div_nonneg (hp.1 x) hβ.le) hμcover
    have hsum : (∑ x, p x / β) = β⁻¹ := by rw [← Finset.sum_div, hp.2, one_div]
    have hlt : β⁻¹ < τ := by
      have hh := (inv_lt_inv₀ hβ hγ).mpr hγβ
      simpa [γ] using hh
    rw [hsum] at hm
    exact (not_lt_of_ge hm hlt)
  obtain ⟨f,u,hfu,hfk⟩ := geometric_hahn_banach_open hUconv hUopen hKconv hdisj
  let a : Z → ℝ := fun z => - f (Pi.single z 1)
  have frep : ∀ v : Z → ℝ, f v = ∑ z, f (Pi.single z 1) * v z := by
    intro v
    have hv : v = ∑ z, v z • (Pi.single z 1) := by
      funext z
      simp [Finset.sum_apply,Pi.single_apply]
    calc
      f v = f (∑ z, v z • Pi.single z 1) := congrArg f hv
      _ = ∑ z, f (Pi.single z 1) * v z := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro z hz
        simp [map_smul,smul_eq_mul,mul_comm]
  have ha : ∀ z, 0 ≤ a z := by
    intro z
    change 0 ≤ - f (Pi.single z 1)
    apply neg_nonneg.mpr
    by_contra hn
    have hf : 0 < f (Pi.single z 1) := lt_of_not_ge hn
    let v₀ : Z → ℝ := fun _ => γ + 1
    have h₀ : v₀ ∈ U := by intro j; dsimp [v₀]; linarith
    have hbase := hfu v₀ h₀
    let t := (u - f v₀ + 1) / f (Pi.single z 1)
    have ht : 0 ≤ t := div_nonneg (by linarith) hf.le
    have hv : v₀ + t • Pi.single z 1 ∈ U := by
      intro j
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      by_cases hj : j = z
      · subst j; simp [v₀] <;> linarith
      · simp [v₀,Pi.single_eq_of_ne hj]
    have hsep := hfu _ hv
    have he : f (v₀ + t • Pi.single z 1) = u + 1 := by
      rw [map_add,map_smul]
      change f v₀ + ((u - f v₀ + 1) / f (Pi.single z 1)) * f (Pi.single z 1) = u + 1
      field_simp <;> ring
    linarith
  let S := ∑ z, a z
  have hS : 0 < S := by
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun z _ => ha z)
    by_contra hn
    have hzero : S = 0 := le_antisymm (le_of_not_gt hn) hS0
    have haz : ∀ z, a z = 0 := fun z =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => ha z)).mp hzero z (Finset.mem_univ z)
    have hfzero : ∀ v : Z → ℝ, f v = 0 := by
      intro v
      rw [frep]
      have he : ∀ z, f (Pi.single z 1) = 0 := fun z => neg_eq_zero.mp (haz z)
      simp [he]
    obtain ⟨x,y,hxy⟩ := hφ (Classical.arbitrary Z)
    have hleft := hfu (fun _ => γ + 1) (by intro z; linarith)
    have hright := hfk (L (Pi.single x 1))
      (Set.mem_image_of_mem L (single_mem_stdSimplex ℝ x))
    rw [hfzero] at hleft hright
    linarith
  have hb : ∀ k ∈ K, (∑ z, a z * k z) ≤ γ * S := by
    intro k hk
    by_contra hn
    have hg : γ * S < ∑ z, a z * k z := lt_of_not_ge hn
    let ε := ((∑ z, a z * k z) / S - γ) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      have hgt : γ < (∑ z, a z * k z) / S := (lt_div_iff₀ hS).mpr hg
      linarith
    have hv : (fun _ : Z => γ + ε) ∈ U := by intro z; linarith
    have hleft := hfu _ hv
    have hright := hfk k hk
    rw [frep] at hleft hright
    have hfconst : (∑ z, f (Pi.single z 1) * (γ + ε)) = -(S * (γ + ε)) := by
      rw [Finset.sum_mul]
      simp [a,Finset.sum_neg_distrib]
    have hfkneg : (∑ z, f (Pi.single z 1) * k z) = -(∑ z, a z * k z) := by
      dsimp [a]
      simp [Finset.sum_neg_distrib]
    rw [hfconst] at hleft
    rw [hfkneg] at hright
    have hεeq : S * ε = ((∑ z, a z * k z) - S * γ) / 2 := by
      dsimp [ε]; field_simp
    nlinarith
  let w : Z → ℝ := fun z => a z / (γ * S)
  have hw : ∀ z, 0 ≤ w z := fun z => div_nonneg (ha z) (mul_pos hγ hS).le
  have hload : ∀ x, (∑ z, if A x z then w z else 0) ≤ 1 := by
    intro x
    have hbcol := hb (L (Pi.single x 1)) (Set.mem_image_of_mem L (single_mem_stdSimplex ℝ x))
    have he : (∑ z, if A x z then w z else 0) =
        (∑ z, a z * L (Pi.single x 1) z) / (γ * S) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z hz
      have hL : L (Pi.single x 1) z = if A x z then 1 else 0 := by
        dsimp [L]
        rw [Finset.sum_eq_single x]
        · simp
        · intro b hb hbx
          simp [Pi.single_eq_of_ne hbx]
        · simp
      rw [hL]
      by_cases har : A x z <;> simp [har,w]
    rw [he]
    exact (div_le_one (mul_pos hγ hS)).mpr hbcol
  have heq : (∑ z, w z) = τ := by
    dsimp [w]
    rw [← Finset.sum_div]
    change S / (γ * S) = τ
    dsimp [γ]
    field_simp
  have hweak : ∀ v : Z → ℝ, (∀ z, 0 ≤ v z) →
      (∀ x, (∑ z, if A x z then v z else 0) ≤ 1) → (∑ z, v z) ≤ τ := by
    intro v hv hvl
    calc
      (∑ z, v z) = ∑ z, v z * 1 := by simp
      _ ≤ ∑ z, v z * (∑ x, if A x z then lam x else 0) := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul_of_nonneg_left (hcover z) (hv z)
      _ = ∑ x, lam x * (∑ z, if A x z then v z else 0) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro z hz
        split_ifs <;> ring
      _ ≤ ∑ x, lam x * 1 := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hvl x) (hlam x).1
      _ = τ := by simp [τ]
  refine ⟨lam,w,(fun x => (hlam x).1),hcover,hw,hload,heq.symm,hmin,?_⟩
  intro v hv hvl
  rw [heq]
  exact hweak v hv hvl

end D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion
