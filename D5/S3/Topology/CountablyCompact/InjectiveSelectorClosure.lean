/- GID: D5/S3/Topology/CountablyCompact/InjectiveSelectorClosure
   generality: G
   mirror-B: D5/B/S3/Topology/CountablyCompact/InjectiveSelectorClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transfinite closing-off with globally fresh selector values. -/

import Mathlib.Topology.Compactness.CountablyCompact
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Regular

open Set Filter Topology Cardinal

namespace D5.S3.Topology.CountablyCompact.InjectiveSelectorClosure

/-- Fresh representatives are constructed along a well-order of the task type.
The forbidden values include the seed and all preceding representatives. -/
theorem exists_fresh_choice {X B I : Type} (q : X → B) (A : I → Set X)
    (H : Set X) (hI : #I ≤ 𝔠) (hH : #H ≤ 𝔠)
    (hsupply : ∀ i (F : Set B), #F ≤ 𝔠 → ∃ x ∈ A i, q x ∉ F) :
    ∃ f : I → X, (∀ i, f i ∈ A i) ∧ Function.Injective (q ∘ f) ∧
      (∀ i, q (f i) ∉ q '' H) := by
  classical
  let r : I → I → Prop := WellOrderingRel
  have wf : WellFounded r := WellOrderingRel.isWellOrder.wf
  have supply (i : I) (g : ∀ j, r j i → X) :
      ∃ x ∈ A i, q x ∉ q '' H ∪ range (fun j : {j // r j i} => q (g j.1 j.2)) := by
    apply hsupply
    calc
      _ ≤ #(q '' H) + #(range (fun j : {j // r j i} => q (g j.1 j.2))) := mk_union_le _ _
      _ ≤ 𝔠 + 𝔠 := add_le_add (mk_image_le.trans hH)
        (mk_range_le.trans ((mk_subtype_le _).trans hI))
      _ = 𝔠 := continuum_add_self
  let pick (i : I) (g : ∀ j, r j i → X) : X := (supply i g).choose
  let f : I → X := wf.fix pick
  have spec (i : I) : f i ∈ A i ∧
      q (f i) ∉ q '' H ∪ range (fun j : {j // r j i} => q (f j.1)) := by
    have eqn : f i = pick i (fun j _ => f j) := wf.fix_eq pick i
    rw [eqn]
    exact (supply i (fun j _ => f j)).choose_spec
  refine ⟨f, fun i => (spec i).1, ?_, fun i h => (spec i).2 (Or.inl h)⟩
  intro i j hij
  rcases trichotomous_of r i j with h | h | h
  · exact False.elim ((spec j).2 (Or.inr ⟨⟨i, h⟩, hij⟩))
  · exact h
  · exact False.elim ((spec i).2 (Or.inr ⟨⟨j, h⟩, hij.symm⟩))

/-- Individual fresh ambient accumulation points, with no continuity requirement on `q`. -/
def FreshClusterSupply {X B : Type} [TopologicalSpace X]
    (good : Set X) (q : X → B) : Prop :=
  ∀ e : ℕ ↪ X, range e ⊆ good → Function.Injective (q ∘ e) →
    ∀ F : Set B, #F ≤ 𝔠 → ∃ x ∈ good, AccPt x (𝓟 (range e)) ∧ q x ∉ F

/-- One simultaneous step processes precisely the embeddings into the input set. -/
private theorem accumulation_step {X B : Type} [TopologicalSpace X]
    (good : Set X) (q : X → B) (hsupply : FreshClusterSupply good q)
    (S : Set X) (hgood : S ⊆ good) (hsmall : #S ≤ 𝔠) (hinj : InjOn q S) :
    ∃ T : Set X, S ⊆ T ∧ T ⊆ good ∧ #T ≤ 𝔠 ∧ InjOn q T ∧
      ∀ e : ℕ ↪ S, ∃ x ∈ T, AccPt x (𝓟 (range (fun n => (e n).val))) := by
  classical
  let I := ℕ ↪ S
  let emb (e : I) : ℕ ↪ X := e.trans (Function.Embedding.subtype S)
  have hI : #I ≤ 𝔠 := by
    calc
      #I ≤ #(ℕ → S) := mk_embedding_le_arrow _ _
      _ = #S ^ ℵ₀ := by simp
      _ ≤ 𝔠 ^ ℵ₀ := power_le_power_right hsmall
      _ = 𝔠 := continuum_power_aleph0
  let A (e : I) : Set X := {x | x ∈ good ∧ AccPt x (𝓟 (range (emb e)))}
  have hA : ∀ e (F : Set B), #F ≤ 𝔠 → ∃ x ∈ A e, q x ∉ F := by
    intro e F hF
    obtain ⟨x, hx, hacc, hfresh⟩ := hsupply (emb e)
      (by rintro _ ⟨n, rfl⟩; exact hgood (e n).property)
      (by intro n m h; exact e.injective (Subtype.ext (hinj (e n).property (e m).property h))) F hF
    exact ⟨x, ⟨hx, hacc⟩, hfresh⟩
  obtain ⟨f, hf, hf_inj, hfresh⟩ := exists_fresh_choice q A S hI hsmall hA
  refine ⟨S ∪ range f, subset_union_left, ?_, ?_, ?_, ?_⟩
  · rintro x (hx | ⟨e, rfl⟩)
    · exact hgood hx
    · exact (hf e).1
  · calc
      _ ≤ #S + #(range f) := mk_union_le _ _
      _ ≤ 𝔠 + 𝔠 := add_le_add hsmall (mk_range_le.trans hI)
      _ = 𝔠 := continuum_add_self
  · rintro x (hx | ⟨e, rfl⟩) y (hy | ⟨d, rfl⟩) hxy
    · exact hinj hx hy hxy
    · exact False.elim (hfresh d ⟨x, hx, hxy⟩)
    · exact False.elim (hfresh e ⟨y, hy, hxy.symm⟩)
    · exact congrArg f (hf_inj hxy)
  · intro e
    exact ⟨f e, Or.inr ⟨e, rfl⟩, (hf e).2⟩

private theorem small_iUnion {X I : Type} (T : I → Set X)
    (hI : #I ≤ 𝔠) (hT : ∀ i, #(T i) ≤ 𝔠) : #(⋃ i, T i) ≤ 𝔠 := by
  calc
    _ ≤ #I * ⨆ i, #(T i) := mk_iUnion_le T
    _ ≤ 𝔠 * 𝔠 := mul_le_mul' hI (ciSup_le' hT)
    _ = 𝔠 := continuum_mul_self

/-- A seed together with a chain of small injective good sets remains admissible. -/
private theorem seed_chain_union {X B I : Type} (good : Set X) (q : X → B)
    (seed : Set X) (T : I → Set X)
    (hs : seed ⊆ good ∧ #seed ≤ 𝔠 ∧ InjOn q seed)
    (hI : #I ≤ 𝔠) (hT : ∀ i, T i ⊆ good ∧ #(T i) ≤ 𝔠 ∧ InjOn q (T i))
    (hseed : ∀ i, seed ⊆ T i)
    (hchain : ∀ i j, T i ⊆ T j ∨ T j ⊆ T i) :
    (seed ∪ ⋃ i, T i) ⊆ good ∧ #(seed ∪ ⋃ i, T i : Set X) ≤ 𝔠 ∧
      InjOn q (seed ∪ ⋃ i, T i) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x (hx | hx)
    · exact hs.1 hx
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact (hT i).1 hi
  · calc
      _ ≤ #seed + #(⋃ i, T i) := mk_union_le _ _
      _ ≤ 𝔠 + 𝔠 := add_le_add hs.2.1 (small_iUnion T hI (fun i => (hT i).2.1))
      _ = 𝔠 := continuum_add_self
  · let U : Option I → Set X := fun i => i.elim seed T
    have hdir : Directed (· ⊆ ·) U := by
      intro i j
      cases i with
      | none =>
        cases j with
        | none => exact ⟨none, subset_rfl, subset_rfl⟩
        | some j => exact ⟨some j, hseed j, subset_rfl⟩
      | some i =>
        cases j with
        | none => exact ⟨some i, subset_rfl, hseed i⟩
        | some j =>
          rcases hchain i j with h | h
          · exact ⟨some j, h, subset_rfl⟩
          · exact ⟨some i, subset_rfl, h⟩
    have hU : ∀ i, InjOn q (U i) := by
      intro i
      cases i with
      | none => exact hs.2.2
      | some i => exact (hT i).2.2
    simpa [U, iUnion_option] using inj_on_iUnion_of_directed hdir hU

/-- Every small good injective seed has an actual countably compact injective extension.
The only supply premise concerns one embedding and one small forbidden set at a time. -/
theorem exists_countablyCompact_injOn_extension {X B : Type}
    [TopologicalSpace X] [T1Space X] (good : Set X) (q : X → B)
    (hsupply : FreshClusterSupply good q) (seed : Set X)
    (hgood : seed ⊆ good) (hsmall : #seed ≤ 𝔠) (hinj : InjOn q seed) :
    ∃ S : Set X, seed ⊆ S ∧ S ⊆ good ∧ #S ≤ 𝔠 ∧ InjOn q S ∧ IsCountablyCompact S := by
  classical
  let admissible (S : Set X) := S ⊆ good ∧ #S ≤ 𝔠 ∧ InjOn q S
  have step (S : Set X) (hS : admissible S) :=
    accumulation_step good q hsupply S hS.1 hS.2.1 hS.2.2
  let next (S : Set X) : Set X := if hS : admissible S then (step S hS).choose else S
  have next_spec (S : Set X) (hS : admissible S) :
      S ⊆ next S ∧ admissible (next S) ∧
        ∀ e : ℕ ↪ S, ∃ x ∈ next S, AccPt x (𝓟 (range (fun n => (e n).val))) := by
    simpa only [next, dif_pos hS, admissible, and_assoc] using (step S hS).choose_spec
  have extensive (S : Set X) : S ⊆ next S := by
    by_cases hS : admissible S
    · exact (next_spec S hS).1
    · simp only [next, dif_neg hS, subset_refl]
  let W := (Ordinal.omega.{0} 1).ToType
  have hW : #W ≤ 𝔠 := by
    simpa only [W, mk_toType, Ordinal.card_omega] using aleph_one_le_continuum
  have : Nonempty W := ⟨Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩⟩
  let : OrderBot W := WellFoundedLT.toOrderBot W
  have : NoMaxOrder W := by
    apply Ordinal.isSuccPrelimit_type_lt_iff.mp
    rw [Ordinal.type_toType]
    exact (isSuccLimit_omega 1).isSuccPrelimit
  let stage : W → Set X := WellFoundedLT.fix fun i prev =>
    seed ∪ ⋃ j : Iio i, next (prev j.1 j.2)
  have stage_eq (i : W) : stage i = seed ∪ ⋃ j : Iio i, next (stage j.1) :=
    WellFoundedLT.fix_eq _ _
  have seed_stage (i : W) : seed ⊆ stage i := by
    rw [stage_eq]
    exact subset_union_left
  have next_stage {i j : W} (h : i < j) : next (stage i) ⊆ stage j := by
    rw [stage_eq j]
    exact subset_union_of_subset_right (subset_iUnion (fun k : Iio j => next (stage k.1)) ⟨i, h⟩) _
  have stage_mono : Monotone stage := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | h
    · exact subset_rfl
    · exact (extensive _).trans (next_stage h)
  have stage_zero : stage ⊥ = seed := by
    rw [stage_eq]
    simp
  have stage_succ (i : W) : stage (Order.succ i) = next (stage i) := by
    rw [stage_eq]
    apply Subset.antisymm
    · apply union_subset ((seed_stage i).trans (extensive _))
      apply iUnion_subset
      intro j
      have hj : j.val ≤ i := (show j.val < Order.succ i ↔ j.val ≤ i from Order.lt_succ_iff).mp j.2
      rcases hj.eq_or_lt with h | h
      · simpa only [h] using (subset_refl (next (stage i)))
      · exact (next_stage h).trans (extensive _)
    · rw [← stage_eq (Order.succ i)]
      exact next_stage (Order.lt_succ i)
  have stage_limit (i : W) (hi : Order.IsSuccLimit i) :
      stage i = ⋃ j : Iio i, stage j.1 := by
    apply Subset.antisymm
    · rw [stage_eq]
      apply union_subset
      · obtain ⟨j, hj⟩ := not_isMin_iff.mp hi.not_isMin
        exact (seed_stage j).trans (subset_iUnion (fun j : Iio i => stage j.1) ⟨j, hj⟩)
      · apply iUnion_subset
        intro j
        have hj : Order.succ j.1 < i := hi.succ_lt j.2
        rw [← stage_succ]
        exact subset_iUnion (fun j : Iio i => stage j.1) ⟨Order.succ j.1, hj⟩
    · exact iUnion_subset fun j => stage_mono j.2.le
  have stage_admissible (i : W) : admissible (stage i) := by
    refine SuccOrder.limitRecOn (motive := fun i => admissible (stage i)) i ?_ ?_ ?_
    · intro j hj
      have hj0 : j = ⊥ := hj.eq_bot
      simpa only [hj0, stage_zero] using (show admissible seed from ⟨hgood, hsmall, hinj⟩)
    · intro j _ ih
      rw [stage_succ]
      exact (next_spec _ ih).2.1
    · intro j hj ih
      have heq : stage j = seed ∪ ⋃ k : Iio j, stage k.1 := by
        rw [stage_limit j hj]
        apply (union_eq_right.mpr ?_).symm
        obtain ⟨k, hk⟩ := not_isMin_iff.mp hj.not_isMin
        exact (seed_stage k).trans (subset_iUnion (fun k : Iio j => stage k.1) ⟨k, hk⟩)
      rw [heq]
      exact seed_chain_union good q seed (fun k : Iio j => stage k.1)
        ⟨hgood, hsmall, hinj⟩ ((mk_subtype_le _).trans hW)
        (fun k => ih k.1 k.2) (fun k => seed_stage k.1)
        (fun k l => (le_total k.1 l.1).imp (fun h => stage_mono h) (fun h => stage_mono h))
  let S : Set X := seed ∪ ⋃ i, stage i
  have hS : admissible S := seed_chain_union good q seed stage
    ⟨hgood, hsmall, hinj⟩ hW stage_admissible seed_stage
    (fun i j => (le_total i j).imp (fun h => stage_mono h) (fun h => stage_mono h))
  refine ⟨S, subset_union_left, hS.1, hS.2.1, hS.2.2, ?_⟩
  apply isCountablyCompact_iff_infinite_subset_has_accPt.mpr
  intro A hAS hA
  let e : ℕ ↪ A := hA.natEmbedding A
  have appearance (n : ℕ) : ∃ i, (e n).val ∈ stage i := by
    rcases hAS (e n).property with h | h
    · exact ⟨⊥, seed_stage ⊥ h⟩
    · exact mem_iUnion.mp h
  choose appearance_stage happear using appearance
  let ord (n : ℕ) : Ordinal := (appearance_stage n).toOrd.val
  have hord (n : ℕ) : ord n < Ordinal.omega 1 := (appearance_stage n).toOrd.property
  let b : W := Ordinal.ToType.mk ⟨⨆ n, ord n, Ordinal.iSup_lt_omega_one hord⟩
  have hab (n : ℕ) : appearance_stage n ≤ b := by
    apply Ordinal.ToType.mk.symm.le_iff_le.mp
    change (appearance_stage n).toOrd.val ≤ b.toOrd.val
    simpa only [b, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply] using Ordinal.le_iSup ord n
  let eb : ℕ ↪ stage b :=
    ⟨fun n => ⟨(e n).val, stage_mono (hab n) (happear n)⟩,
      fun n m h => e.injective (Subtype.ext (congrArg (fun z : stage b => z.val) h))⟩
  obtain ⟨x, hx, hacc⟩ := (next_spec (stage b) (stage_admissible b)).2.2 eb
  refine ⟨x, Or.inr (mem_iUnion.mpr ⟨Order.succ b, stage_succ b ▸ hx⟩), ?_⟩
  exact hacc.mono (Filter.principal_mono.mpr (by rintro _ ⟨n, rfl⟩; exact (e n).property))

end D5.S3.Topology.CountablyCompact.InjectiveSelectorClosure
