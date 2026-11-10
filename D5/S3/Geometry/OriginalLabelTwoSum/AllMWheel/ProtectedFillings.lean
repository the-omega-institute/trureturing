/- GID: D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/AllMWheel/ProtectedFillings
   mirror-E: none(waiver:all-m-protected-source-only)
   anchors: [mathlib/module/Mathlib.Order.UpperLower.CompleteLattice]
   utility: none
   digest: Actual maximal-critical protection, path Gamma and ghost-retaining zero fillings on the original wheel grounds. -/

import D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.CycleWord

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
local instance allMWheelProtectedPropDecidable : (p : Prop) → Decidable p := Classical.propDecidable
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
open FiniteProtectedDualWord OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem dual_mem (W : Finset V) (K : Family V) (s : Finset V) :
    s ∈ rawDual W K ↔ s ⊆ W ∧ W \ s ∉ K := by
  change s ∈ FiniteAlexanderDualCollapse.dualTable W
    (W.powerset.filter (fun T => T ∈ K)) ↔ _
  simp only [FiniteAlexanderDualCollapse.dualTable, Finset.mem_filter,
    Finset.mem_powerset, Finset.sdiff_subset, true_and]

private theorem word_owner {xs : List (Symbol V)}
    (hp : xs.Pairwise (fun a b => Disjoint a.faces b.faces))
    {a b : Symbol V} {s : Finset V} (ha : a ∈ xs) (hb : b ∈ xs)
    (hsa : s ∈ a.faces) (hsb : s ∈ b.faces) : a = b := by
  revert hp ha hb
  induction xs with
  | nil => intro hp ha hb; simp at ha
  | cons c xs ih =>
      intro hp ha hb
      obtain ⟨hc, ht⟩ := List.pairwise_cons.mp hp
      rcases List.mem_cons.mp ha with hac | ha
      · rcases List.mem_cons.mp hb with hbc | hb
        · exact hac.trans hbc.symm
        · have hd := hc _ hb
          rw [← hac] at hd
          exact (Finset.disjoint_left.mp hd hsa hsb).elim
      · rcases List.mem_cons.mp hb with hbc | hb
        · have hd := hc _ ha
          rw [← hbc] at hd
          exact (Finset.disjoint_left.mp hd hsb hsa).elim
        · exact ih ht ha hb

/- This is a constructor of the EXISTING P02 Contract, not another word or
   collapse authority. All four protection obligations are proved here. -/
private def maximalContract {W : Finset V} {K : Family V} (d : Word W K)
    (hm : ∀ S, Symbol.critical S ∈ d.word → ∀ U ∈ K, S ⊆ U → U = S)
    (hp : ∀ L v, Symbol.pair L v ∈ d.word → insert v L ⊂ W) : Contract W K where
  toWord := d
  «protected» := criticalFaces d.word
  protected_subset := by
    intro S hS
    exact d.critical_data S ((criticalFaces_mem _ S).mp hS)
  protected_upward := by
    intro S U hS hU hSU
    rw [hm S ((criticalFaces_mem _ S).mp hS) U hU hSU]
    exact hS
  protected_pair := by
    intro L v hpair
    have hn : ∀ T ∈ (Symbol.pair L v).faces, T ∉ criticalFaces d.word := by
      intro T hT hc
      have he := word_owner d.partition hpair ((criticalFaces_mem _ T).mp hc)
        hT (by simp [Symbol.faces])
      cases he
    exact ⟨fun h => (hn L (by simp [Symbol.faces]) h).elim,
      fun h => (hn (insert v L) (by simp [Symbol.faces]) h).elim⟩
  critical_protected := by
    intro S hS
    exact (criticalFaces_mem _ S).mpr hS
  emitted_proper := by intro L v h _; exact hp L v h

private theorem contract_endpoint {W : Finset V} {K : Family V} (d : Contract W K) :
    rawEndpoint W K d.protected d.protected_upward =
      endpoint (rawDual W K) (d.protected.image (fun T => W \ T)) := by
  apply SetLike.ext
  intro s
  change (s ⊆ W ∧ (W \ s ∉ K ∨ W \ s ∈ d.protected)) ↔
    s ∈ rawDual W K ∨ ∃ a ∈ d.protected.image (fun T => W \ T), s ⊆ a
  constructor
  · rintro ⟨hs, hn | hH⟩
    · exact Or.inl ((dual_mem W K s).mpr ⟨hs, hn⟩)
    · exact Or.inr ⟨W \ (W \ s), Finset.mem_image.mpr ⟨W \ s, hH, rfl⟩,
        by rw [Finset.sdiff_sdiff_eq_self hs]⟩
  · rintro (h | ⟨a, ha, hsa⟩)
    · obtain ⟨hs, hn⟩ := (dual_mem W K s).mp h
      exact ⟨hs, Or.inl hn⟩
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp ha
      have hs : s ⊆ W := hsa.trans Finset.sdiff_subset
      refine ⟨hs, ?_⟩
      by_cases hc : W \ s ∈ K
      · right
        apply d.protected_upward hT hc
        intro x hx
        have hxW := d.supported T (d.protected_subset T hT) hx
        exact Finset.mem_sdiff.mpr ⟨hxW, fun hxs =>
          (Finset.mem_sdiff.mp (hsa hxs)).2 hx⟩
      · exact Or.inl hc

private theorem maximal_cells {W : Finset V} {K : Family V}
    (C : Finset (Finset V)) (hs : ∀ T ∈ C, T ∈ K ∧ T ⊂ W)
    (hm : ∀ T ∈ C, ∀ U ∈ K, T ⊆ U → U = T) :
    CriticalData (rawDual W K) (C.image (fun T => W \ T)) := by
  constructor
  · intro s h
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp h
    rw [Finset.sdiff_nonempty]
    exact fun h => (hs T hT).2.ne (Finset.Subset.antisymm (hs T hT).2.subset h)
  · intro s h hd
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp h
    have hn := ((dual_mem W K _).mp hd).2
    rw [Finset.sdiff_sdiff_eq_self (hs T hT).2.subset] at hn
    exact hn (hs T hT).1
  · intro s h t hts
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp h
    have htW : t ⊆ W := hts.subset.trans Finset.sdiff_subset
    apply (dual_mem W K t).mpr
    refine ⟨htW, ?_⟩
    intro hc
    have hTc : T ⊆ W \ t := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨(hs T hT).2.subset hx,
        fun hxt => (Finset.mem_sdiff.mp (hts.subset hxt)).2 hx⟩
    have he := hm T hT (W \ t) hc hTc
    have he' := congrArg (fun q : Finset V => W \ q) he
    have : t = W \ T := by simpa only [Finset.sdiff_sdiff_eq_self htW] using he'
    exact hts.ne this
  · intro s hs' t ht' hst
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hs'
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp ht'
    have hTS : T ⊆ S := by
      intro x hx
      by_contra hxn
      have hc := hst (Finset.mem_sdiff.mpr ⟨(hs T hT).2.subset hx, hxn⟩)
      exact (Finset.mem_sdiff.mp hc).2 hx
    rw [hm T hT S (hs S hS).1 hTS]

/- Every selected middle vertex dominates its own consecutive triple.
   The proof retains the empty and two-vertex bases of the raw recurrence. -/
private theorem path_critical_dominates (vs : List V) (S : Finset V)
    (hS : S ∈ FiniteIndependentPathGreedy.pathCritical vs) :
    ∀ x ∈ vs, x ∈ S ∨ ∃ y ∈ S, {x, y} ∈ pathEdges vs := by
  induction vs using FiniteIndependentPathGreedy.pathCritical.induct generalizing S with
  | case1 => simp
  | case2 a => simp [FiniteIndependentPathGreedy.pathCritical] at hS
  | case3 a b =>
      have he : S = {b} := by simpa [FiniteIndependentPathGreedy.pathCritical] using hS
      subst S
      intro x hx
      rcases (show x = a ∨ x = b by simpa using hx) with rfl | rfl
      · exact Or.inr ⟨b, by simp, by simp [pathEdges]⟩
      · exact Or.inl (by simp)
  | case4 a b c vs ih =>
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
      intro x hx
      rcases (show x = a ∨ x = b ∨ x = c ∨ x ∈ vs by simpa using hx) with
        rfl | rfl | rfl | hx
      · exact Or.inr ⟨b, by simp, by simp [pathEdges]⟩
      · exact Or.inl (by simp)
      · exact Or.inr ⟨b, by simp, by simp [pathEdges, Finset.pair_comm]⟩
      · rcases ih T hT x hx with h | ⟨y, hy, he⟩
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · refine Or.inr ⟨y, Finset.mem_insert_of_mem hy, ?_⟩
          cases vs <;> simp_all [pathEdges]

private theorem path_critical_maximal (vs : List V) (hd : vs.Nodup)
    (S : Finset V) (hS : Symbol.critical S ∈ pathWord vs)
    (U : Finset V) (hU : U ∈ pathFamily vs) (hSU : S ⊆ U) : U = S := by
  have hSc : S ∈ FiniteIndependentPathGreedy.pathCritical vs := by
    rw [← pathWord_critical_eq_selected]
    exact (criticalFaces_mem _ S).mpr hS
  have hu := (mem_pathIndependentOn vs U).mp ((mem_pathFamily vs U).mp hU)
  apply Finset.Subset.antisymm _ hSU
  intro x hx
  rcases path_critical_dominates vs S hSc x (List.mem_toFinset.mp (hu.1 hx)) with
    h | ⟨y, hy, he⟩
  · exact h
  · exact (hu.2 {x, y} he (by simpa only [Finset.insert_subset_iff,
      Finset.singleton_subset_iff] using And.intro hx (hSU hy))).elim

private theorem rim_support (m : Nat) (hm : 3 ≤ m) : rim m hm ⊆ ground m := by
  intro x hx
  rcases (show x = firstLabel m hm ∨ x = secondLabel m hm by simpa [rim] using hx)
    with rfl | rfl <;> simp [ground, firstLabel, secondLabel]

private theorem tail_mem (m : Nat) (hm : 3 ≤ m) (x : Label m) :
    x ∈ tailGround m hm ↔ 3 ≤ x.val := by
  simp only [tailGround, ground, rim, Finset.mem_sdiff, Finset.mem_erase,
    Finset.mem_univ, and_true, Finset.mem_insert, Finset.mem_singleton,
    ne_eq, Fin.ext_iff, firstLabel, secondLabel, Fin.val_zero, Fin.val_mk]
  omega

private theorem interval_independent (m lo n : Nat) (h : lo + n ≤ m + 1)
    (s : Finset (Label m)) :
    s ∈ pathIndependentOn (labelInterval m lo n h) ↔
      (∀ x ∈ s, lo ≤ x.val ∧ x.val < lo + n) ∧
      (∀ x ∈ s, ∀ y ∈ s, y.val ≠ x.val + 1) := by
  rw [mem_pathIndependentOn]
  constructor
  · rintro ⟨hs, he⟩
    refine ⟨fun x hx => (mem_labelInterval _ _ _ _ x).mp
      (List.mem_toFinset.mp (hs hx)), ?_⟩
    intro x hx y hy heq
    have hxl := (mem_labelInterval _ _ _ _ x).mp (List.mem_toFinset.mp (hs hx))
    have hyl := (mem_labelInterval _ _ _ _ y).mp (List.mem_toFinset.mp (hs hy))
    exact he {x, y} ((labelInterval_edges _ _ _ _ _).mpr
      ⟨x, y, hxl.1, heq, hyl.2, rfl⟩) (Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩)
  · rintro ⟨hs, he⟩
    refine ⟨fun x hx => List.mem_toFinset.mpr
      ((mem_labelInterval _ _ _ _ x).mpr (hs x hx)), ?_⟩
    intro e he' hsub
    obtain ⟨x, y, _, hxy, _, rfl⟩ := (labelInterval_edges _ _ _ _ e).mp he'
    exact he x (hsub (by simp)) y (hsub (by simp)) hxy

private theorem root_independent (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :
    s ∈ pathFamily (pathRootPath m hm) ↔ s ⊆ ground m ∧
      (∀ x ∈ s, ∀ y ∈ s, 2 ≤ x.val → y.val ≠ x.val + 1) ∧
      (lastLabel m ∉ s ∨ firstLabel m hm ∉ s) := by
  rw [mem_pathFamily, mem_pathIndependentOn, pathRootPath_vertices]
  constructor
  · rintro ⟨hs, he⟩
    refine ⟨hs, ?_, ?_⟩
    · intro x hx y hy hx2 hxy
      exact he {x, y} ((pathRootPath_edges m hm _).mpr (Or.inl
        ⟨x, y, hx2, hxy, by have := y.isLt; omega, rfl⟩)) (Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩)
    · by_contra hn
      push_neg at hn
      exact he {lastLabel m, firstLabel m hm}
        ((pathRootPath_edges m hm _).mpr (Or.inr rfl)) (Finset.insert_subset_iff.mpr ⟨hn.1, Finset.singleton_subset_iff.mpr hn.2⟩)
  · rintro ⟨hs, he, hw⟩
    refine ⟨hs, ?_⟩
    intro e he' hsub
    rcases (pathRootPath_edges m hm e).mp he' with
      ⟨x, y, hx2, hxy, _, rfl⟩ | rfl
    · exact he x (hsub (by simp)) y (hsub (by simp)) hx2 hxy
    · exact hw.elim (fun h => h (hsub (by simp))) (fun h => h (hsub (by simp)))

private theorem root_dual (m : Nat) (hm : 3 ≤ m) :
    rawDual (ground m) (pathFamily (pathRootPath m hm)) = pathRoot m hm := by
  apply SetLike.ext
  intro s
  rw [dual_mem, mem_pathFamily, mem_pathIndependentOn, pathRootPath_vertices,
    pathRootPath_row_edges]
  constructor
  · rintro ⟨hs, hn⟩
    have hn' : ¬ ∀ e ∈ ((Finset.univ : Finset (Fin m)).erase
        (interfaceRow m hm)).image (rimEdge m (by omega)), ¬ e ⊆ ground m \ s := by
      intro h
      exact hn ⟨Finset.sdiff_subset, h⟩
    push_neg at hn'
    obtain ⟨e, he, hes⟩ := hn'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    refine ⟨⟨i, (Finset.mem_erase.mp hi).1⟩, ?_⟩
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hs hx, fun hxe => (Finset.mem_sdiff.mp (hes hxe)).2 hx⟩
  · rintro ⟨i, hi⟩
    refine ⟨hi.trans Finset.sdiff_subset, ?_⟩
    rintro ⟨_, he⟩
    apply he (rimEdge m (by omega) i.val)
      (Finset.mem_image.mpr ⟨i.val, Finset.mem_erase.mpr ⟨i.property, Finset.mem_univ _⟩, rfl⟩)
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨(rimRows m (by omega)).row_supported i.val hx,
      fun hxs => (Finset.mem_sdiff.mp (hi hxs)).2 hx⟩

private theorem adjoin_rim_independent (m : Nat) (hm : 3 ≤ m)
    (T : Finset (Label m)) (hT : T ⊆ tailGround m hm) :
    rim m hm ∪ T ∈ pathFamily (pathRootPath m hm) ↔
      T ∈ pathFamily (cyclePathTail m hm) := by
  rw [root_independent, mem_pathFamily, cyclePathTail, interval_independent]
  have ht : ∀ x ∈ T, 3 ≤ x.val := fun x hx => (tail_mem m hm x).mp (hT hx)
  have h1 : firstLabel m hm ∈ rim m hm ∪ T := by simp [rim]
  have h2 : secondLabel m hm ∈ rim m hm ∪ T := by simp [rim]
  constructor
  · rintro ⟨_, ha, hw⟩
    have hmT : lastLabel m ∉ T := fun h => hw.elim
      (fun hn => hn (Finset.mem_union_right _ h)) (fun hn => hn h1)
    refine ⟨?_, fun x hx y hy => ha x (Finset.mem_union_right _ hx) y
      (Finset.mem_union_right _ hy) (by have := ht x hx; omega)⟩
    intro x hx
    have hx3 : x.val ≠ 3 := by
      intro he
      exact ha (secondLabel m hm) h2 x (Finset.mem_union_right _ hx)
        (by simp [secondLabel]) (by simp [secondLabel, he])
    have hxm : x.val ≠ m := fun he => hmT ((show x = lastLabel m from Fin.ext he) ▸ hx)
    have hxl := ht x hx
    have hxu := x.isLt
    constructor <;> omega
  · rintro ⟨hb, ha⟩
    refine ⟨Finset.union_subset (rim_support m hm)
      (hT.trans Finset.sdiff_subset), ?_, Or.inl ?_⟩
    · intro x hx y hy hx2 hxy
      simp only [Finset.mem_union, rim, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with (rfl | rfl) | hx <;> rcases hy with (rfl | rfl) | hy
      all_goals first
        | exact ha _ hx _ hy hxy
        | (have hxb := hb _ hx; have hxv := x.isLt
           simp only [firstLabel, secondLabel] at *; omega)
        | (have hyb := hb _ hy; have hyv := y.isLt
           simp only [firstLabel, secondLabel] at *; omega)
        | (simp only [firstLabel, secondLabel] at *; omega)
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · simp only [rim, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
          lastLabel, firstLabel, secondLabel] at h
        omega
      · have hb' := hb (lastLabel m) h
        dsimp [lastLabel] at hb'
        omega

private theorem zero_dual (m : Nat) (hm : 3 ≤ m) :
    rawDual (tailGround m hm) (pathFamily (cyclePathTail m hm)) = A0 m hm := by
  apply SetLike.ext
  intro s
  rw [dual_mem]
  change _ ↔ s ∈ pathRoot m hm ∧ s ⊆ tailGround m hm
  rw [← root_dual m hm, dual_mem]
  constructor
  · rintro ⟨hs, hn⟩
    refine ⟨⟨hs.trans Finset.sdiff_subset, ?_⟩, hs⟩
    have hc : ground m \ s = rim m hm ∪ (tailGround m hm \ s) := by
      ext x
      have hr := rim_support m hm
      have hsr : x ∈ s → x ∉ rim m hm := fun hx => (Finset.mem_sdiff.mp (hs hx)).2
      simp only [tailGround, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨hw, hns⟩
        by_cases hx : x ∈ rim m hm
        · exact Or.inl hx
        · exact Or.inr ⟨⟨hw, hx⟩, hns⟩
      · rintro (hx | ⟨⟨hw, _⟩, hns⟩)
        · exact ⟨hr hx, fun hxs => hsr hxs hx⟩
        · exact ⟨hw, hns⟩
    rw [hc, adjoin_rim_independent m hm _ Finset.sdiff_subset]
    exact hn
  · rintro ⟨⟨_, hn⟩, hs⟩
    refine ⟨hs, ?_⟩
    intro hc
    apply hn
    have hri := (adjoin_rim_independent m hm (tailGround m hm \ s)
      Finset.sdiff_subset).mpr hc
    apply (pathFamily (pathRootPath m hm)).lower _ hri
    intro x hx
    by_cases hr : x ∈ rim m hm
    · exact Finset.mem_union_left _ hr
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, hr⟩,
          (Finset.mem_sdiff.mp hx).2⟩)

private theorem root_pair_proper (m : Nat) (hm : 3 ≤ m) (L : Finset (Label m))
    (v : Label m) (h : Symbol.pair L v ∈ (pathRootWordData m hm).word) :
    insert v L ⊂ ground m := by
  have hu := (pathRootWordData m hm).pair_data L v h
  have hU := (root_independent m hm _).mp hu.2.1
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hU.1, ?_⟩
  intro he
  have h2 : secondLabel m hm ∈ insert v L := by rw [he]; simp [ground, secondLabel]
  let z : Label m := ⟨3, by omega⟩
  have h3 : z ∈ insert v L := by rw [he]; simp [ground, z]
  exact hU.2.1 _ h2 z h3 (by simp [secondLabel]) (by simp [z, secondLabel])

private theorem transported_word {W X : Finset V} {K : Family V}
    (h : W = X) (d : Word W K) : (h ▸ d).word = d.word := by
  cases h
  rfl

private theorem root_word (m : Nat) (hm : 3 ≤ m) :
    (pathRootWordData m hm).word = pathWord (pathRootPath m hm) := by
  exact (transported_word (pathRootPath_vertices m hm)
    (pathWordData _ (pathRootPath_nodup m hm))).trans
      (pathWordData_word _ (pathRootPath_nodup m hm))

/-- Actual all-residue path H; every unexecuted raw critical is protected. -/
def pathContract (m : Nat) (hm : 3 ≤ m) :
    Contract (ground m) (pathFamily (pathRootPath m hm)) :=
  maximalContract (pathRootWordData m hm)
    (by
      intro S hS U hU hSU
      apply path_critical_maximal _ (pathRootPath_nodup m hm) S _ U hU hSU
      simpa only [root_word] using hS)
    (root_pair_proper m hm)

/-- Exact original path-row root, retaining the fixed ambient labels. -/
theorem pathRoot_rawDual (m : Nat) (hm : 3 ≤ m) :
    rawDual (ground m) (pathFamily (pathRootPath m hm)) = pathRoot m hm :=
  root_dual m hm

/-- P04's partial filling is also present in both obstructed classes.
    The cells are fixed-ground complements, never raw path criticals. -/
def pathFilling (m : Nat) (hm : 3 ≤ m) : Filling (ground m) (pathRoot m hm) := by
  let d := pathContract m hm
  have hd : rawDual (ground m) (pathFamily (pathRootPath m hm)) = pathRoot m hm :=
    root_dual m hm
  have hc := maximal_cells d.protected
    (by
      intro T hT
      have ht := d.protected_subset T hT
      refine ⟨ht, ?_⟩
      have hs := (root_independent m hm T).mp ht
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hs.1, ?_⟩
      intro he
      have h2 : secondLabel m hm ∈ T := by rw [he]; simp [ground, secondLabel]
      let z : Label m := ⟨3, by omega⟩
      have h3 : z ∈ T := by rw [he]; simp [ground, z]
      exact hs.2.1 _ h2 z h3 (by simp [secondLabel]) (by simp [z, secondLabel]))
    (by
      intro T hT U hU hTU
      apply path_critical_maximal _ (pathRootPath_nodup m hm) T _ U hU hTU
      have h := (criticalFaces_mem _ T).mp hT
      simpa only [d, pathContract, maximalContract, root_word] using h)
  refine {
    empty_mem := ?_
    collar := pathRoot m hm
    critical := d.protected.image (fun T => ground m \ T)
    contains := le_rfl
    supported := ((rimRows m (by omega)).without (interfaceRow m hm)).root_supported
    critical_supported := ?_
    cells := hd ▸ hc
    main := d.protectedDualWordSequence.cast rfl ?_
    separate := Sequence.refl _ }
  · rw [← hd, dual_mem]
    refine ⟨Finset.empty_subset _, ?_⟩
    intro h
    have hi := (root_independent m hm _).mp h
    simp only [Finset.sdiff_empty] at hi
    exact hi.2.1 (secondLabel m hm) (by simp [ground, secondLabel])
      (⟨3, by omega⟩ : Label m) (by simp [ground])
      (by simp [secondLabel]) (by simp [secondLabel])
  · intro s hs
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.sdiff_subset
  · change project (rawEndpoint _ _ _ _) = _
    rw [contract_endpoint d, hd]

/-- Genuine good-residue Gamma, with its no-critical premise derived from m.
    This is the sufficiency direction, not the Euler necessity theorem. -/
def gammaGood (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :
    Sequence (project (delta (ground m))) (project (pathRoot m hm)) := by
  have S := (pathRootWordData m hm).noCritical_unprotected
    (by simpa only [root_word] using pathRootPath_noCritical m hm hg)
    (root_pair_proper m hm)
  exact S.cast rfl (congrArg project (root_dual m hm))

/-- Actual zero-filling Contract on Z, with the forbidden endpoints retained
    as ghosts. At m=3 and 4 H contains the raw EMPTY critical face. -/
def zeroContract (m : Nat) (hm : 3 ≤ m) :
    Contract (tailGround m hm) (pathFamily (cyclePathTail m hm)) := by
  let p := cycleTailWordData m hm
  let d : Word (tailGround m hm) (pathFamily (cyclePathTail m hm)) := {
    word := p.word
    supported := by
      intro s hs x hx
      apply (tail_mem m hm x).mpr
      have ht := p.supported s hs hx
      exact le_trans (by omega) ((cyclePathTail_vertices m hm x).mp ht).1
    pair_data := p.pair_data
    critical_data := p.critical_data
    partition := p.partition
    covers := p.covers
    pair_dependency := p.pair_dependency
    critical_dependency := p.critical_dependency }
  exact maximalContract d
    (by
      intro S hS U hU hSU
      apply path_critical_maximal _ (cyclePathTail_nodup m hm) S _ U hU hSU
      simpa only [d, p, cycleTailWordData, pathWordData_word] using hS)
    (by
      intro L v h
      have hU := d.pair_data L v h
      have hs := d.supported _ hU.2.1
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, ?_⟩
      intro he
      let z : Label m := ⟨3, by omega⟩
      have hz : z ∈ insert v L := by rw [he]; exact (tail_mem m hm z).mpr (by rfl)
      have ht := p.supported _ hU.2.1 hz
      have hn := (cyclePathTail_vertices m hm z).mp ht
      dsimp [z] at hn
      omega)

/-- P05 for every m>=3: actual main list, identity standalone collar, and
    full proper boundaries/absence/antichain on the unchanged Z. -/
def fill0 (m : Nat) (hm : 3 ≤ m) : Filling (tailGround m hm) (A0 m hm) := by
  let d := zeroContract m hm
  have hd := zero_dual m hm
  have hp : ∀ T ∈ d.protected, T ⊂ tailGround m hm := by
    intro T hT
    have ht := d.protected_subset T hT
    have hs := d.supported T ht
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, ?_⟩
    intro he
    let z : Label m := ⟨3, by omega⟩
    have hz : z ∈ T := by rw [he]; exact (tail_mem m hm z).mpr (by rfl)
    have htail := (mem_pathIndependentOn _ T).mp ((mem_pathFamily _ T).mp ht)
    have hn := (cyclePathTail_vertices m hm z).mp (htail.1 hz)
    dsimp [z] at hn
    omega
  have hc := maximal_cells d.protected
    (by intro T hT; exact ⟨d.protected_subset T hT, hp T hT⟩)
    (by
      intro T hT U hU hTU
      apply path_critical_maximal _ (cyclePathTail_nodup m hm) T _ U hU hTU
      have h := (criticalFaces_mem _ T).mp hT
      simpa only [d, zeroContract, maximalContract, cycleTailWordData, pathWordData_word] using h)
  refine {
    empty_mem := ?_
    collar := A0 m hm
    critical := d.protected.image (fun T => tailGround m hm \ T)
    contains := le_rfl
    supported := by intro s hs; exact hs.2
    critical_supported := ?_
    cells := hd ▸ hc
    main := d.protectedDualWordSequence.cast rfl ?_
    separate := Sequence.refl _ }
  · rw [← hd, dual_mem]
    refine ⟨Finset.empty_subset _, ?_⟩
    intro h
    have ht := (mem_pathIndependentOn _ _).mp ((mem_pathFamily _ _).mp h)
    let z : Label m := ⟨3, by omega⟩
    have hz : z ∈ tailGround m hm := (tail_mem m hm z).mpr (by rfl)
    have hn := (cyclePathTail_vertices m hm z).mp
      (ht.1 (by simpa only [Finset.sdiff_empty] using hz))
    dsimp [z] at hn
    omega
  · intro s hs
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.sdiff_subset
  · change project (rawEndpoint _ _ _ _) = _
    rw [contract_endpoint d, hd]

/-- Exact zero critical tops, including singleton complements of empty tails. -/
theorem fill0_critical (m : Nat) (hm : 3 ≤ m) :
    (fill0 m hm).critical = if m % 3 = 2 then ∅ else {eta0 m hm} := by
  change (criticalFaces (tailWord m hm)).image (fun T => tailGround m hm \ T) = _
  rw [tailWord_critical_formula]
  split_ifs <;> simp [eta0]

/-- P01's dual on Z keeps both forbidden endpoint ghosts. -/
theorem A0_rawDual (m : Nat) (hm : 3 ≤ m) :
    rawDual (tailGround m hm) (pathFamily (cyclePathTail m hm)) = A0 m hm :=
  zero_dual m hm

private theorem interface_edge (m : Nat) (hm : 3 ≤ m) :
    rimEdge m (by omega) (interfaceRow m hm) = rim m hm := by
  simp only [rimEdge, interfaceRow, label, rimIndex,
    Nat.mod_eq_of_lt (by omega : 1 < m), rim, firstLabel, secondLabel]

/-- Literal original indexed wheel root, with the interface row restored. -/
theorem wheelRoot_eq_A1 (m : Nat) (hm : 3 ≤ m) :
    wheelRoot m (by omega) = A1 m hm := by
  apply SetLike.ext
  intro s
  change (∃ i : Fin m, s ⊆ ground m \ rimEdge m (by omega) i) ↔
    (∃ i : {i : Fin m // i ≠ interfaceRow m hm},
      s ⊆ ground m \ rimEdge m (by omega) i.val) ∨ s ⊆ tailGround m hm
  constructor
  · rintro ⟨i, hi⟩
    by_cases he : i = interfaceRow m hm
    · right
      simpa only [he, interface_edge, tailGround] using hi
    · exact Or.inl ⟨⟨i, he⟩, hi⟩
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.val, hi⟩
    · exact ⟨interfaceRow m hm, by simpa only [interface_edge, tailGround] using hi⟩

private theorem cycle_edge_linear (m : Nat) (hm : 3 ≤ m)
    (x y : Label m) (hx : 1 ≤ x.val) (hy : y.val = x.val + 1) :
    {x, y} ∈ cycleEdges m hm :=
  (cycleEdges_mem m hm _).mpr (Or.inl
    ⟨x, y, hx, hy, by have := y.isLt; omega, rfl⟩)

private theorem ground_positive (m : Nat) {x : Label m} (hx : x ∈ ground m) :
    1 ≤ x.val := by
  have hn : x ≠ 0 := (Finset.mem_erase.mp hx).1
  have hz : x = 0 ↔ x.val = 0 := Fin.ext_iff
  have hnval := (not_congr hz).mp hn
  omega

private theorem dominate_two (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (x : Label m) (hx : x ∈ ground m) :
    x ∈ labelsCongruent m 2 2 ∨
      ∃ y ∈ labelsCongruent m 2 2, {x, y} ∈ cycleEdges m hm := by
  have hxp := ground_positive m hx
  have hxm := x.isLt
  by_cases h2 : x.val % 3 = 2
  · left
    simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, h2⟩
  · by_cases h1 : x.val % 3 = 1
    · let y : Label m := ⟨x.val + 1, by omega⟩
      refine Or.inr ⟨y, ?_, cycle_edge_linear m hm x y hxp rfl⟩
      simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [y]
      constructor <;> omega
    · let y : Label m := ⟨x.val - 1, by omega⟩
      refine Or.inr ⟨y, ?_, ?_⟩
      · simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp [y]
        constructor <;> omega
      · rw [Finset.pair_comm]
        apply cycle_edge_linear m hm y x <;> dsimp [y] <;> omega

private theorem dominate_zero (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (x : Label m) (hx : x ∈ ground m) :
    x ∈ labelsCongruent m 0 3 ∨
      ∃ y ∈ labelsCongruent m 0 3, {x, y} ∈ cycleEdges m hm := by
  have hxp := ground_positive m hx
  have hxm := x.isLt
  by_cases h0x : x.val % 3 = 0
  · left
    simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, h0x⟩
  · by_cases h1 : x.val = 1
    · refine Or.inr ⟨lastLabel m, ?_, ?_⟩
      · simp [labelsCongruent, lastLabel, hm, h0]
      · have he : x = firstLabel m hm := Fin.ext h1
        rw [he, Finset.pair_comm]
        exact (cycleEdges_mem m hm _).mpr (Or.inr rfl)
    · by_cases h2 : x.val % 3 = 2
      · let y : Label m := ⟨x.val + 1, by omega⟩
        refine Or.inr ⟨y, ?_, cycle_edge_linear m hm x y hxp rfl⟩
        simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp [y]
        constructor <;> omega
      · let y : Label m := ⟨x.val - 1, by omega⟩
        refine Or.inr ⟨y, ?_, ?_⟩
        · simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp [y]
          constructor <;> omega
        · rw [Finset.pair_comm]
          apply cycle_edge_linear m hm y x <;> dsimp [y] <;> omega

private theorem dominate_last (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2)
    (x : Label m) (hx : x ∈ ground m) :
    x ∈ insert (lastLabel m) (labelsCongruent m 0 3) ∨
      ∃ y ∈ insert (lastLabel m) (labelsCongruent m 0 3), {x, y} ∈ cycleEdges m hm := by
  have hxp := ground_positive m hx
  have hxm := x.isLt
  by_cases hl : x.val = m
  · exact Or.inl (Finset.mem_insert.mpr (Or.inl (Fin.ext hl)))
  · by_cases h0x : x.val % 3 = 0
    · left
      apply Finset.mem_insert_of_mem
      simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by omega, h0x⟩
    · by_cases h1 : x.val = 1
      · refine Or.inr ⟨lastLabel m, by simp, ?_⟩
        have he : x = firstLabel m hm := Fin.ext h1
        rw [he, Finset.pair_comm]
        exact (cycleEdges_mem m hm _).mpr (Or.inr rfl)
      · by_cases h2x : x.val % 3 = 2
        · let y : Label m := ⟨x.val + 1, by omega⟩
          refine Or.inr ⟨y, Finset.mem_insert_of_mem ?_,
            cycle_edge_linear m hm x y hxp rfl⟩
          simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp [y]
          constructor <;> omega
        · let y : Label m := ⟨x.val - 1, by omega⟩
          refine Or.inr ⟨y, Finset.mem_insert_of_mem ?_, ?_⟩
          · simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
            dsimp [y]
            constructor <;> omega
          · rw [Finset.pair_comm]
            apply cycle_edge_linear m hm y x <;> dsimp [y] <;> omega

private theorem cycle_critical_maximal (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 1)
    (S : Finset (Label m)) (hS : Symbol.critical S ∈ cycleWord m hm)
    (U : Finset (Label m)) (hU : U ∈ facets (cycleIndependentOn m hm))
    (hSU : S ⊆ U) : U = S := by
  have hc := (criticalFaces_mem _ S).mpr hS
  rw [cycleWord_critical_formula] at hc
  have hu := (mem_cycleIndependentOn m hm U).mp ((mem_cycleFamily m hm U).mp hU)
  have hd : ∀ x ∈ ground m, x ∈ S ∨ ∃ y ∈ S, {x, y} ∈ cycleEdges m hm := by
    by_cases h0 : m % 3 = 0
    · simp only [if_pos h0, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact dominate_two m hm h0
      · exact dominate_zero m hm h0
    · have h2 : m % 3 = 2 := by omega
      have he : S = insert (lastLabel m) (labelsCongruent m 0 3) := by
        simpa only [if_neg h0, if_neg hr, Finset.mem_singleton] using hc
      subst S
      exact dominate_last m hm h2
  apply Finset.Subset.antisymm _ hSU
  intro x hx
  rcases hd x (hu.1 hx) with h | ⟨y, hy, he⟩
  · exact h
  · exact (hu.2 {x, y} he (Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr (hSU hy)⟩)).elim

private theorem cycle_face_proper (m : Nat) (hm : 3 ≤ m)
    (U : Finset (Label m)) (hU : U ∈ facets (cycleIndependentOn m hm)) :
    U ⊂ ground m := by
  have hu := (mem_cycleIndependentOn m hm U).mp ((mem_cycleFamily m hm U).mp hU)
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hu.1, ?_⟩
  intro he
  let x := firstLabel m hm
  let y := secondLabel m hm
  apply hu.2 {x, y} (cycle_edge_linear m hm x y (by simp [x, firstLabel])
    (by simp [x, y, firstLabel, secondLabel]))
  rw [he]
  exact Finset.insert_subset_iff.mpr ⟨by simp [x, ground, firstLabel],
    Finset.singleton_subset_iff.mpr (by simp [y, ground, secondLabel])⟩

/-- Both excluded residues use actual maximal critical protection; no good
    residue is incorrectly fed to this constructor. -/
def excludedCycleContract (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 1) :
    Contract (ground m) (facets (cycleIndependentOn m hm)) :=
  maximalContract (cycleWordData m hm) (by
    intro S hS U hU hSU
    exact cycle_critical_maximal m hm hr S hS U hU hSU)
    (by intro L v h; exact cycle_face_proper m hm _ ((cycleWordData m hm).pair_data L v h).2.1)

/-- Genuine P06 filling in residues zero and two, with collar exactly A1,
    all proper critical boundaries, and the separate identity list. -/
def fill1Excluded (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 1) :
    Filling (ground m) (A1 m hm) := by
  let d := excludedCycleContract m hm hr
  have hd : rawDual (ground m) (facets (cycleIndependentOn m hm)) = A1 m hm :=
    (cycleWord_rawDual_eq_wheelRoot m hm).trans (wheelRoot_eq_A1 m hm)
  have hc := maximal_cells d.protected
    (by intro T hT; exact ⟨d.protected_subset T hT,
      cycle_face_proper m hm T (d.protected_subset T hT)⟩)
    (by intro T hT U hU hTU
        exact cycle_critical_maximal m hm hr T ((criticalFaces_mem _ T).mp hT) U hU hTU)
  refine {
    empty_mem := ?_
    collar := A1 m hm
    critical := d.protected.image (fun T => ground m \ T)
    contains := le_rfl
    supported := by intro s hs; rw [← wheelRoot_eq_A1 m hm] at hs
                    exact (rimRows m (by omega)).root_supported s hs
    critical_supported := ?_
    cells := hd ▸ hc
    main := d.protectedDualWordSequence.cast rfl ?_
    separate := Sequence.refl _ }
  · rw [← hd, dual_mem]
    refine ⟨Finset.empty_subset _, ?_⟩
    intro h
    have hp := cycle_face_proper m hm _ h
    simp only [Finset.sdiff_empty] at hp
    exact hp.ne rfl
  · intro s hs
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.sdiff_subset
  · change project (rawEndpoint _ _ _ _) = _
    rw [contract_endpoint d, hd]

/-- The exact two/one critical tops use fixed-ground cycle complements. -/
theorem fill1Excluded_critical (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 1) :
    (fill1Excluded m hm hr).critical = cycleCritical m hm := by
  exact (cycleCritical_eq_complements m hm).symm


end D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
