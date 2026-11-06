/- GID: D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected
   generality: G
   digest: Actual maximal-critical protection, path Gamma and ghost-retaining
           zero fillings on the original wheel grounds.
   SOURCE_ONLY_UNCOMPILED: no elaboration or acceptance receipt. -/
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

/- A pivot changes from the earlier residue lo+1 to the later residue lo.
   This finite set is only arithmetic notation used in the EXISTING Word. -/
private def switchBase (m lo k j : Nat) : Finset (Label m) :=
  Finset.univ.filter (fun x =>
    (lo + 1 ≤ x.val ∧ x.val < lo + 3*j ∧ x.val % 3 = (lo + 1) % 3) ∨
    (lo + 3*j + 3 ≤ x.val ∧ x.val < lo + 3*k - 2 ∧ x.val % 3 = lo % 3))

private theorem switch_pair (m lo k j : Nat) (hk : 1 ≤ k) (hj : j < k)
    (h : lo + (3*k - 2) ≤ m + 1) :
    Symbol.pair (switchBase m lo k j) (⟨lo + 3*j, by omega⟩ : Label m) ∈
      pathWord (labelInterval m lo (3*k - 2) h) := by
  induction j generalizing lo k with
  | zero =>
      by_cases h1 : k = 1
      · subst k
        have he : switchBase m lo 1 0 = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have hh := (Finset.mem_filter.mp hx).2
          rcases hh with ⟨hl, hu, _⟩ | ⟨hl, hu, _⟩ <;> omega
        simpa [labelInterval, he] using
          (show Symbol.pair ∅ (⟨lo, by omega⟩ : Label m) ∈
            pathWord [⟨lo, by omega⟩] by simp)
      · have hn : 3*k - 2 = (3*k - 4) + 2 := by omega
        simp only [hn]
        change _ ∈ pathWord (⟨lo, by omega⟩ :: ⟨lo+1, by omega⟩ ::
          labelInterval m (lo+2) (3*k-4) (by omega))
        rw [pathWord_cons_cons]
        apply List.mem_append.mpr
        left
        apply List.mem_map.mpr
        refine ⟨switchBase m lo k 0, (mem_orderedFaces _ _).mpr ?_, ?_⟩
        · apply (interval_independent _ _ _ _ _).mpr
          constructor
          · intro x hx
            simp only [switchBase, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            constructor <;> omega
          · intro x hx y hy hxy
            simp only [switchBase, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
            omega
        · simp
  | succ j ih =>
      have hk' : 1 ≤ k-1 := by omega
      have hj' : j < k-1 := by omega
      have hn : 3*k-2 = (3*(k-1)-2)+3 := by omega
      have hb : switchBase m lo k (j+1) =
          insert (⟨lo+1, by omega⟩ : Label m) (switchBase m (lo+3) (k-1) j) := by
        ext x
        simp only [switchBase, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Fin.ext_iff]
        omega
      have hp : (⟨lo+3*(j+1), by omega⟩ : Label m) =
          (⟨(lo+3)+3*j, by omega⟩ : Label m) := by
        apply Fin.ext
        change lo + 3 * (j + 1) = (lo + 3) + 3 * j
        omega
      simp only [hn]
      change _ ∈ pathWord (⟨lo, by omega⟩ :: ⟨lo+1, by omega⟩ ::
        ⟨lo+2, by omega⟩ :: labelInterval m (lo+3) (3*(k-1)-2) (by omega))
      rw [pathWord_cons_cons]
      apply List.mem_append.mpr
      right
      apply List.mem_map.mpr
      exact ⟨Symbol.pair (switchBase m (lo+3) (k-1) j) (⟨(lo+3)+3*j, by omega⟩ : Label m),
        ih (lo+3) (k-1) hk' hj' (by omega), by simp only [List.tail_cons,
          adjoinSymbol_pair, hb, hp]⟩

/-- P07 a_j, indexed here from zero; j=0 corresponds to the ordinary j=1. -/
def collarA (m : Nat) (j : Fin (m/3)) : Finset (Label m) :=
  insert (lastLabel m) (switchBase m 2 (m/3) j.val)
def collarPivot (m : Nat) (j : Fin (m/3)) : Label m :=
  ⟨3*j.val+2, by have := j.isLt; omega⟩
def collarB (m : Nat) (j : Fin (m/3)) : Finset (Label m) :=
  insert (collarPivot m j) (collarA m j)
def collarUpper (m : Nat) (j : Fin (m/3)) : Finset (Label m) := ground m \ collarA m j
def collarLower (m : Nat) (j : Fin (m/3)) : Finset (Label m) := ground m \ collarB m j

private theorem good_width (m : Nat) (h1 : m % 3 = 1) : m = 3*(m/3)+1 := by omega
private theorem good_k (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) : 0 < m/3 := by omega

private theorem collarA_mem (m : Nat) (h1 : m % 3 = 1) (j : Fin (m/3)) (x : Label m) :
    x ∈ collarA m j ↔ x.val = m ∨
      (3 ≤ x.val ∧ x.val ≤ 3*j.val ∧ x.val % 3 = 0) ∨
      (3*j.val+5 ≤ x.val ∧ x.val < m ∧ x.val % 3 = 2) := by
  simp only [collarA, switchBase, Finset.mem_insert, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.ext_iff, lastLabel]
  have hmk := good_width m h1
  omega

private theorem collar_pair_in_word (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) : Symbol.pair (collarA m j) (collarPivot m j) ∈ cycleWord m hm := by
  have he : m-3 = 3*(m/3)-2 := by omega
  have hp := switch_pair m 2 (m/3) j.val (by have := good_k m hm h1; omega)
    j.isLt (by omega)
  have ht : Symbol.pair (switchBase m 2 (m/3) j.val) (collarPivot m j) ∈
      pathWord (cyclePathLast m hm) := by
    simpa only [cyclePathLast, he, collarPivot, Nat.add_comm 2 (3*j.val)] using hp
  rw [cycleWord_eq]
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨_, ht, rfl⟩

private theorem collar_pair_data (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) :
    collarA m j ∈ facets (cycleIndependentOn m hm) ∧
      collarB m j ∈ facets (cycleIndependentOn m hm) ∧ collarPivot m j ∉ collarA m j :=
  (cycleWordData m hm).pair_data _ _ (collar_pair_in_word m hm h1 j)

private theorem good_critical (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    Symbol.critical (labelsCongruent m 2 2) ∈ cycleWord m hm := by
  apply (criticalFaces_mem _ _).mp
  rw [cycleWord_critical_formula, if_neg (by omega : m % 3 ≠ 0), if_pos h1]
  simp

private theorem cycle_no_adj (m : Nat) (hm : 3 ≤ m) {U : Finset (Label m)}
    (hU : U ∈ facets (cycleIndependentOn m hm)) {x y : Label m}
    (hx : x ∈ U) (hy : y ∈ U) (he : {x, y} ∈ cycleEdges m hm) : False := by
  have h := (mem_cycleIndependentOn m hm U).mp ((mem_cycleFamily m hm U).mp hU)
  exact h.2 {x, y} he (Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩)

/- Only the two adjacent holes 3j+2,3j+3 can extend a_j. This is the
   domination calculation, not an assumption about the wanted endpoint. -/
private theorem collar_holes (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) (x : Label m) (hx : x ∈ ground m)
    (ha : x ∉ collarA m j) (hp : x.val ≠ 3*j.val+2) (hq : x.val ≠ 3*j.val+3) :
    ∃ y ∈ collarA m j, {x, y} ∈ cycleEdges m hm := by
  have hxp := ground_positive m hx
  have hxm := x.isLt
  have hj := j.isLt
  have hmk := good_width m h1
  have hn := not_congr (collarA_mem m h1 j x)
  have hna := hn.mp ha
  by_cases hx1 : x.val = 1
  · refine ⟨lastLabel m, by simp [collarA], ?_⟩
    have he : x = firstLabel m hm := Fin.ext hx1
    rw [he, Finset.pair_comm]
    exact (cycleEdges_mem m hm _).mpr (Or.inr rfl)
  · by_cases hxm1 : x.val+1 = m
    · exact ⟨lastLabel m, by simp [collarA],
        cycle_edge_linear m hm x (lastLabel m) hxp (by simpa [lastLabel] using hxm1.symm)⟩
    · by_cases hleft : x.val < 3*j.val+2
      · by_cases hr1 : x.val % 3 = 1
        · let y : Label m := ⟨x.val-1, by omega⟩
          refine ⟨y, (collarA_mem m h1 j y).mpr (Or.inr (Or.inl ?_)), ?_⟩
          · dsimp [y]; exact ⟨by omega, by omega, by omega⟩
          · rw [Finset.pair_comm]
            apply cycle_edge_linear m hm y x <;> dsimp [y] <;> omega
        · let y : Label m := ⟨x.val+1, by omega⟩
          refine ⟨y, (collarA_mem m h1 j y).mpr (Or.inr (Or.inl ?_)),
            cycle_edge_linear m hm x y hxp rfl⟩
          dsimp [y]
          exact ⟨by omega, by omega, by omega⟩
      · by_cases hr0 : x.val % 3 = 0
        · let y : Label m := ⟨x.val-1, by omega⟩
          refine ⟨y, (collarA_mem m h1 j y).mpr (Or.inr (Or.inr ?_)), ?_⟩
          · dsimp [y]; exact ⟨by omega, by omega, by omega⟩
          · rw [Finset.pair_comm]
            apply cycle_edge_linear m hm y x <;> dsimp [y] <;> omega
        · let y : Label m := ⟨x.val+1, by omega⟩
          refine ⟨y, (collarA_mem m h1 j y).mpr (Or.inr (Or.inr ?_)),
            cycle_edge_linear m hm x y hxp rfl⟩
          dsimp [y]
          exact ⟨by omega, by omega, by omega⟩

private theorem collar_next (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) (hj : j.val+1 < m/3) :
    collarB m ⟨j.val+1, hj⟩ =
      insert (⟨3*j.val+3, by have := j.isLt; omega⟩ : Label m) (collarA m j) := by
  ext x
  simp only [collarB, Finset.mem_insert, Fin.ext_iff, collarPivot,
    collarA_mem m h1]
  have hx := x.isLt
  have hmk := good_width m h1
  omega

private theorem collar_supersets (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) (U : Finset (Label m))
    (hU : U ∈ facets (cycleIndependentOn m hm)) (haU : collarA m j ⊆ U) :
    U = collarA m j ∨ U = collarB m j ∨
      ∃ hj : j.val+1 < m/3, U = collarB m ⟨j.val+1, hj⟩ := by
  let p := collarPivot m j
  let q : Label m := ⟨3*j.val+3, by have := j.isLt; omega⟩
  have hu := (mem_cycleIndependentOn m hm U).mp ((mem_cycleFamily m hm U).mp hU)
  have holes : ∀ x ∈ U, x ∈ collarA m j ∨ x = p ∨ x = q := by
    intro x hx
    by_cases ha : x ∈ collarA m j
    · exact Or.inl ha
    · by_cases hp : x = p
      · exact Or.inr (Or.inl hp)
      · by_cases hq : x = q
        · exact Or.inr (Or.inr hq)
        · obtain ⟨y, hy, he⟩ := collar_holes m hm h1 j x (hu.1 hx) ha
            (by intro hv; exact hp (Fin.ext hv)) (by intro hv; exact hq (Fin.ext hv))
          exact (cycle_no_adj m hm hU hx (haU hy) he).elim
  have hadj : ¬ (p ∈ U ∧ q ∈ U) := by
    rintro ⟨hp, hq⟩
    exact cycle_no_adj m hm hU hp hq (cycle_edge_linear m hm p q
      (by dsimp [p, collarPivot]; omega) (by dsimp [p, q, collarPivot] <;> omega))
  by_cases hp : p ∈ U
  · right; left
    apply Finset.Subset.antisymm
    · intro x hx
      rcases holes x hx with ha | rfl | rfl
      · exact Finset.mem_insert_of_mem ha
      · exact Finset.mem_insert_self _ _
      · exact (hadj ⟨hp, hx⟩).elim
    · exact Finset.insert_subset hp haU
  · by_cases hq : q ∈ U
    · right; right
      have hj : j.val+1 < m/3 := by
        by_contra hn
        have hlast : (lastLabel m).val = q.val+1 := by
          dsimp [q, lastLabel]; have := j.isLt; have := good_width m h1; omega
        exact cycle_no_adj m hm hU hq (haU (by simp [collarA]))
          (cycle_edge_linear m hm q (lastLabel m) (by dsimp [q]; omega) hlast)
      refine ⟨hj, ?_⟩
      rw [collar_next m hm h1 j hj]
      apply Finset.Subset.antisymm
      · intro x hx
        rcases holes x hx with ha | rfl | rfl
        · exact Finset.mem_insert_of_mem ha
        · exact (hp hx).elim
        · exact Finset.mem_insert_self _ _
      · exact Finset.insert_subset hq haU
    · left
      apply Finset.Subset.antisymm _ haU
      intro x hx
      rcases holes x hx with ha | rfl | rfl
      · exact ha
      · exact (hp hx).elim
      · exact (hq hx).elim

private theorem critical_supersets (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (U : Finset (Label m)) (hU : U ∈ facets (cycleIndependentOn m hm))
    (hSU : labelsCongruent m 2 2 ⊆ U) :
    U = labelsCongruent m 2 2 ∨ U = collarB m ⟨0, good_k m hm h1⟩ := by
  have hu := (mem_cycleIndependentOn m hm U).mp ((mem_cycleFamily m hm U).mp hU)
  have holes : ∀ x ∈ U, x ∈ labelsCongruent m 2 2 ∨ x = lastLabel m := by
    intro x hx
    have hxp := ground_positive m (hu.1 hx)
    have hxm := x.isLt
    by_cases hl : x.val = m
    · exact Or.inr (Fin.ext hl)
    · by_cases h2 : x.val % 3 = 2
      · left
        simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by omega, h2⟩
      · by_cases h0 : x.val % 3 = 0
        · let y : Label m := ⟨x.val-1, by omega⟩
          have hy : y ∈ labelsCongruent m 2 2 := by
            simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
            dsimp [y]; exact ⟨by omega, by omega⟩
          exact (cycle_no_adj m hm hU (hSU hy) hx
            (cycle_edge_linear m hm y x (by dsimp [y]; omega) (by dsimp [y]; omega))).elim
        · let y : Label m := ⟨x.val+1, by omega⟩
          have hy : y ∈ labelsCongruent m 2 2 := by
            simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
            dsimp [y]; exact ⟨by omega, by omega⟩
          exact (cycle_no_adj m hm hU hx (hSU hy) (cycle_edge_linear m hm x y hxp rfl)).elim
  have hb0 : collarB m ⟨0, good_k m hm h1⟩ =
      insert (lastLabel m) (labelsCongruent m 2 2) := by
    ext x
    simp only [collarB, Finset.mem_insert, collarA_mem m h1, Fin.ext_iff,
      collarPivot, labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and, lastLabel]
    have hx := x.isLt
    omega
  by_cases hl : lastLabel m ∈ U
  · right
    rw [hb0]
    exact Finset.Subset.antisymm
      (fun x hx => (holes x hx).elim (fun h => Finset.mem_insert_of_mem h)
        (fun h => Finset.mem_insert.mpr (Or.inl h))) (Finset.insert_subset hl hSU)
  · left
    exact Finset.Subset.antisymm (fun x hx => (holes x hx).resolve_right (fun h => hl (h ▸ hx))) hSU

/-- The actual P07 protection is the sole critical AND its actual whole pairs. -/
def goodH (m : Nat) : Finset (Finset (Label m)) :=
  insert (labelsCongruent m 2 2)
    ((Finset.univ : Finset (Fin (m/3))).biUnion (fun j => {collarA m j, collarB m j}))

private theorem mem_goodH (m : Nat) (T : Finset (Label m)) :
    T ∈ goodH m ↔ T = labelsCongruent m 2 2 ∨
      ∃ j : Fin (m/3), T = collarA m j ∨ T = collarB m j := by
  simp only [goodH, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]

/-- Full good-class Contract: upward, whole-symbol and all-critical coverage
    are established from the actual canonical word, not passed in. -/
def goodCycleContract (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    Contract (ground m) (facets (cycleIndependentOn m hm)) where
  toWord := cycleWordData m hm
  «protected» := goodH m
  protected_subset := by
    intro T hT
    rcases (mem_goodH m T).mp hT with rfl | ⟨j, rfl | rfl⟩
    · exact (cycleWordData m hm).critical_data _ (good_critical m hm h1)
    · exact (collar_pair_data m hm h1 j).1
    · exact (collar_pair_data m hm h1 j).2.1
  protected_upward := by
    intro T U hT hU hTU
    apply (mem_goodH m U).mpr
    rcases (mem_goodH m T).mp hT with rfl | ⟨j, rfl | rfl⟩
    · rcases critical_supersets m hm h1 U hU hTU with he | he
      · exact Or.inl he
      · exact Or.inr ⟨⟨0, good_k m hm h1⟩, Or.inr he⟩
    all_goals
      have haU : collarA m j ⊆ U := by
        first | exact hTU | exact (Finset.subset_insert _ _).trans hTU
      rcases collar_supersets m hm h1 j U hU haU with he | he | ⟨hj, he⟩
      · exact Or.inr ⟨j, Or.inl he⟩
      · exact Or.inr ⟨j, Or.inr he⟩
      · exact Or.inr ⟨⟨j.val+1, hj⟩, Or.inr he⟩
  protected_pair := by
    intro L v hp
    have whole : ∀ T ∈ (Symbol.pair L v).faces, T ∈ goodH m →
        ∀ U ∈ (Symbol.pair L v).faces, U ∈ goodH m := by
      intro T hT hH U hU
      rcases (mem_goodH m T).mp hH with he | ⟨j, he | he⟩
      · have ho := word_owner (cycleWordData m hm).partition hp (good_critical m hm h1)
          hT (by simpa only [he, Symbol.faces, Finset.mem_singleton])
        cases ho
      all_goals
        have ht : T ∈ (Symbol.pair (collarA m j) (collarPivot m j)).faces := by
          simp [Symbol.faces, he, collarB]
        have ho := word_owner (cycleWordData m hm).partition hp
          (collar_pair_in_word m hm h1 j) hT ht
        rw [ho] at hU
        rcases (show U = collarA m j ∨ U = collarB m j by
          simpa only [Symbol.faces, Finset.mem_insert, Finset.mem_singleton, collarB] using hU)
          with he | he
        · exact (mem_goodH m U).mpr (Or.inr ⟨j, Or.inl he⟩)
        · exact (mem_goodH m U).mpr (Or.inr ⟨j, Or.inr he⟩)
    exact ⟨fun h => whole L (by simp [Symbol.faces]) h _ (by simp [Symbol.faces]),
      fun h => whole (insert v L) (by simp [Symbol.faces]) h _ (by simp [Symbol.faces])⟩
  critical_protected := by
    intro S hS
    have hc := (criticalFaces_mem _ S).mpr hS
    rw [cycleWordData_word, cycleWord_critical_formula, if_neg (by omega : m % 3 ≠ 0), if_pos h1] at hc
    exact (mem_goodH m S).mpr (Or.inl (Finset.mem_singleton.mp hc))
  emitted_proper := by
    intro L v hp _
    exact cycle_face_proper m hm _ ((cycleWordData m hm).pair_data L v hp).2.1

/-- Standalone B1, without the retained eta1 simplex. -/
def collarCore (m : Nat) (hm : 3 ≤ m) : Family (Label m) :=
  A1 m hm ⊔ facets ((Finset.univ : Finset (Fin (m/3))).image (collarUpper m))

private theorem good_dual (m : Nat) (hm : 3 ≤ m) :
    rawDual (ground m) (facets (cycleIndependentOn m hm)) = A1 m hm :=
  (cycleWord_rawDual_eq_wheelRoot m hm).trans (wheelRoot_eq_A1 m hm)

private theorem good_endpoint (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    rawEndpoint (ground m) (facets (cycleIndependentOn m hm))
      (goodCycleContract m hm h1).protected (goodCycleContract m hm h1).protected_upward =
        endpoint (collarCore m hm) {eta1 m hm} := by
  rw [contract_endpoint, good_dual]
  apply SetLike.ext
  intro s
  change (s ∈ A1 m hm ∨ ∃ t ∈ (goodH m).image (fun T => ground m \ T), s ⊆ t) ↔
    (s ∈ A1 m hm ∨ ∃ t ∈ (Finset.univ : Finset (Fin (m/3))).image (collarUpper m), s ⊆ t) ∨
      ∃ t ∈ ({eta1 m hm} : Finset (Finset (Label m))), s ⊆ t
  constructor
  · rintro (h | ⟨t, ht, hst⟩)
    · exact Or.inl (Or.inl h)
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp ht
      rcases (mem_goodH m T).mp hT with rfl | ⟨j, rfl | rfl⟩
      · exact Or.inr ⟨eta1 m hm, by simp, hst⟩
      · exact Or.inl (Or.inr ⟨collarUpper m j, Finset.mem_image.mpr
          ⟨j, Finset.mem_univ _, rfl⟩, hst⟩)
      · exact Or.inl (Or.inr ⟨collarUpper m j, Finset.mem_image.mpr
          ⟨j, Finset.mem_univ _, rfl⟩, hst.trans
            (Finset.sdiff_subset_sdiff_right _ (Finset.subset_insert _ _))⟩)
  · rintro ((h | ⟨t, ht, hst⟩) | ⟨t, ht, hst⟩)
    · exact Or.inl h
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
      exact Or.inr ⟨collarUpper m j, Finset.mem_image.mpr
        ⟨collarA m j, (mem_goodH m _).mpr (Or.inr ⟨j, Or.inl rfl⟩), rfl⟩, hst⟩
    · have he : t = eta1 m hm := Finset.mem_singleton.mp ht
      subst t
      exact Or.inr ⟨eta1 m hm, Finset.mem_image.mpr
        ⟨labelsCongruent m 2 2, (mem_goodH m _).mpr (Or.inl rfl), rfl⟩, hst⟩

private theorem eta_good_cells (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    CriticalData (collarCore m hm) {eta1 m hm} := by
  have hS := (cycleWordData m hm).critical_data _ (good_critical m hm h1)
  have hSW := (cycleWordData m hm).supported _ hS
  have hmS : lastLabel m ∉ labelsCongruent m 2 2 := by
    simp [labelsCongruent, lastLabel, h1]
  have hmEta : lastLabel m ∈ eta1 m hm := by
    exact Finset.mem_sdiff.mpr ⟨by simp [ground, lastLabel, ne_eq, Fin.ext_iff] <;> omega, hmS⟩
  have hEtaAbsent : eta1 m hm ∉ A1 m hm := by
    rw [← good_dual m hm, dual_mem]
    rintro ⟨_, hn⟩
    exact hn (by simpa only [eta1, Finset.sdiff_sdiff_eq_self hSW] using hS)
  have hAbs : eta1 m hm ∉ collarCore m hm := by
    rintro (h | ⟨t, ht, he⟩)
    · exact hEtaAbsent h
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
      exact (Finset.mem_sdiff.mp (he hmEta)).2 (by simp [collarA])
  constructor
  · intro s hs
    have he := Finset.mem_singleton.mp hs
    subst s
    exact ⟨lastLabel m, hmEta⟩
  · intro s hs
    have he := Finset.mem_singleton.mp hs
    subst s
    exact hAbs
  · intro s hs t hts
    have he := Finset.mem_singleton.mp hs
    subst s
    by_cases ht : t ∈ A1 m hm
    · exact Or.inl ht
    · have htW : t ⊆ ground m := hts.subset.trans Finset.sdiff_subset
      have hU : ground m \ t ∈ facets (cycleIndependentOn m hm) := by
        by_contra hn
        exact ht (by rw [← good_dual m hm, dual_mem]; exact ⟨htW, hn⟩)
      have hSU : labelsCongruent m 2 2 ⊆ ground m \ t := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨hSW hx, fun hxt =>
          (Finset.mem_sdiff.mp (hts.subset hxt)).2 hx⟩
      rcases critical_supersets m hm h1 _ hU hSU with hEq | hEq
      · have he' := congrArg (fun q : Finset (Label m) => ground m \ q) hEq
        have hte : t = eta1 m hm := by
          simpa only [Finset.sdiff_sdiff_eq_self htW, eta1] using he'
        exact (hts.ne hte).elim
      · have he' := congrArg (fun q : Finset (Label m) => ground m \ q) hEq
        have hte : t = collarLower m ⟨0, good_k m hm h1⟩ := by
          simpa only [Finset.sdiff_sdiff_eq_self htW, collarLower] using he'
        right
        refine ⟨collarUpper m ⟨0, good_k m hm h1⟩,
          Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
        rw [hte]
        exact Finset.sdiff_subset_sdiff_right _ (Finset.subset_insert _ _)
  · intro s hs t ht _
    exact (Finset.mem_singleton.mp hs).trans (Finset.mem_singleton.mp ht).symm

private def collarRest (m j : Nat) : Finset (Finset (Label m)) :=
  ((Finset.univ : Finset (Fin (m/3))).filter (fun i => j ≤ i.val)).biUnion
    (fun i => {collarA m i, collarB m i})

private theorem mem_collarRest (m j : Nat) (T : Finset (Label m)) :
    T ∈ collarRest m j ↔ ∃ i : Fin (m/3), j ≤ i.val ∧ (T = collarA m i ∨ T = collarB m i) := by
  simp only [collarRest, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]

private theorem collarRest_up (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) (j : Nat) :
    ∀ {T U}, T ∈ collarRest m j → U ∈ facets (cycleIndependentOn m hm) →
      T ⊆ U → U ∈ collarRest m j := by
  intro T U hT hU hTU
  obtain ⟨i, hi, he⟩ := (mem_collarRest m j T).mp hT
  have haU : collarA m i ⊆ U := by
    rcases he with rfl | rfl
    · exact hTU
    · exact (Finset.subset_insert _ _).trans hTU
  apply (mem_collarRest m j U).mpr
  rcases collar_supersets m hm h1 i U hU haU with he | he | ⟨hn, he⟩
  · exact ⟨i, hi, Or.inl he⟩
  · exact ⟨i, hi, Or.inr he⟩
  · exact ⟨⟨i.val+1, hn⟩, by change j ≤ i.val + 1; omega, Or.inr he⟩

private def collarState (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) (j : Nat) :
    Family (Label m) := rawEndpoint (ground m) (facets (cycleIndependentOn m hm))
      (collarRest m j) (collarRest_up m hm h1 j)

private theorem collarRest_subset (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) (T : Finset (Label m)) (hT : T ∈ collarRest m j.val)
    (hsub : T ⊆ collarB m j) : T = collarA m j ∨ T = collarB m j := by
  obtain ⟨i, hi, he⟩ := (mem_collarRest m j.val T).mp hT
  have hai : collarA m i ⊆ T := by
    rcases he with rfl | rfl
    · exact le_rfl
    · exact Finset.subset_insert _ _
  have hij : i = j := by
    apply Fin.ext
    by_contra hn
    have hlt : j.val < i.val := by omega
    let q : Label m := ⟨3*j.val+3, by have := j.isLt; omega⟩
    have hq : q ∈ collarA m i := by
      apply (collarA_mem m h1 i q).mpr
      right; left
      dsimp [q]
      exact ⟨by omega, by omega, by omega⟩
    have hqn : q ∉ collarB m j := by
      simp only [collarB, Finset.mem_insert, collarA_mem m h1, Fin.ext_iff, collarPivot]
      dsimp [q]
      have := good_width m h1
      have := j.isLt
      omega
    exact hqn (hsub (hai hq))
  simpa only [hij] using he

private theorem collarState_cofaces (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) (s : Finset (Label m)) (hs : s ∈ collarState m hm h1 j.val)
    (hfs : collarLower m j ⊆ s) : s = collarLower m j ∨ s = collarUpper m j := by
  obtain ⟨hsW, hs⟩ := hs
  have hbW := (cycleWordData m hm).supported _ (collar_pair_data m hm h1 j).2.1
  have hcsub : ground m \ s ⊆ collarB m j := by
    intro x hx
    by_contra hn
    exact (Finset.mem_sdiff.mp hx).2 (hfs (Finset.mem_sdiff.mpr
      ⟨(Finset.mem_sdiff.mp hx).1, hn⟩))
  have hcK := (facets (cycleIndependentOn m hm)).lower hcsub
    (collar_pair_data m hm h1 j).2.1
  have hcH : ground m \ s ∈ collarRest m j.val := hs.resolve_left (fun h => h hcK)
  rcases collarRest_subset m hm h1 j _ hcH hcsub with he | he
  · right
    have h := congrArg (fun q : Finset (Label m) => ground m \ q) he
    simpa only [Finset.sdiff_sdiff_eq_self hsW, collarUpper] using h
  · left
    have h := congrArg (fun q : Finset (Label m) => ground m \ q) he
    simpa only [Finset.sdiff_sdiff_eq_self hsW, collarLower] using h

private theorem collar_upper_eq (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) : insert (collarPivot m j) (collarLower m j) = collarUpper m j := by
  have hd := collar_pair_data m hm h1 j
  have hp := (cycleWordData m hm).supported _ hd.2.1 (Finset.mem_insert_self _ _)
  ext x
  by_cases hx : x = collarPivot m j
  · subst x; simp [collarLower, collarUpper, collarB, hp, hd.2.2]
  · simp [collarLower, collarUpper, collarB, hx]

private theorem collarState_upper (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) : collarUpper m j ∈ collarState m hm h1 j.val := by
  have haW := (cycleWordData m hm).supported _ (collar_pair_data m hm h1 j).1
  refine ⟨Finset.sdiff_subset, Or.inr ?_⟩
  rw [collarUpper, Finset.sdiff_sdiff_eq_self haW]
  exact (mem_collarRest m j.val _).mpr ⟨j, le_rfl, Or.inl rfl⟩

private theorem collarState_next (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) :
    cut (collarState m hm h1 j.val) {collarLower m j} = collarState m hm h1 (j.val+1) := by
  apply SetLike.ext
  intro s
  change (s ∈ collarState m hm h1 j.val ∧ ∀ a ∈ ({collarLower m j} : Finset (Finset (Label m))), ¬ a ⊆ s) ↔ _
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨⟨hsW, hc⟩, hnot⟩
    refine ⟨hsW, ?_⟩
    rcases hc with hn | hc
    · exact Or.inl hn
    · obtain ⟨i, hi, he⟩ := (mem_collarRest m j.val _).mp hc
      by_cases heq : i.val = j.val
      · have hij : i = j := Fin.ext heq
        subst i
        have hsEq : s = collarLower m j ∨ s = collarUpper m j := by
          rcases he with he | he
          · right
            have hh := congrArg (fun T : Finset (Label m) => ground m \ T) he
            simpa only [Finset.sdiff_sdiff_eq_self hsW, collarUpper] using hh
          · left
            have hh := congrArg (fun T : Finset (Label m) => ground m \ T) he
            simpa only [Finset.sdiff_sdiff_eq_self hsW, collarLower] using hh
        have hfs : collarLower m j ⊆ s := by
          rcases hsEq with rfl | rfl
          · exact le_rfl
          · exact Finset.sdiff_subset_sdiff_right _ (Finset.subset_insert _ _)
        exact (hnot hfs).elim
      · exact Or.inr ((mem_collarRest m (j.val+1) _).mpr ⟨i, by omega, he⟩)
  · rintro ⟨hsW, hc⟩
    have hprev : s ∈ collarState m hm h1 j.val := by
      refine ⟨hsW, ?_⟩
      rcases hc with hn | hc
      · exact Or.inl hn
      · obtain ⟨i, hi, he⟩ := (mem_collarRest m (j.val+1) _).mp hc
        exact Or.inr ((mem_collarRest m j.val _).mpr ⟨i, by omega, he⟩)
    refine ⟨hprev, ?_⟩
    intro hfs
    have hb := (collar_pair_data m hm h1 j).2.1
    have hcsub : ground m \ s ⊆ collarB m j := by
      intro x hx
      by_contra hn
      exact (Finset.mem_sdiff.mp hx).2 (hfs (Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp hx).1, hn⟩))
    have hcK := (facets (cycleIndependentOn m hm)).lower hcsub hb
    have hcH := hc.resolve_left (fun h => h hcK)
    obtain ⟨i, hi, he⟩ := (mem_collarRest m (j.val+1) _).mp hcH
    let q : Label m := ⟨3*j.val+3, by have := j.isLt; omega⟩
    have hq : q ∈ collarA m i := by
      apply (collarA_mem m h1 i q).mpr
      right; left
      dsimp [q]; exact ⟨by omega, by omega, by omega⟩
    have hqT : q ∈ ground m \ s := by
      rcases he with he | he <;> rw [he]
      · exact hq
      · exact Finset.mem_insert_of_mem hq
    have hn : q ∉ collarB m j := by
      simp only [collarB, Finset.mem_insert, collarA_mem m h1, Fin.ext_iff, collarPivot]
      dsimp [q]; have := good_width m h1; have := j.isLt; omega
    exact hn (hcsub hqT)

private theorem collarState_final (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    collarState m hm h1 (m/3) = A1 m hm := by
  apply SetLike.ext
  intro s
  rw [← good_dual m hm, dual_mem]
  change (s ⊆ ground m ∧ (ground m \ s ∉ facets (cycleIndependentOn m hm) ∨
    ground m \ s ∈ collarRest m (m/3))) ↔ _
  have hn : ∀ T, T ∉ collarRest m (m/3) := by
    intro T h
    obtain ⟨i, hi, _⟩ := (mem_collarRest _ _ _).mp h
    have := i.isLt
    omega
  simp only [hn, or_false]

private theorem collarState_start (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    collarState m hm h1 0 = collarCore m hm := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hsW, hn | hH⟩
    · left
      change s ∈ A1 m hm
      rw [← good_dual m hm, dual_mem]
      exact ⟨hsW, hn⟩
    · obtain ⟨i, _, he⟩ := (mem_collarRest m 0 _).mp hH
      right
      refine ⟨collarUpper m i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
      have hsub : collarA m i ⊆ ground m \ s := by
        rcases he with he | he
        · rw [he]
        · rw [he]
          exact Finset.subset_insert _ _
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hsW hx, fun hxa =>
        (Finset.mem_sdiff.mp (hsub hxa)).2 hx⟩
  · rintro (hs | ⟨t, ht, hst⟩)
    · change s ∈ A1 m hm at hs
      rw [← good_dual m hm, dual_mem] at hs
      exact ⟨hs.1, Or.inl hs.2⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
      have hsW : s ⊆ ground m := hst.trans Finset.sdiff_subset
      refine ⟨hsW, ?_⟩
      by_cases hc : ground m \ s ∈ facets (cycleIndependentOn m hm)
      · right
        apply collarRest_up m hm h1 0
          ((mem_collarRest m 0 _).mpr ⟨i, Nat.zero_le _, Or.inl rfl⟩) hc
        intro x hx
        have hxW := (cycleWordData m hm).supported _ (collar_pair_data m hm h1 i).1 hx
        exact Finset.mem_sdiff.mpr ⟨hxW, fun hxs => (Finset.mem_sdiff.mp (hst hxs)).2 hx⟩
      · exact Or.inl hc

private def collarFrom (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Nat) (hj : j ≤ m/3) :
    Sequence (project (collarState m hm h1 j)) (project (A1 m hm)) := by
  by_cases hlt : j < m/3
  · let i : Fin (m/3) := ⟨j, hlt⟩
    have hp := cycle_face_proper m hm _ (collar_pair_data m hm h1 i).2.1
    have hne : (collarLower m i).Nonempty := by
      rw [collarLower, Finset.sdiff_nonempty]
      exact fun h => hp.ne (Finset.Subset.antisymm hp.subset h)
    have hv : collarPivot m i ∉ collarLower m i := by simp [collarLower, collarB]
    have hu : insert (collarPivot m i) (collarLower m i) ∈ collarState m hm h1 j := by
      rw [collar_upper_eq m hm h1 i]
      exact collarState_upper m hm h1 i
    have hf : ∀ s ∈ collarState m hm h1 j, collarLower m i ⊆ s →
        s = collarLower m i ∨ s = insert (collarPivot m i) (collarLower m i) := by
      intro s hs hfs
      rw [collar_upper_eq m hm h1 i]
      exact collarState_cofaces m hm h1 i s hs hfs
    let P := emitPair (collarState m hm h1 j) (collarLower m i) (collarPivot m i) hne hv hu hf
    have hret : P.retained = project (collarState m hm h1 (j+1)) := by
      rw [emitPair_retained, collarState_next m hm h1 i]
    exact Sequence.step P ((collarFrom m hm h1 (j+1) (by omega)).cast hret.symm rfl)
  · have he : j = m/3 := by omega
    subst j
    exact (Sequence.refl _).cast (congrArg project (collarState_final m hm h1)).symm rfl
termination_by m/3-j
decreasing_by omega

/-- Genuine increasing P07 collar list on B1 ALONE. Each step above constructs
    its native pair from the exact current family and its two cofaces. -/
def collarSequence (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    Sequence (project (collarCore m hm)) (project (A1 m hm)) :=
  (collarFrom m hm h1 0 (Nat.zero_le _)).cast
    (congrArg project (collarState_start m hm h1)) rfl

/-- Good-class fill1 with actual main list, exact critical eta1 and the
    SEPARATE collar just constructed. -/
def fill1Good (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    Filling (ground m) (A1 m hm) where
  empty_mem := by
    rw [← good_dual m hm, dual_mem]
    refine ⟨Finset.empty_subset _, ?_⟩
    intro h
    have hp := cycle_face_proper m hm _ h
    simp only [Finset.sdiff_empty] at hp
    exact hp.ne rfl
  collar := collarCore m hm
  critical := {eta1 m hm}
  contains := le_sup_left
  supported := by
    intro s hs
    rcases hs with hs | ⟨t, ht, hst⟩
    · rw [← wheelRoot_eq_A1 m hm] at hs
      exact (rimRows m (by omega)).root_supported s hs
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
      exact hst.trans Finset.sdiff_subset
  critical_supported := by intro s hs; rw [Finset.mem_singleton.mp hs]; exact Finset.sdiff_subset
  cells := eta_good_cells m hm h1
  main := (goodCycleContract m hm h1).protectedDualWordSequence.cast rfl
    (congrArg project (good_endpoint m hm h1))
  separate := collarSequence m hm h1

/-- Both residues and the collar residue share the original Filling API;
    none of the desired outputs is an input to this all-m function. -/
def fill1 (m : Nat) (hm : 3 ≤ m) : Filling (ground m) (A1 m hm) :=
  if h1 : m % 3 = 1 then fill1Good m hm h1 else fill1Excluded m hm h1

theorem fill1_critical (m : Nat) (hm : 3 ≤ m) :
    (fill1 m hm).critical = cycleCritical m hm := by
  unfold fill1
  split_ifs with h1
  · simp only [fill1Good, cycleCritical, if_neg (by omega : m % 3 ≠ 0), if_pos h1, eta1]
  · exact fill1Excluded_critical m hm h1

private def nativeTable (K : PreAbstractSimplicialComplex V) : Finset (Finset V) :=
  by
    classical
    exact Finset.univ.filter (fun s => s ∈ K)
private def nativeEuler (K : PreAbstractSimplicialComplex V) : Int :=
  ∑ s ∈ nativeTable K, (-1 : Int)^s.card

/- Finite, ordinary, codimension-one pairs preserve this invariant. The
   argument uses the actual retained family and excludes the empty face via
   the imported CollapsePair lower_nonempty/upper_mem conditions. -/
private theorem pair_euler (P : CollapsePair V) : nativeEuler P.ambient = nativeEuler P.retained := by
  have hlu : P.lower ≠ P.upper := by
    intro he
    exact P.apex_notMem (he.symm ▸ Finset.mem_insert_self _ _)
  have hl : P.lower ∈ P.ambient := P.lower_mem
  have hlt : P.lower ∉ nativeTable P.retained := by
    simp only [nativeTable, Finset.mem_filter, Finset.mem_univ, true_and,
      P.mem_retained_iff]
    tauto
  have hut : P.upper ∉ nativeTable P.retained := by
    simp only [nativeTable, Finset.mem_filter, Finset.mem_univ, true_and,
      P.mem_retained_iff]
    tauto
  have ht : nativeTable P.ambient = insert P.lower (insert P.upper (nativeTable P.retained)) := by
    ext s
    simp only [nativeTable, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, P.mem_retained_iff]
    constructor
    · intro hs
      by_cases hsl : s = P.lower
      · exact Or.inl hsl
      · by_cases hsu : s = P.upper
        · exact Or.inr (Or.inl hsu)
        · exact Or.inr (Or.inr ⟨hs, hsl, hsu⟩)
    · rintro (rfl | rfl | ⟨hs, _, _⟩)
      · exact hl
      · exact P.upper_mem
      · exact hs
  unfold nativeEuler
  rw [ht, Finset.sum_insert (by simp [hlt, hlu]), Finset.sum_insert hut]
  have hc : P.upper.card = P.lower.card+1 := by
    exact Finset.card_insert_of_notMem P.apex_notMem
  rw [hc, pow_succ]
  ring

private theorem sequence_euler {K L : PreAbstractSimplicialComplex V} (S : Sequence K L) :
    nativeEuler K = nativeEuler L := by
  induction S with
  | refl => rfl
  | step P T ih => exact (pair_euler P).trans ih

private theorem cell_euler (B : Family V) (d : Finset V)
    (hc : CriticalData B {d}) :
    nativeEuler (project (endpoint B {d})) = (-1 : Int)^d.card + nativeEuler (project B) := by
  have hn := hc.nonempty d (by simp)
  have ha := hc.absent d (by simp)
  have ht : nativeTable (project (endpoint B {d})) = insert d (nativeTable (project B)) := by
    ext s
    simp only [nativeTable, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, mem_project]
    constructor
    · rintro ⟨hsn, hs | ⟨t, ht, hst⟩⟩
      · exact Or.inr ⟨hsn, hs⟩
      · have he : t = d := Finset.mem_singleton.mp ht
        subst t
        by_cases hs : s = d
        · exact Or.inl hs
        · exact Or.inr ⟨hsn, hc.boundary d (by simp) s
            (Finset.ssubset_iff_subset_ne.mpr ⟨hst, hs⟩)⟩
    · rintro (he | ⟨hsn, hs⟩)
      · rw [he]
        exact ⟨hn, Or.inr ⟨d, by simp, le_rfl⟩⟩
      · exact ⟨hsn, Or.inl hs⟩
  unfold nativeEuler
  rw [ht, Finset.sum_insert]
  simp only [nativeTable, Finset.mem_filter, Finset.mem_univ, true_and, mem_project,
    not_and_or, ha, not_false_eq_true, or_true]

/-- Exact raw-path complementary critical family in every residue. -/
theorem pathFilling_critical (m : Nat) (hm : 3 ≤ m) :
    (pathFilling m hm).critical =
      if m % 3 = 1 then ∅ else
        {ground m \ FiniteIndependentPathGreedy.pathChosen (pathRootPath m hm)} := by
  change (criticalFaces (pathRootWordData m hm).word).image (fun T => ground m \ T) = _
  rw [root_word, pathWord_critical_formula _ (pathRootPath_nodup m hm), pathRootPath_length]
  split_ifs <;> simp

/-- Necessity includes BOTH excluded residues. It uses ordinary finite Euler
    invariance and the actual one-critical partial filling; no homology or
    inferred collapse from a contractible target is used. -/
theorem gamma_iff (m : Nat) (hm : 3 ≤ m) :
    Nonempty (Sequence (project (delta (ground m))) (project (pathRoot m hm))) ↔
      goodResidue m := by
  constructor
  · rintro ⟨G⟩
    by_contra hn
    have hr : m % 3 ≠ 1 := by
      intro h1
      exact hn ⟨m/3, good_width m h1⟩
    let d := ground m \ FiniteIndependentPathGreedy.pathChosen (pathRootPath m hm)
    have hc : (pathFilling m hm).critical = {d} := by
      rw [pathFilling_critical, if_neg hr]
    have hmain := sequence_euler (pathFilling m hm).main
    have hgamma := sequence_euler G
    have hcells : CriticalData (pathRoot m hm) {d} := by
      rw [← hc]
      exact (pathFilling m hm).cells
    have hcell := cell_euler (pathRoot m hm) d hcells
    change nativeEuler (project (delta (ground m))) =
      nativeEuler (project (endpoint (pathRoot m hm) (pathFilling m hm).critical)) at hmain
    rw [hc] at hmain
    have hzero : (-1 : Int)^d.card = 0 := by omega
    exact (pow_ne_zero d.card (by decide : (-1 : Int) ≠ 0)) hzero
  · intro hg
    exact ⟨gammaGood m hm hg⟩

end D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
