/- GID: D5/S3/Combinatorics/Graph/Chordal/PureThreeTreeEmbedding
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite three-tree stackings embed into a prefix-closed part of replicated histories. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.ThreeTrees.PureThreeTreeChild
import D5.S3.Combinatorics.Graph.Chordal.PureThreeTreeRetract
import D5.S3.Combinatorics.Graph.Chordal.ThreeTrees.StackedThreeTreeGraph

compile_only_with_mathlib

/-! Every finite three-tree stacking history has a prefix-closed induced
embedding into the replicated pure three-tree histories. -/

namespace Omega.PureThreeTree
open SimpleGraph Omega.RollingCliques
open StackedTriangleCurvature (Build Face)
noncomputable section

variable {n k : ℕ}
local notation "V" => Vertex n k
local notation "D" => Fin (n+1)
local notation "K" => Fin (k+1)
local notation "W" => StackedTriangleCurvature.Vertex

private def faceFin {m : ℕ} (b : Build m) (p : Face m) : Finset (W m) := by
  classical
  let t := b.triangle p
  exact {t.1,t.2.1,t.2.2}

private theorem mem_faceFin {m : ℕ} (b : Build m) (p : Face m) (x : W m) :
    x ∈ faceFin b p ↔ x ∈ b.faceVertices p := by
  classical
  simp [faceFin, Build.faceVertices]

private theorem card_faceFin {m : ℕ} (b : Build m) (p : Face m) :
    (faceFin b p).card = 3 := by
  classical
  have h := b.triangle_distinct p
  have he : (b.triangle p).1 ∉ ({(b.triangle p).2.1, (b.triangle p).2.2} : Finset (W m)) := by
    simp [h.1,h.2.2.symm]
  have hf : (b.triangle p).2.1 ∉ ({(b.triangle p).2.2} : Finset (W m)) := by simp [h.2.1]
  change ({(b.triangle p).1, (b.triangle p).2.1, (b.triangle p).2.2} : Finset (W m)).card = _
  rw [Finset.card_insert_of_notMem he, Finset.card_insert_of_notMem hf, Finset.card_singleton]

private structure EmbeddingData {m : ℕ} (b : Build m) (n k : ℕ) where
  map : W m ↪ Vertex n k
  adj : ∀ x y, (graph n k).Adj (map x) (map y) ↔ b.graph.Adj x y
  root_mem : ∀ a : Fin 3, ∃ x, map x = root a
  depth_bound : ∀ x, (map x).val.1.stage.val ≤ m
  copy_bound : ∀ x i, ((map x).val.1.step i).2.val ≤ m
  prefix_mem : ∀ x (a : History n k), a.IsPrefix (map x).val.1 → ∃ y, (map y).val.1 = a
  face_top : ∀ p, ∃ x ∈ b.faceVertices p, map x = birth (map x).val.1 ∧
    ∀ y ∈ b.faceVertices p, pre (map y) (map x)

private def root_embedding : EmbeddingData Build.root n k where
  map := ⟨root, fun x y h => congrArg (fun v : V => v.val.2) h⟩
  adj x y := by
    change (graph n k).Adj (root x) (root y) ↔ x ≠ y
    exact ⟨fun h he => h.ne (congrArg root he), root_adj⟩
  root_mem a := ⟨a, rfl⟩
  depth_bound x := le_rfl
  copy_bound x i := le_rfl
  prefix_mem x a h := ⟨x, (History.stage_zero (le_antisymm h.1 (Fin.zero_le _))).symm⟩
  face_top p := by
    cases p
    refine ⟨0, ?_, rfl, fun _ _ => data.refl _⟩
    simp [Build.faceVertices, Build.triangle]

private theorem face_old {m : ℕ} (b : Build m) (p q : Face m) :
    (b.attach p).faceVertices (Sum.inl q) = Sum.inl '' b.faceVertices q := by
  simp [Build.faceVertices, Build.triangle, Set.image_insert_eq]

private theorem face_new {m : ℕ} (b : Build m) (p : Face m) (j : Fin 3) :
    Sum.inr () ∈ (b.attach p).faceVertices (Sum.inr j) ∧
    ∀ x ∈ (b.attach p).faceVertices (Sum.inr j),
      x = Sum.inr () ∨ ∃ y ∈ b.faceVertices p, x = Sum.inl y := by
  fin_cases j <;> constructor <;> simp [Build.faceVertices, Build.triangle]

private theorem attach_embedding {m : ℕ} {b : Build m} (D₀ : EmbeddingData b n k)
    (p : Face m) (hn : m < n) (hk : m < k) :
    Nonempty (EmbeddingData (b.attach p) n k) := by
  classical
  let f := D₀.map
  obtain ⟨x,hxp,hxb,htop⟩ := D₀.face_top p
  let base := (f x).val.1
  let t : D := ⟨base.stage.val+1, Nat.succ_lt_succ (lt_of_le_of_lt (D₀.depth_bound x) hn)⟩
  let stamp : K := ⟨m+1, Nat.succ_lt_succ hk⟩
  let P := (faceFin b p).image f
  have hmem (y : W m) : f y ∈ P ↔ y ∈ b.faceVertices p := by
    change f y ∈ (faceFin b p).image f ↔ _
    rw [Finset.mem_image]
    simp only [f.injective.eq_iff, exists_eq_right, mem_faceFin]
  have hcard : P.card = 3 := by
    rw [Finset.card_image_of_injective _ f.injective, card_faceFin]
  have hP (v : V) (hv : v ∈ P) : v.val.1.IsPrefix base ∧
      (v.val.1 = base ∨ (graph n k).Adj v (birth base)) := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    have hy' := (mem_faceFin b p y).1 hy
    refine ⟨htop y hy', ?_⟩
    by_cases he : (f y).val.1 = base
    · exact Or.inl he
    · right
      rw [show birth base = f x from hxb.symm]
      exact (D₀.adj _ _).2 (b.faceVertices_isClique p hy' hxp (fun e => he (congrArg (fun z => (f z).val.1) e)))
  have hpbase : birth base ∈ P := by
    rw [show birth base = f x from hxb.symm]
    exact (hmem x).2 hxp
  obtain ⟨c,hct,hbc,hstamp,hret⟩ := exists_child_with_triangle base t rfl P hcard hP hpbase stamp
  let new : V := birth c
  have hfresh (y : W m) : ¬ c.IsPrefix (f y).val.1 := by
    intro h
    have he : (c.step t).2 = ((f y).val.1.step t).2 := congrArg Prod.snd (h.2 t hct.ge)
    rw [hstamp] at he
    have hm := D₀.copy_bound y t
    change (((f y).val.1.step t).2).val ≤ m at hm
    have hv : (stamp : K).val = (((f y).val.1.step t).2).val := congrArg Fin.val he
    change m+1 = _ at hv
    omega
  have hne (y : W m) : f y ≠ new := by
    intro he
    exact hfresh y ((congrArg (fun v : V => v.val.1) he).symm ▸ data.refl c)
  let F : W (m+1) ↪ V := {
    toFun := Sum.elim f (fun _ => new)
    inj' := by
      rintro (a|⟨⟩) (b|⟨⟩) h
      · exact congrArg Sum.inl (f.injective h)
      · exact (hne a h).elim
      · exact (hne b h.symm).elim
      · rfl }
  have hold {a : History n k} (h : a.IsPrefix c) (ha : a.stage ≤ base.stage) :
      a.IsPrefix base :=
    ⟨ha, fun i hi => (h.2 i hi).trans (hbc.2 i (hi.trans ha)).symm⟩
  have hsplit {a : History n k} (h : a.IsPrefix c) : a = c ∨ a.IsPrefix base := by
    by_cases he : a.stage = c.stage
    · exact Or.inl (h.eq_of_stage_eq he)
    · right
      apply hold h
      have hl : a.stage < c.stage := lt_of_le_of_ne h.1 he
      have hg : a.stage.val < c.stage.val := hl
      rw [hct] at hg
      change a.stage.val < base.stage.val+1 at hg
      omega
  have hforward (y : W m) : (graph n k).Adj (f y) new ↔ y ∈ b.faceVertices p := by
    rw [← hmem]
    constructor
    · intro e
      rcases e.2 with he | h | h
      · exact (hfresh y (he ▸ data.refl (f y).val.1)).elim
      · rcases hsplit h.1 with he | hh
        · exact (hfresh y (he ▸ data.refl (f y).val.1)).elim
        · apply (hret _ hh).1
          have hr : (f y).val.2 ∈ (c.step c.stage).1 (f y).val.1.stage := h.2
          simpa only [hct] using hr
      · exact (hfresh y h.1).elim
    · intro hy
      have hp := (hP _ hy).1
      refine ⟨fun h => hne y (Subtype.ext h), Or.inr (Or.inl ⟨data.trans hp hbc, ?_⟩)⟩
      change (f y).val.2 ∈ (c.step c.stage).1 (f y).val.1.stage
      rw [hct]
      exact (hret _ hp).2 hy
  refine ⟨⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro (a|⟨⟩) (b|⟨⟩)
    · exact D₀.adj a b
    · exact hforward a
    · exact ⟨fun h => (hforward b).1 h.symm, fun h => ((hforward b).2 h).symm⟩
    · exact ⟨fun h => h.ne rfl, False.elim⟩
  · intro a
    obtain ⟨y,hy⟩ := D₀.root_mem a
    exact ⟨Sum.inl y,hy⟩
  · rintro (y|⟨⟩)
    · exact (D₀.depth_bound y).trans (Nat.le_succ _)
    · change c.stage.val ≤ m+1
      rw [hct]
      exact Nat.succ_le_succ (D₀.depth_bound x)
  · rintro (y|⟨⟩) i
    · exact (D₀.copy_bound y i).trans (Nat.le_succ _)
    · change (c.step i).2.val ≤ m+1
      by_cases hi : i ≤ base.stage
      · rw [← hbc.2 _ hi]
        exact (D₀.copy_bound x i).trans (Nat.le_succ _)
      · by_cases he : i = t
        · subst i
          rw [hstamp]
        · have hh : t < i := by
            have hi' : base.stage.val < i.val := lt_of_not_ge hi
            exact lt_of_le_of_ne (Nat.succ_le_of_lt hi') (Ne.symm he)
          rw [c.beyond _ (hct ▸ hh)]
          exact Nat.zero_le _
  · rintro (y|⟨⟩) a h
    · obtain ⟨w,hw⟩ := D₀.prefix_mem y a h
      exact ⟨Sum.inl w,hw⟩
    · rcases hsplit h with he | he
      · exact ⟨Sum.inr (),he.symm⟩
      · obtain ⟨w,hw⟩ := D₀.prefix_mem x a he
        exact ⟨Sum.inl w,hw⟩
  · rintro (j|j)
    · obtain ⟨y,hy,hb,ha⟩ := D₀.face_top j
      refine ⟨Sum.inl y, ?_, hb, ?_⟩
      · rw [face_old]
        exact ⟨y,hy,rfl⟩
      · intro v hv
        rw [face_old] at hv
        obtain ⟨v,hv,rfl⟩ := hv
        exact ha _ hv
    · have hf := face_new b p j
      refine ⟨Sum.inr (),hf.1,rfl,fun y hy => ?_⟩
      rcases hf.2 _ hy with he | ⟨z,hz,rfl⟩
      · subst y
        exact data.refl _
      · exact data.trans (htop _ hz) hbc

private theorem exists_embedding_data {m : ℕ} (b : Build m) (hn : m ≤ n) (hk : m ≤ k) :
    Nonempty (EmbeddingData b n k) := by
  induction b with
  | root => exact ⟨root_embedding⟩
  | @attach m b p ih =>
    obtain ⟨D₀⟩ := ih (Nat.le_of_succ_le hn) (Nat.le_of_succ_le hk)
    exact attach_embedding D₀ p (Nat.lt_of_succ_le hn) (Nat.lt_of_succ_le hk)

/-- A finite pure 3-tree in insertion form embeds as an induced subgraph on a
prefix-closed set of the replicated histories. -/
theorem exists_build_embedding {m : ℕ} (b : Build m) (hn : m ≤ n) (hk : m ≤ k) :
    ∃ (S : Set (History n k)) (f : W m ↪ V),
      History.initial ∈ S ∧
      (∀ {a b}, a.IsPrefix b → b ∈ S → a ∈ S) ∧
      Set.range f = {v | v.val.1 ∈ S} ∧
      ∀ x y, (graph n k).Adj (f x) (f y) ↔ b.graph.Adj x y := by
  obtain ⟨D₀⟩ := exists_embedding_data b hn hk
  let S := Set.range (fun x => (D₀.map x).val.1)
  have h₀ : History.initial ∈ S := by
    obtain ⟨x,hx⟩ := D₀.root_mem 0
    exact ⟨x, congrArg (fun v : V => v.val.1) hx⟩
  refine ⟨S,D₀.map,h₀,?_,?_,D₀.adj⟩
  · rintro a b hab ⟨x,rfl⟩
    exact D₀.prefix_mem x a hab
  · ext v
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x,rfl⟩
    · rintro ⟨x,hx⟩
      by_cases he : v.val.1.stage = 0
      · obtain ⟨y,hy⟩ := D₀.root_mem v.val.2
        refine ⟨y, hy.trans ?_⟩
        exact Subtype.ext (Prod.ext (History.stage_zero he).symm rfl)
      · refine ⟨x, Subtype.ext (Prod.ext hx ?_)⟩
        have hv := v.property.resolve_left he
        have hx' := (D₀.map x).property.resolve_left (by simpa only [hx] using he)
        exact hx'.trans hv.symm

universe u

/-- A Banach budget on the replicated tree applies to every stacking with
at most its depth and copy-index bounds. -/
theorem banach_of_build {m : ℕ} (b : Build m) (hn : m ≤ n) (hk : m ≤ k)
    {R : ℝ} (h : BanachFeasible.{u} n k R)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : W m → W m → E) (hg : ∀ x y, g y x = -g x y)
    (ht : ∀ x y z, b.graph.Adj x y → b.graph.Adj y z → b.graph.Adj x z →
      ‖g x y + g y z - g x z‖ ≤ 1) :
    ∃ p : W m → E, ∀ x y, b.graph.Adj x y → ‖g x y - (p y - p x)‖ ≤ R := by
  obtain ⟨S,f,h₀,hS,hi,hf⟩ := exists_build_embedding b hn hk
  exact banach_of_prefix_closed_embedding h₀ hS f hf hi h g hg ht


end
end Omega.PureThreeTree
