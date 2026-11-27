/- GID: D5/S3/Topology/FixedTargetGraphTermination
   generality: G
   mirror-B: D5/B/S3/Topology/FixedTargetGraphTermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Triangle moves on a finite family of paths lift to relative contiguity on padded intervals. -/

import D5.S3.Topology.PathContiguity
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic
import OmegaBuild.Commands

/-! The finite edge-path argument in Section 24 of two-dimensional-factor-two.
A path is indexed by its vertices, since consecutive equal vertices are allowed.
Every face condition is checked in the given target complex. -/

compile_only_with_mathlib


namespace D5.S3.Topology.FixedTargetGraphTermination

open BarycentricBaseRigidity (Contiguous faceImage)
open BarycentricGraphDistance (Vertex oneSkeleton)
open PathContiguity (intervalComplex)
open Relation (ReflTransGen SymmGen)

set_option autoImplicit false

noncomputable section

local instance (X : Type*) : DecidableEq X := Classical.decEq X

variable {X Y : Type} {K : PreAbstractSimplicialComplex X}
variable {P : PreAbstractSimplicialComplex Y}

/-- Consecutive vertices span a face, which may be a singleton. -/
structure EdgePath (K : PreAbstractSimplicialComplex X) where
  length : ℕ
  point : Fin (length + 1) → Vertex K
  edge : ∀ i : Fin length, ({(point i.castSucc).val, (point i.succ).val} : Finset X) ∈ K

/-- Positions beyond the right endpoint read as the right endpoint. -/
def EdgePath.read (p : EdgePath K) (i : ℕ) : Vertex K :=
  p.point ⟨min i p.length, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The path of length one provided by an edge, allowing equal endpoints. -/
def EdgePath.single (x y : Vertex K) (h : ({x.val, y.val} : Finset X) ∈ K) :
    EdgePath K where
  length := 1
  point i := if i.val = 0 then x else y
  edge i := by
    have hi : i.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
    simpa [hi] using h

@[simp]
theorem EdgePath.read_single (x y : Vertex K)
    (h : ({x.val, y.val} : Finset X) ∈ K) (i : ℕ) :
    (EdgePath.single x y h).read i = if i = 0 then x else y := by
  change (if min i 1 = 0 then x else y) = _
  have he : min i 1 = 0 ↔ i = 0 := by omega
  simp only [he]

private theorem EdgePath.read_le (p : EdgePath K) (i : ℕ) (hi : i ≤ p.length) :
    p.read i = p.point ⟨i, Nat.lt_succ_of_le hi⟩ :=
  congrArg p.point (Fin.ext (min_eq_left hi))

private theorem EdgePath.read_clamp (p : EdgePath K) (i : ℕ) :
    p.read (min i p.length) = p.read i :=
  congrArg p.point (Fin.ext (min_eq_left (min_le_right i p.length)))

private theorem EdgePath.read_edge (p : EdgePath K) (i : ℕ) :
    ({(p.read i).val, (p.read (i + 1)).val} : Finset X) ∈ K := by
  by_cases hi : i < p.length
  · rw [p.read_le i (Nat.le_of_lt hi), p.read_le (i + 1) (Nat.succ_le_of_lt hi)]
    exact p.edge ⟨i, hi⟩
  · have heq : p.read (i + 1) = p.read i := by
      apply congrArg p.point
      apply Fin.ext
      change min (i + 1) p.length = min i p.length
      rw [min_eq_right (show p.length ≤ i + 1 by omega),
        min_eq_right (show p.length ≤ i by omega)]
    rw [heq]
    simpa using (p.read i).property

private def vertexInFace {s : Finset Y} (hs : s ∈ P) (x : {a // a ∈ s}) : Vertex P :=
  ⟨x.val, (P.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr x.property)
    (Finset.singleton_nonempty _)⟩

private theorem contiguous_of_face_carriers {f g : Vertex P → Vertex K}
    (h : ∀ s : Finset Y, s ∈ P → ∃ t : Finset X, t ∈ K ∧
      ∀ x : Vertex P, x.val ∈ s → (f x).val ∈ t ∧ (g x).val ∈ t) :
    Contiguous f g := by
  intro s hs
  obtain ⟨t, ht, hc⟩ := h s hs
  have hf : faceImage f hs ⊆ t := by
    intro y hy
    unfold faceImage at hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact (hc (vertexInFace hs x) x.property).1
  have hg : faceImage g hs ⊆ t := by
    intro y hy
    unfold faceImage at hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact (hc (vertexInFace hs x) x.property).2
  have hne : (faceImage f hs).Nonempty :=
    Finset.image_nonempty.mpr (Finset.attach_nonempty_iff.mpr (P.isRelLowerSet_faces hs).1)
  exact (K.isRelLowerSet_faces ht).2 (Finset.union_subset hf hg)
    (hne.mono Finset.subset_union_left)

/-- On a source face, a pair of contiguous numerical maps uses at most two
consecutive indices. -/
private theorem face_schedule_values {dec : DecidableEq Y} {f g : Vertex P → ℕ}
    (h : PathContiguity.Contiguous (@oneSkeleton Y dec P) f g) {s : Finset Y} (hs : s ∈ P) :
    ∃ k : ℕ, ∀ x : Vertex P, x.val ∈ s →
      (f x = k ∨ f x = k + 1) ∧ (g x = k ∨ g x = k + 1) := by
  let lower (x : {a // a ∈ s}) := min (f (vertexInFace hs x)) (g (vertexInFace hs x))
  obtain ⟨z, _, hz⟩ := Finset.exists_min_image s.attach lower
    (Finset.attach_nonempty_iff.mpr (P.isRelLowerSet_faces hs).1)
  let y := vertexInFace hs z
  let k := min (f y) (g y)
  refine ⟨k, ?_⟩
  intro x hx
  have hlo : k ≤ min (f x) (g x) :=
    hz ⟨x.val, hx⟩ (Finset.mem_attach _ _)
  have hxy : x = y ∨ (@oneSkeleton Y dec P).Adj x y := by
    by_cases heq : x = y
    · exact Or.inl heq
    · exact Or.inr ⟨heq, (P.isRelLowerSet_faces hs).2
        (Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr z.property⟩)
        (Finset.insert_nonempty _ _)⟩
  have hhi : max (f x) (g x) ≤ k + 1 := h hxy
  have hfx₀ := hlo.trans (min_le_left (f x) (g x))
  have hgx₀ := hlo.trans (min_le_right (f x) (g x))
  have hfx₁ := (le_max_left (f x) (g x)).trans hhi
  have hgx₁ := (le_max_right (f x) (g x)).trans hhi
  omega

private theorem interval_contiguous {n : ℕ} {a b : ℕ → Vertex K}
    (h : ∀ i : ℕ, ∃ t : Finset X, t ∈ K ∧
      (a i).val ∈ t ∧ (a (i + 1)).val ∈ t ∧ (b i).val ∈ t ∧ (b (i + 1)).val ∈ t) :
    Contiguous (fun x : Vertex (intervalComplex n) => a x.val) (fun x => b x.val) := by
  apply contiguous_of_face_carriers
  intro s hs
  let i := s.min' hs.1
  have hi : i ∈ s := Finset.min'_mem _ _
  obtain ⟨t, ht, ha₀, ha₁, hb₀, hb₁⟩ := h i
  refine ⟨t, ht, ?_⟩
  intro x hx
  have hlo : i ≤ x.val := Finset.min'_le _ _ hx
  have hhi : x.val ≤ i + 1 := hs.2.2 x.val hx i hi
  have hx' : x.val = i ∨ x.val = i + 1 := by omega
  rcases hx' with hx' | hx' <;> simp only [hx']
  · exact ⟨ha₀, hb₀⟩
  · exact ⟨ha₁, hb₁⟩

private instance (n : ℕ) : Finite (Vertex (intervalComplex n)) :=
  Finite.of_injective (fun x : Vertex (intervalComplex n) =>
    (⟨x.val, Nat.lt_succ_of_le (x.property.2.1 _ (Finset.mem_singleton_self _))⟩ :
      Fin (n + 1))) (fun _ _ h => Subtype.ext (congrArg Fin.val h))

/-- An interval labelling using path indices and taking the prescribed endpoint
indices. Inserting repeats in order is a special case. -/
def IsPadding (p : EdgePath K) (n : ℕ) (f : Vertex (intervalComplex n) → ℕ) : Prop :=
  PathContiguity.IsIntervalMap (oneSkeleton (intervalComplex n)) p.length f ∧
    (∀ x : Vertex (intervalComplex n), x.val = 0 → f x = 0) ∧
    (∀ x : Vertex (intervalComplex n), x.val = n → f x = p.length)

/-- The padded path in the original target. -/
def paddedPath (p : EdgePath K) {n : ℕ} (f : Vertex (intervalComplex n) → ℕ) :
    Vertex (intervalComplex n) → Vertex K :=
  p.read ∘ f

/-- The two maps are contiguous and agree at the two ends of the source. -/
def RelativeStep (n : ℕ) (f g : Vertex (intervalComplex n) → Vertex K) : Prop :=
  Contiguous f g ∧ ∀ x : Vertex (intervalComplex n), x.val = 0 ∨ x.val = n → f x = g x

private instance (n : ℕ) : Std.Symm (@RelativeStep X K n) where
  symm f g h :=
    ⟨fun s hs => by simpa only [Finset.union_comm] using h.1 s hs,
      fun x hx => (h.2 x hx).symm⟩

private theorem contiguous_padded {n : ℕ} (p : EdgePath K)
    {f g : Vertex (intervalComplex n) → ℕ}
    (h : PathContiguity.Contiguous (oneSkeleton (intervalComplex n)) f g) :
    Contiguous (paddedPath p f) (paddedPath p g) := by
  apply contiguous_of_face_carriers
  intro s hs
  obtain ⟨k, hk⟩ := face_schedule_values h hs
  refine ⟨_, p.read_edge k, ?_⟩
  intro x hx
  obtain ⟨hf, hg⟩ := hk x hx
  constructor
  · rcases hf with hfx | hfx <;> simp [paddedPath, hfx]
  · rcases hg with hgx | hgx <;> simp [paddedPath, hgx]

private theorem padded_self {n : ℕ} {p : EdgePath K}
    {f : Vertex (intervalComplex n) → ℕ} (hf : IsPadding p n f) :
    RelativeStep n (paddedPath p f) (paddedPath p f) := by
  refine ⟨contiguous_padded p ?_, fun _ _ => rfl⟩
  intro x y h
  rw [max_self, min_self]
  rcases h with rfl | hxy
  · exact Nat.le_succ _
  · exact (hf.1.2 hxy).1

/-- Any two placements of repeats on a single path admit a relative chain. -/
theorem compare_paddings {n : ℕ} {p : EdgePath K}
    {f g : Vertex (intervalComplex n) → ℕ}
    (hf : IsPadding p n f) (hg : IsPadding p n g) :
    ReflTransGen (RelativeStep n) (paddedPath p f) (paddedPath p g) := by
  let S : Set (Vertex (intervalComplex n)) := {x | x.val = 0 ∨ x.val = n}
  have hfix : Set.EqOn f g S := by
    intro x hx
    rcases (show x.val = 0 ∨ x.val = n from hx) with h | h
    · exact (hf.2.1 x h).trans (hg.2.1 x h).symm
    · exact (hf.2.2 x h).trans (hg.2.2 x h).symm
  have hchain := PathContiguity.relative_contiguity (oneSkeleton (intervalComplex n))
    p.length S hf.1 hg.1 hfix
  refine ReflTransGen.lift (paddedPath p) ?_ _ _ hchain
  intro a b hab
  exact ⟨contiguous_padded p hab.2.2.2.2,
    fun x hx => congrArg p.read ((hab.2.2.1 hx).trans (hab.2.2.2.1 hx).symm)⟩

private theorem padding_of_trace {n : ℕ} (p : EdgePath K) (r : ℕ → ℕ)
    (hbound : ∀ i, r i ≤ p.length)
    (hstep : ∀ i, r (i + 1) = r i ∨ r (i + 1) = r i + 1)
    (hzero : r 0 = 0) (hend : r n = p.length) :
    IsPadding p n (fun x => r x.val) := by
  refine ⟨⟨fun x => hbound x.val, ?_⟩,
    fun x hx => (congrArg r hx).trans hzero, fun x hx => (congrArg r hx).trans hend⟩
  intro x y hxy
  have hs : ({x.val, y.val} : Finset ℕ) ∈ intervalComplex n := hxy.2
  have h₁ := hs.2.2 x.val (Finset.mem_insert_self _ _) y.val
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have h₂ := hs.2.2 y.val (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) x.val
    (Finset.mem_insert_self _ _)
  have h : y.val = x.val ∨ y.val = x.val + 1 ∨ x.val = y.val + 1 := by omega
  change r x.val ≤ r y.val + 1 ∧ r y.val ≤ r x.val + 1
  rcases h with he | he | he
  · rw [he]
    exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · rw [he]
    rcases hstep x.val with hv | hv <;> rw [hv] <;> omega
  · rw [he]
    rcases hstep y.val with hv | hv <;> rw [hv] <;> omega

private theorem clamp_step {a b m : ℕ} (h : b = a ∨ b = a + 1) :
    min b m = min a m ∨ min b m = min a m + 1 := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  by_cases hm : a < m
  · right
    rw [min_eq_left (Nat.succ_le_of_lt hm), min_eq_left (Nat.le_of_lt hm)]
  · left
    rw [min_eq_right (show m ≤ a + 1 by omega), min_eq_right (show m ≤ a by omega)]

private def rightPadding (p : EdgePath K) (n : ℕ) (x : Vertex (intervalComplex n)) : ℕ :=
  min x.val p.length

private theorem rightPadding_valid {n : ℕ} {p : EdgePath K} (hn : p.length ≤ n) :
    IsPadding p n (rightPadding p n) :=
  padding_of_trace p (fun i => min i p.length) (fun _ => min_le_right _ _)
    (fun _ => clamp_step (Or.inr rfl)) (min_eq_left (Nat.zero_le _)) (min_eq_right hn)

/-- The position map that repeats position k once. -/
def pauseAt (k i : ℕ) : ℕ := if i ≤ k then i else i - 1

private theorem pauseAt_step (k i : ℕ) :
    pauseAt k (i + 1) = pauseAt k i ∨ pauseAt k (i + 1) = pauseAt k i + 1 := by
  by_cases hi : i < k
  · right
    simp only [pauseAt, if_pos (show i + 1 ≤ k by omega), if_pos (Nat.le_of_lt hi)]
  by_cases he : i = k
  · left
    rw [pauseAt, if_neg (show ¬ i + 1 ≤ k by omega),
      pauseAt, if_pos (show i ≤ k by omega)] <;> omega
  · right
    rw [pauseAt, if_neg (show ¬ i + 1 ≤ k by omega),
      pauseAt, if_neg (show ¬ i ≤ k by omega)] <;> omega

/-- Insertion between positions k and k+1, allowing degenerate triangles.
A path of length zero also admits insertion of a copy of its sole vertex. -/
def TriangleInsert (p q : EdgePath K) : Prop :=
  (∃ k : ℕ, k < p.length ∧ q.length = p.length + 1 ∧
    (∀ i : ℕ, i ≠ k + 1 → q.read i = p.read (pauseAt k i)) ∧
    ({(p.read k).val, (q.read (k + 1)).val, (p.read (k + 1)).val} : Finset X) ∈ K) ∨
  (p.length = 0 ∧ q.length = 1 ∧ ∀ i : ℕ, q.read i = p.read i)

private theorem triangle_insert_padded {p q : EdgePath K} {n : ℕ}
    (h : TriangleInsert p q) (hn : q.length ≤ n) :
    ReflTransGen (RelativeStep n)
      (paddedPath p (rightPadding p n)) (paddedPath q (rightPadding q n)) := by
  rcases h with ⟨k, hk, hlen, hmatch, htriangle⟩ | ⟨_, _, heq⟩
  · let r (i : ℕ) := min (pauseAt k i) p.length
    have hp_valid : IsPadding p n (rightPadding p n) := rightPadding_valid (by omega)
    have hr_valid : IsPadding p n (fun x => r x.val) :=
      padding_of_trace p r (fun _ => min_le_right _ _) (fun i => clamp_step (pauseAt_step k i))
        (by simp [r, pauseAt])
        (by
          change min (pauseAt k n) p.length = p.length
          rw [pauseAt, if_neg (show ¬ n ≤ k by omega)]
          exact min_eq_right (by omega))
    have hfirst := compare_paddings hp_valid hr_valid
    have hp_read (i : ℕ) : p.read (r i) = p.read (pauseAt k i) :=
      p.read_clamp (pauseAt k i)
    have hq_read (i : ℕ) : q.read (min i q.length) = q.read i := q.read_clamp i
    have hk₀ : pauseAt k k = k := by simp [pauseAt]
    have hk₁ : pauseAt k (k + 1) = k := by
      rw [pauseAt, if_neg (show ¬ k + 1 ≤ k by omega)] <;> omega
    have hk₂ : pauseAt k (k + 1 + 1) = k + 1 := by
      rw [pauseAt, if_neg (show ¬ k + 1 + 1 ≤ k by omega)] <;> omega
    have hq₀ : q.read k = p.read k := by rw [hmatch k (by omega), hk₀]
    have hq₂ : q.read (k + 1 + 1) = p.read (k + 1) := by
      rw [hmatch (k + 1 + 1) (by omega), hk₂]
    have hlocal : Contiguous (fun x : Vertex (intervalComplex n) => p.read (pauseAt k x.val))
        (fun x => q.read x.val) := by
      refine interval_contiguous (n := n) (a := fun i => p.read (pauseAt k i)) (b := q.read) ?_
      intro i
      by_cases hi : i = k
      · subst i
        rw [hk₀, hk₁, hq₀]
        refine ⟨_, htriangle, ?_, ?_, ?_, ?_⟩ <;> simp
      by_cases hi' : i = k + 1
      · subst i
        rw [hk₁, hk₂, hq₂]
        refine ⟨_, htriangle, ?_, ?_, ?_, ?_⟩ <;> simp
      have hi'' : i + 1 ≠ k + 1 := by omega
      rw [hmatch i hi', hmatch (i + 1) hi'']
      have hp : ({(p.read (pauseAt k i)).val, (p.read (pauseAt k (i + 1))).val} :
          Finset X) ∈ K := by
        rcases pauseAt_step k i with he | he
        · rw [he]
          simpa using (p.read (pauseAt k i)).property
        · rw [he]
          exact p.read_edge (pauseAt k i)
      refine ⟨_, hp, ?_, ?_, ?_, ?_⟩ <;> simp
    refine hfirst.tail ⟨?_, ?_⟩
    · change Contiguous (fun x => p.read (r x.val)) (fun x => q.read (min x.val q.length))
      simpa only [hp_read, hq_read] using hlocal
    · intro x hx
      have hx' : x.val ≠ k + 1 := by
        rcases hx with he | he <;> omega
      change p.read (r x.val) = q.read (min x.val q.length)
      rw [hp_read, hq_read, hmatch x.val hx']
  · have hsame : paddedPath p (rightPadding p n) = paddedPath q (rightPadding q n) := by
      funext x
      change p.read (min x.val p.length) = q.read (min x.val q.length)
      rw [p.read_clamp, q.read_clamp, heq]
    simpa only [hsame] using (ReflTransGen.refl :
      ReflTransGen (RelativeStep n)
        (paddedPath q (rightPadding q n)) (paddedPath q (rightPadding q n)))

private theorem bounded_move_chain {p q : EdgePath K}
    (h : ReflTransGen (SymmGen TriangleInsert) p q) :
    ∃ B : ℕ, p.length ≤ B ∧ q.length ≤ B ∧ ∀ n, B ≤ n →
      ReflTransGen (RelativeStep n)
        (paddedPath p (rightPadding p n)) (paddedPath q (rightPadding q n)) := by
  induction h with
  | refl => exact ⟨p.length, le_rfl, le_rfl, fun _ _ => .refl⟩
  | @tail q r _ hqr ih =>
    obtain ⟨B, hp, hq, hchain⟩ := ih
    refine ⟨max B r.length, hp.trans (le_max_left _ _), le_max_right _ _, ?_⟩
    intro n hn
    have hBn := (le_max_left B r.length).trans hn
    have hqn := hq.trans hBn
    have hrn := (le_max_right B r.length).trans hn
    refine (hchain n hBn).trans ?_
    rcases hqr with hins | hdel
    · exact triangle_insert_padded hins hrn
    · exact symm (triangle_insert_padded hdel hqn)

private theorem finite_family_chain {E A : Type*} [Fintype E] {R : A → A → Prop}
    {f g : E → A} (hf : ∀ e, R (f e) (f e)) (hg : ∀ e, R (g e) (g e))
    (h : ∀ e, ReflTransGen R (f e) (g e)) :
    ReflTransGen (fun a b : E → A => ∀ e, R (a e) (b e)) f g := by
  let S (a b : E → A) := ∀ e, R (a e) (b e)
  let state (s : Finset E) (e : E) := if e ∈ s then g e else f e
  have hs (s : Finset E) : ReflTransGen S f (state s) := by
    induction s using Finset.induction_on with
    | empty => simpa [state] using
        (ReflTransGen.refl : ReflTransGen S f f)
    | @insert e s he ih =>
      let put (a : A) (d : E) := if d = e then a else state s d
      have hput (a b : A) (hab : R a b) : S (put a) (put b) := by
        intro d
        by_cases hde : d = e
        · simpa only [put, if_pos hde] using hab
        · by_cases hds : d ∈ s
          · simpa only [put, if_neg hde, state, if_pos hds] using hg d
          · simpa only [put, if_neg hde, state, if_neg hds] using hf d
      have hstart : put (f e) = state s := by
        funext d
        by_cases hde : d = e
        · subst d
          simp [put, state, he]
        · simp [put, hde]
      have hend : put (g e) = state (insert e s) := by
        funext d
        by_cases hde : d = e
        · subst d
          simp [put, state]
        · simp [put, state, hde]
      have hlocal : ReflTransGen S (put (f e)) (put (g e)) :=
        ReflTransGen.lift put (fun _ _ h => hput _ _ h) _ _ (h e)
      rw [hstart, hend] at hlocal
      exact ih.trans hlocal
  simpa only [state, Finset.mem_univ, if_true] using hs Finset.univ

/-- One bound works for a finite family of complete triangle insertion and
deletion witnesses. At any common interval length above that bound, any
admissible input and output paddings admit a single chain of families. Each
step is contiguous on every interval and fixes both endpoints of every
interval. In particular, a common number of segments can be a power of two. -/
theorem simultaneous_padded_comparison {E : Type*} [Finite E]
    (p q : E → EdgePath K) (h : ∀ e, ReflTransGen (SymmGen TriangleInsert) (p e) (q e)) :
    ∃ B : ℕ, (∀ e, (p e).length ≤ B ∧ (q e).length ≤ B) ∧
      ∀ n, B ≤ n → ∀ (a b : E → Vertex (intervalComplex n) → ℕ),
        (∀ e, IsPadding (p e) n (a e)) → (∀ e, IsPadding (q e) n (b e)) →
        ReflTransGen (fun f g : E → Vertex (intervalComplex n) → Vertex K =>
          ∀ e, RelativeStep n (f e) (g e))
          (fun e => paddedPath (p e) (a e)) (fun e => paddedPath (q e) (b e)) := by
  letI := Fintype.ofFinite E
  choose L hL using fun e => bounded_move_chain (h e)
  let B := Finset.univ.sup L
  have hLB (e : E) : L e ≤ B := Finset.le_sup (Finset.mem_univ e)
  refine ⟨B, fun e => ⟨(hL e).1.trans (hLB e), (hL e).2.1.trans (hLB e)⟩, ?_⟩
  intro n hn a b ha hb
  have hLn (e : E) := (hLB e).trans hn
  apply finite_family_chain (fun e => padded_self (ha e)) (fun e => padded_self (hb e))
  intro e
  have hp := rightPadding_valid (p := p e) (n := n) ((hL e).1.trans (hLn e))
  have hq := rightPadding_valid (p := q e) (n := n) ((hL e).2.1.trans (hLn e))
  exact (compare_paddings (ha e) hp).trans
    (((hL e).2.2 n (hLn e)).trans (compare_paddings hq (hb e)))

private def joinedVertex (left right : EdgePath K) (i : ℕ) : Vertex K :=
  if i ≤ left.length then left.read (left.length - i) else right.read (i - left.length)

/-- Traverse one path backwards and then the other forwards from their common start. -/
def joinAtStart (left right : EdgePath K) (hstart : left.read 0 = right.read 0) :
    EdgePath K where
  length := left.length + right.length
  point i := joinedVertex left right i.val
  edge i := by
    change ({(joinedVertex left right i.val).val,
      (joinedVertex left right (i.val + 1)).val} : Finset X) ∈ K
    by_cases hi : i.val + 1 ≤ left.length
    · have hprevious : left.length - i.val = left.length - (i.val + 1) + 1 := by omega
      simp only [joinedVertex, if_pos hi, if_pos (show i.val ≤ left.length by omega), hprevious]
      rw [Finset.pair_comm]
      exact left.read_edge _
    · by_cases he : i.val = left.length
      · simp only [joinedVertex, ite_eq_left he.le, ite_eq_right hi]
        rw [he, Nat.sub_self, hstart]
        rw [show left.length + 1 - left.length = 1 by omega]
        exact right.read_edge 0
      · have hi' : ¬ i.val ≤ left.length := by omega
        have hs : i.val + 1 - left.length = i.val - left.length + 1 := by omega
        simp only [joinedVertex, if_neg hi, if_neg hi', hs]
        exact right.read_edge _

/-- Put the joint at the middle of an interval, using repetitions towards
the two outer endpoints. The padding preserves the originally chosen path
through the common start, including when either path is constant. -/
theorem joinAtStart_centered_padding (left right : EdgePath K)
    (hstart : left.read 0 = right.read 0) {M : ℕ}
    (hleft : left.length ≤ M) (hright : right.length ≤ M) :
    ∃ a : Vertex (intervalComplex (2 * M)) → ℕ,
      IsPadding (joinAtStart left right hstart) (2 * M) a ∧
      ∀ i, paddedPath (joinAtStart left right hstart) a i =
        if i.val ≤ M then left.read (M - i.val) else right.read (i.val - M) := by
  let r (i : ℕ) := if i ≤ M then left.length - min (M - i) left.length
                    else left.length + min (i - M) right.length
  have hb (i : ℕ) : r i ≤ left.length + right.length := by
    dsimp [r]
    split <;> omega
  have hstep (i : ℕ) : r (i + 1) = r i ∨ r (i + 1) = r i + 1 := by
    dsimp [r]
    split <;> split <;> omega
  have hzero : r 0 = 0 := by simp [r, min_eq_right hleft]
  have hend : r (2 * M) = left.length + right.length := by
    dsimp [r]
    split <;> omega
  refine ⟨fun i => r i.val, padding_of_trace _ r hb hstep hzero hend, ?_⟩
  intro i
  change (joinAtStart left right hstart).read (r i.val) = _
  rw [EdgePath.read_le _ _ (hb _)]
  change joinedVertex left right (r i.val) = _
  by_cases hi : i.val ≤ M
  · simp only [r, hi, if_true, joinedVertex,
      if_pos (Nat.sub_le left.length (min (M - i.val) left.length))]
    rw [show left.length - (left.length - min (M - i.val) left.length) =
      min (M - i.val) left.length by omega, left.read_clamp]
  · simp only [r, hi, if_false, joinedVertex]
    by_cases hz : min (i.val - M) right.length = 0
    · simp [hz, hstart, ← right.read_clamp (i.val - M)]
    · rw [if_neg (by omega), show left.length + min (i.val - M) right.length -
        left.length = min (i.val - M) right.length by omega, right.read_clamp]

/-- Glue the interval chains on a graph with specified subdivided-edge
parametrizations. An interior point belongs to a single interval. Every
source face is covered by an interval face or is a singleton outside the
interiors. The assembled chain fixes all old endpoints and isolated vertices. -/
theorem glue_relative_path_chains {E : Type*} {n : ℕ}
    (chart : E → Vertex (intervalComplex n) → Vertex P)
    (hinj : ∀ e, Function.Injective (chart e))
    (hdisjoint : ∀ (e d : E) (i j : Vertex (intervalComplex n)),
      i.val ≠ 0 → i.val ≠ n → chart e i = chart d j → e = d)
    (hcover : ∀ s : Finset Y, s ∈ P →
      (∃ x : Vertex P, s = {x.val} ∧
        ¬ ∃ (e : E) (i : Vertex (intervalComplex n)), i.val ≠ 0 ∧ i.val ≠ n ∧ chart e i = x) ∨
      ∃ (e : E) (t : Finset ℕ), t ∈ intervalComplex n ∧
        ∀ x : Vertex P, x.val ∈ s →
          ∃ i : Vertex (intervalComplex n), i.val ∈ t ∧ chart e i = x)
    (f : Vertex P → Vertex K)
    {a b : E → Vertex (intervalComplex n) → Vertex K}
    (ha : ∀ e i, a e i = f (chart e i))
    (hchain : ReflTransGen (fun a b => ∀ e, RelativeStep n (a e) (b e)) a b) :
    let old : Set (Vertex P) :=
      {x | ¬ ∃ (e : E) (i : Vertex (intervalComplex n)), i.val ≠ 0 ∧ i.val ≠ n ∧ chart e i = x}
    ∃ g : Vertex P → Vertex K,
      ReflTransGen (fun u v => Contiguous u v ∧ Set.EqOn u v old) f g ∧
      (∀ e i, g (chart e i) = b e i) ∧ Set.EqOn g f old := by
  classical
  let I := Vertex (intervalComplex n)
  let A := E → I → Vertex K
  let Interior (i : I) := i.val ≠ 0 ∧ i.val ≠ n
  let hasInterior (x : Vertex P) := ∃ ei : E × I, Interior ei.2 ∧ chart ei.1 ei.2 = x
  let old : Set (Vertex P) := {x | ¬ ∃ (e : E) (i : I), i.val ≠ 0 ∧ i.val ≠ n ∧ chart e i = x}
  let fill (c : A) (x : Vertex P) : Vertex K :=
    if h : hasInterior x then c h.choose.1 h.choose.2 else f x
  let Fixed (c : A) := ∀ (e : E) (i : I), i.val = 0 ∨ i.val = n → c e i = f (chart e i)
  let R (u v : Vertex P → Vertex K) := Contiguous u v ∧ Set.EqOn u v old
  change ∃ g, ReflTransGen R f g ∧ (∀ e i, g (chart e i) = b e i) ∧ Set.EqOn g f old
  have hfill_fixed (c : A) : Set.EqOn (fill c) f old := by
    intro x hx
    have hx' : ¬ hasInterior x := by
      rintro ⟨⟨e, i⟩, hi, heq⟩
      exact hx ⟨e, i, hi.1, hi.2, heq⟩
    exact dif_neg hx'
  have htrace {c : A} (hc : Fixed c) (e : E) (i : I) : fill c (chart e i) = c e i := by
    by_cases hi : Interior i
    · have hex : hasInterior (chart e i) := ⟨(e, i), hi, rfl⟩
      dsimp only [fill]
      rw [dif_pos hex]
      obtain ⟨hj, heq⟩ := hex.choose_spec
      have hed := hdisjoint _ _ _ _ hj.1 hj.2 heq
      have hji : hex.choose.2 = i := hinj e (by simpa only [hed] using heq)
      rw [hed, hji]
    · have hex : ¬ hasInterior (chart e i) := by
        rintro ⟨⟨d, j⟩, hj, heq⟩
        have hde := hdisjoint d e j i hj.1 hj.2 heq
        subst d
        exact hi ((hinj e heq) ▸ hj)
      have hend : i.val = 0 ∨ i.val = n := by
        by_cases h0 : i.val = 0
        · exact Or.inl h0
        · by_cases hn : i.val = n
          · exact Or.inr hn
          · exact False.elim (hi ⟨h0, hn⟩)
      dsimp only [fill]
      rw [dif_neg hex, hc e i hend]
  have hf : fill a = f := by
    funext x
    by_cases hx : hasInterior x
    · dsimp only [fill]
      rw [dif_pos hx, ha, hx.choose_spec.2]
    · exact dif_neg hx
  have hstep {c d : A} (hc : Fixed c) (hd : Fixed d)
      (hcd : ∀ e, RelativeStep n (c e) (d e)) : R (fill c) (fill d) := by
    refine ⟨?_, fun x hx => (hfill_fixed c hx).trans (hfill_fixed d hx).symm⟩
    apply contiguous_of_face_carriers
    intro s hs
    rcases hcover s hs with ⟨x, hsingleton, hx⟩ | ⟨e, t, ht, hto⟩
    · refine ⟨{(f x).val}, (f x).property, ?_⟩
      intro y hy
      rw [hsingleton] at hy
      have hyx : y = x := Subtype.ext (Finset.mem_singleton.mp hy)
      subst y
      simp [hfill_fixed c hx, hfill_fixed d hx]
    · refine ⟨_, (hcd e).1 t ht, ?_⟩
      intro x hx
      obtain ⟨i, hi, rfl⟩ := hto x hx
      rw [htrace hc, htrace hd]
      have hm (u : I → Vertex K) : (u i).val ∈ faceImage u ht := by
        unfold faceImage
        exact Finset.mem_image.mpr ⟨⟨i.val, hi⟩, Finset.mem_attach _ _, rfl⟩
      exact ⟨Finset.mem_union_left _ (hm (c e)), Finset.mem_union_right _ (hm (d e))⟩
  have hg : Fixed b ∧ ReflTransGen R f (fill b) := by
    induction hchain with
    | refl =>
      refine ⟨fun e i _ => ha e i, ?_⟩
      simpa only [hf] using (ReflTransGen.refl : ReflTransGen R f f)
    | @tail c d _ hcd ih =>
      have hd : Fixed d := fun e i hi => ((hcd e).2 i hi).symm.trans (ih.1 e i hi)
      exact ⟨hd, ih.2.tail (hstep ih.1 hd hcd)⟩
  exact ⟨fill b, hg.2, htrace hg.1, hfill_fixed b⟩

/-- Edge-path witnesses can replace all subdivided old edges by paths through
one base vertex. The two halves are padded to the same length and the old
vertices are fixed during the replacement. The initial map on each old edge
may use any selection carried by the supplied target face. -/
theorem replace_by_centered_paths {E V : Type*} [Finite E]
    (p : E → EdgePath K) (paths : V → EdgePath K)
    (base : Vertex K) (hstart : ∀ v, (paths v).read 0 = base)
    (left right : E → V)
    (hmoves : ∀ e, ReflTransGen (SymmGen TriangleInsert) (p e)
      (joinAtStart (paths (left e)) (paths (right e))
        ((hstart _).trans (hstart _).symm))) :
    ∃ B : ℕ, ∀ {Z : Type} {P : PreAbstractSimplicialComplex Z},
      ∀ (M : ℕ), B ≤ M → (∀ v, (paths v).length ≤ M) →
      ∀ (chart : E → Vertex (intervalComplex (2 * M)) → Vertex P)
        (hinj : ∀ e, Function.Injective (chart e))
        (hdisjoint : ∀ e d i j, i.val ≠ 0 → i.val ≠ 2 * M →
          chart e i = chart d j → e = d)
        (hcover : ∀ s : Finset Z, s ∈ P →
          (∃ x : Vertex P, s = {x.val} ∧
            ¬ ∃ (e : E) (i : Vertex (intervalComplex (2 * M))),
              i.val ≠ 0 ∧ i.val ≠ 2 * M ∧ chart e i = x) ∨
          ∃ (e : E) (t : Finset ℕ), t ∈ intervalComplex (2 * M) ∧
            ∀ x : Vertex P, x.val ∈ s →
              ∃ i : Vertex (intervalComplex (2 * M)), i.val ∈ t ∧ chart e i = x)
        (f g : Vertex P → Vertex K)
        (hcarrier : ∀ e, ∃ t : Finset X, t ∈ K ∧
          (∀ i, (f (chart e i)).val ∈ t) ∧ ∀ i, ((p e).read i).val ∈ t)
        (hend : ∀ e i,
          (i.val = 0 → f (chart e i) = (p e).read 0) ∧
          (i.val = 2 * M → f (chart e i) = (p e).read (p e).length))
        (hnew : ∀ e i, g (chart e i) =
          if i.val ≤ M then (paths (left e)).read (M - i.val)
          else (paths (right e)).read (i.val - M))
        (houtside : ∀ x, (¬ ∃ e i, chart e i = x) → g x = f x),
        ReflTransGen Contiguous f g := by
  let q (e : E) := joinAtStart (paths (left e)) (paths (right e))
    ((hstart _).trans (hstart _).symm)
  obtain ⟨B, hbound, hcompare⟩ := simultaneous_padded_comparison p q hmoves
  refine ⟨B, ?_⟩
  intro Z P M hBM hpaths chart hinj hdisjoint hcover f g hcarrier hend hnew houtside
  let a (e : E) := rightPadding (p e) (2 * M)
  have ha (e : E) : IsPadding (p e) (2 * M) (a e) :=
    rightPadding_valid ((hbound e).1.trans (by omega))
  have centered (e : E) :=
    joinAtStart_centered_padding (paths (left e)) (paths (right e))
      ((hstart _).trans (hstart _).symm) (hpaths _) (hpaths _)
  choose b hb hb_eval using centered
  have hstep (e : E) : RelativeStep (2 * M) (f ∘ chart e) (paddedPath (p e) (a e)) := by
    obtain ⟨t, ht, hf, hp⟩ := hcarrier e
    constructor
    · apply contiguous_of_face_carriers
      exact fun _ _ => ⟨t, ht, fun i _ => ⟨hf i, hp _⟩⟩
    · intro i hi
      change f (chart e i) = (p e).read (a e i)
      rcases hi with hi | hi
      · rw [(ha e).2.1 i hi]
        exact (hend e i).1 hi
      · rw [(ha e).2.2 i hi]
        exact (hend e i).2 hi
  have hchain := (hcompare (2 * M) (by omega) a b ha hb).head hstep
  obtain ⟨g', hchain', hchart, hfixed⟩ :=
    glue_relative_path_chains chart hinj hdisjoint hcover f (fun _ _ => rfl) hchain
  have heq : g' = g := by
    funext x
    by_cases hx : ∃ e i, chart e i = x
    · obtain ⟨e, i, rfl⟩ := hx
      rw [hchart, hnew]
      exact hb_eval e i
    · exact (hfixed (fun ⟨e, i, _, _, he⟩ => hx ⟨e, i, he⟩)).trans
        (houtside x hx).symm
  rw [← heq]
  exact ReflTransGen.lift id (fun _ _ h => h.1) _ _ hchain'

/-- Contract the assembled half paths on a finite split graph. The owner of an
old vertex or half-edge interior is the corresponding old vertex. An unowned
vertex is a midpoint. Each face uses at most one owner, and all paths start at
the same target vertex. An isolated old vertex can have its own owner. -/
theorem contract_padded_half_paths {V : Type*} [Finite (Vertex P)] (base : Vertex K)
    (paths : V → EdgePath K) (hstart : ∀ v, (paths v).read 0 = base)
    (owner : Vertex P → Option V)
    (hface : ∀ s : Finset Y, s ∈ P → ∃ w : Option V,
      ∀ x : Vertex P, x.val ∈ s → owner x = none ∨ owner x = w)
    (M : ℕ) (r : Vertex P → ℕ)
    (hr : PathContiguity.IsIntervalMap (oneSkeleton P) M r)
    (hmid : ∀ x, owner x = none → r x = 0) :
    ReflTransGen Contiguous
      (fun x => (owner x).elim base (fun v => (paths v).read (r x))) (fun _ => base) := by
  let S : Set (Vertex P) := {x | owner x = none}
  let zero : Vertex P → ℕ := fun _ => 0
  let stage (a : Vertex P → ℕ) (x : Vertex P) :=
    (owner x).elim base (fun v => (paths v).read (a x))
  have hzero : PathContiguity.IsIntervalMap (oneSkeleton P) M zero :=
    ⟨fun _ => Nat.zero_le _, fun _ _ _ => ⟨Nat.zero_le _, Nat.zero_le _⟩⟩
  have hfix : Set.EqOn r zero S := fun x hx => hmid x hx
  have hchain := PathContiguity.relative_contiguity (oneSkeleton P) M S hr hzero hfix
  have hstep (a b : Vertex P → ℕ)
      (hab : PathContiguity.RelativeContiguous (oneSkeleton P) M S r a b) :
      Contiguous (stage a) (stage b) := by
    apply contiguous_of_face_carriers
    intro s hs
    obtain ⟨w, hw⟩ := hface s hs
    cases w with
    | none =>
      refine ⟨{base.val}, base.property, ?_⟩
      intro x hx
      have ho : owner x = none := (hw x hx).elim id id
      simp [stage, ho]
    | some v =>
      obtain ⟨k, hk⟩ := face_schedule_values hab.2.2.2.2 hs
      refine ⟨_, (paths v).read_edge k, ?_⟩
      intro x hx
      have hread : stage a x = (paths v).read (a x) ∧
          stage b x = (paths v).read (b x) := by
        rcases hw x hx with ho | ho
        · have ha : a x = 0 := (hab.2.2.1 (show x ∈ S from ho)).trans (hmid x ho)
          have hb : b x = 0 := (hab.2.2.2.1 (show x ∈ S from ho)).trans (hmid x ho)
          simp [stage, ho, ha, hb, hstart]
        · simp [stage, ho]
      rw [hread.1, hread.2]
      obtain ⟨ha, hb⟩ := hk x hx
      constructor
      · rcases ha with he | he <;> simp [he]
      · rcases hb with he | he <;> simp [he]
  have hlift := ReflTransGen.lift stage hstep _ _ hchain
  have hend : stage zero = fun _ => base := by
    funext x
    cases ho : owner x <;> simp [stage, zero, ho, hstart]
  change ReflTransGen Contiguous (stage r) (stage zero) at hlift
  rw [hend] at hlift
  exact hlift

end

end D5.S3.Topology.FixedTargetGraphTermination
