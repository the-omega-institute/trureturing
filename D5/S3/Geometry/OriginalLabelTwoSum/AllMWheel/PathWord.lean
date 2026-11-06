/- GID: D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord
   generality: G
   digest: Ordered distinct paths give exhaustive raw P02 words with global dependencies.
   SOURCE_ONLY_UNCOMPILED: source proofs, no kernel or admission receipt. -/
import D5.S3.Geometry.FiniteProtectedDualWord
import D5.S3.Geometry.FiniteIndependentPathGreedy
import D5.S3.Geometry.OriginalLabelTwoSum.Certificates
import Mathlib.Data.List.Sort
import Mathlib.Tactic

noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
open FiniteProtectedDualWord
open OriginalLabelTwoSum
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Symbol := FiniteProtectedDualWord.Symbol
abbrev Word (W : Finset V) (K : Family V) := FiniteProtectedDualWord.Word W K
abbrev Contract (W : Finset V) (K : Family V) := FiniteProtectedDualWord.Contract W K

/- Literal edges, including repeated-label inputs. Distinctness is imposed on
   the Word theorem, not smuggled into the definition of independence. -/
def pathEdges : List V → Finset (Finset V)
  | [] => ∅
  | [_] => ∅
  | a :: b :: rest => insert {a, b} (pathEdges (b :: rest))
def pathIndependent (vertices : Finset V) (edges : Finset (Finset V)) :
    Finset (Finset V) := by
  classical
  exact vertices.powerset.filter (fun s => ∀ e ∈ edges, ¬ e ⊆ s)
def pathIndependentOn (vertices : List V) : Finset (Finset V) :=
  pathIndependent vertices.toFinset (pathEdges vertices)
def pathFamily (vertices : List V) : Family V := facets (pathIndependentOn vertices)

theorem mem_pathIndependentOn (vertices : List V) (s : Finset V) :
    s ∈ pathIndependentOn vertices ↔ s ⊆ vertices.toFinset ∧
      ∀ e ∈ pathEdges vertices, ¬ e ⊆ s := by
  simp [pathIndependentOn, pathIndependent]

theorem pathIndependentOn_lower {vertices : List V} {s t : Finset V}
    (hs : s ∈ pathIndependentOn vertices) (hts : t ⊆ s) :
    t ∈ pathIndependentOn vertices := by
  obtain ⟨hW, hE⟩ := (mem_pathIndependentOn _ _).mp hs
  exact (mem_pathIndependentOn _ _).mpr
    ⟨hts.trans hW, fun e he ht => hE e he (ht.trans hts)⟩

@[simp] theorem mem_pathFamily (vertices : List V) (s : Finset V) :
    s ∈ pathFamily vertices ↔ s ∈ pathIndependentOn vertices := by
  constructor
  · rintro ⟨t, ht, hst⟩
    exact pathIndependentOn_lower ht hst
  · intro hs
    exact ⟨s, hs, Finset.Subset.refl s⟩

private theorem edges_independent (vertices : List V) (s : Finset V) :
    (∀ e ∈ pathEdges vertices, ¬ e ⊆ s) ↔
      FiniteIndependentPathGreedy.IndependentAlong vertices s := by
  induction vertices using pathEdges.induct with
  | case1 => simp [pathEdges, FiniteIndependentPathGreedy.IndependentAlong]
  | case2 a => simp [pathEdges, FiniteIndependentPathGreedy.IndependentAlong]
  | case3 a b rest ih =>
      simp only [pathEdges, Finset.mem_insert, forall_eq_or_imp,
        FiniteIndependentPathGreedy.IndependentAlong, ← ih]
      have hpair : ({a, b} : Finset V) ⊆ s ↔ a ∈ s ∧ b ∈ s := by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      rw [hpair]
      tauto

/-- Reuse the selected recursive independent family only after identifying
    its support and every literal consecutive edge. -/
theorem pathIndependentOn_eq_paths (vertices : List V) (hd : vertices.Nodup) :
    pathIndependentOn vertices = FiniteIndependentPathGreedy.paths vertices := by
  ext s
  rw [mem_pathIndependentOn, edges_independent,
    FiniteIndependentPathGreedy.mem_paths_iff vertices hd]
  simp only [Finset.subset_iff, List.mem_toFinset]

private theorem paths_cons (a : V) (rest : List V) :
    FiniteIndependentPathGreedy.paths (a :: rest) =
      FiniteIndependentPathGreedy.paths rest ∪
      (FiniteIndependentPathGreedy.paths rest.tail).image (insert a) := by
  cases rest <;> simp [FiniteIndependentPathGreedy.paths]

/-- Exact two-block decomposition. The first two summands are the two faces
    of each first-block pair; the last summand contains the second vertex. -/
theorem pathIndependentOn_step (a b : V) (rest : List V)
    (hd : (a :: b :: rest).Nodup) :
    pathIndependentOn (a :: b :: rest) =
      (pathIndependentOn rest ∪ (pathIndependentOn rest).image (insert a)) ∪
        (pathIndependentOn rest.tail).image (insert b) := by
  have hr := (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2
  rw [pathIndependentOn_eq_paths _ hd, paths_cons a, paths_cons b,
    pathIndependentOn_eq_paths _ hr, pathIndependentOn_eq_paths _ hr.tail]
  simp only [List.tail_cons]
  ac_rfl

private theorem independent_tail_subset (rest : List V) (hd : rest.Nodup) :
    pathIndependentOn rest.tail ⊆ pathIndependentOn rest := by
  cases rest with
  | nil => exact Finset.Subset.refl _
  | cons c tail =>
      change pathIndependentOn tail ⊆ pathIndependentOn (c :: tail)
      rw [pathIndependentOn_eq_paths _ hd,
        pathIndependentOn_eq_paths _ (List.nodup_cons.mp hd).2, paths_cons]
      exact Finset.subset_union_left

private theorem avoids {vertices : List V} {s : Finset V} {x : V}
    (hs : s ∈ pathIndependentOn vertices) (hx : x ∉ vertices) : x ∉ s := by
  intro h
  exact hx (List.mem_toFinset.mp (((mem_pathIndependentOn _ _).mp hs).1 h))

/- Cardinality is the primary key. The finite tie key is used only to make a
   total order; no later proof mistakes an arbitrary toList for sorted labels. -/
def faceBefore (a b : Finset V) : Prop :=
  a.card < b.card ∨ a.card = b.card ∧
    (Fintype.equivFin (Finset V) a).val ≤ (Fintype.equivFin (Finset V) b).val
private instance faceBeforeTotal : Std.Total (faceBefore (V := V)) :=
  ⟨by
    intro a b
    unfold faceBefore
    by_cases h : a.card < b.card
    · exact Or.inl (Or.inl h)
    by_cases h' : b.card < a.card
    · exact Or.inr (Or.inl h')
    have hc : a.card = b.card := by omega
    rcases le_total (Fintype.equivFin (Finset V) a).val
      (Fintype.equivFin (Finset V) b).val with hab | hba
    · exact Or.inl (Or.inr ⟨hc, hab⟩)
    · exact Or.inr (Or.inr ⟨hc.symm, hba⟩)⟩
private instance faceBeforeTrans : IsTrans (Finset V) (faceBefore (V := V)) :=
  ⟨by
    intro a b c hab hbc
    unfold faceBefore at hab hbc ⊢
    rcases hab with hab | ⟨hab, hab'⟩ <;>
      rcases hbc with hbc | ⟨hbc, hbc'⟩
    · exact Or.inl (lt_trans hab hbc)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, le_trans hab' hbc'⟩⟩

def orderedFaces (F : Finset (Finset V)) : List (Finset V) :=
  by
    classical
    exact F.toList.mergeSort (fun a b => faceBefore a b)
theorem orderedFaces_spec (F : Finset (Finset V)) :
    (orderedFaces F).Nodup ∧ (orderedFaces F).toFinset = F ∧
      (orderedFaces F).Pairwise (fun a b => a.card ≤ b.card) := by
  classical
  have hp : List.Perm (orderedFaces F) F.toList := List.mergeSort_perm _ _
  refine ⟨hp.nodup_iff.mpr F.nodup_toList, ?_, ?_⟩
  · ext s
    simpa only [List.mem_toFinset, Finset.mem_toList] using hp.mem_iff
  · exact (List.pairwise_mergeSort' (faceBefore (V := V)) F.toList).imp
      (by intro a b h; unfold faceBefore at h; rcases h with h | ⟨h, _⟩ <;> omega)

@[simp] theorem mem_orderedFaces (F : Finset (Finset V)) (s : Finset V) :
    s ∈ orderedFaces F ↔ s ∈ F := by
  have h := (orderedFaces_spec F).2.1
  have hm : s ∈ (orderedFaces F).toFinset ↔ s ∈ F := by rw [h]
  simpa only [List.mem_toFinset] using hm

/-- Apex remains a vertex; adjoining changes each face by the same insertion. -/
def adjoinSymbol (v : V) : Symbol V → Symbol V
  | .pair L a => .pair (insert v L) a
  | .critical S => .critical (insert v S)

@[simp] theorem adjoinSymbol_pair (v a : V) (L : Finset V) :
    adjoinSymbol v (.pair L a) = .pair (insert v L) a := rfl
@[simp] theorem adjoinSymbol_critical (v : V) (S : Finset V) :
    adjoinSymbol v (.critical S) = .critical (insert v S) := rfl

theorem adjoinSymbol_faces (v : V) (q : Symbol V) :
    (adjoinSymbol v q).faces = q.faces.image (insert v) := by
  cases q <;> ext s <;>
    simp [adjoinSymbol, FiniteProtectedDualWord.Symbol.faces, Finset.insert_comm]

theorem mem_adjoinSymbol_faces (v : V) (q : Symbol V) (s : Finset V) :
    s ∈ (adjoinSymbol v q).faces ↔ ∃ t ∈ q.faces, insert v t = s := by
  rw [adjoinSymbol_faces, Finset.mem_image]

def pathWord : List V → List (Symbol V)
  | [] => [.critical ∅]
  | [v] => [.pair ∅ v]
  | a :: b :: rest =>
      (orderedFaces (pathIndependentOn rest)).map (fun T => .pair T a) ++
        (pathWord rest.tail).map (adjoinSymbol b)
termination_by vertices => vertices.length
decreasing_by
  cases rest <;> simp_all <;> omega

def pathCritical (vertices : List V) : Finset (Finset V) :=
  criticalFaces (pathWord vertices)

@[simp] theorem pathWord_nil : pathWord ([] : List V) = [.critical ∅] := by rw [pathWord]
@[simp] theorem pathWord_single (v : V) : pathWord [v] = [.pair ∅ v] := by rw [pathWord]
@[simp] theorem pathWord_cons_cons (a b : V) (rest : List V) :
    pathWord (a :: b :: rest) =
      (orderedFaces (pathIndependentOn rest)).map (fun T => .pair T a) ++
        (pathWord rest.tail).map (adjoinSymbol b) := by rw [pathWord]
@[simp] theorem pathWord_critical (vertices : List V) :
    criticalFaces (pathWord vertices) = pathCritical vertices := rfl

/- Occurrence lemmas below retain the actual arbitrary prefix. They do not
   replace global dependency by membership in the complete word. -/
private theorem split_append {α : Type*} (xs ys p : List α) (z : α) (s : List α)
    (h : xs ++ ys = p ++ z :: s) :
    (∃ a b, xs = a ++ z :: b ∧ p = a ∧ s = b ++ ys) ∨
    (∃ a b, ys = a ++ z :: b ∧ p = xs ++ a ∧ s = b) := by
  induction xs generalizing p with
  | nil => exact Or.inr ⟨p, s, by simpa using h, rfl, rfl⟩
  | cons x xs ih =>
      cases p with
      | nil =>
          have hh := List.cons.inj h
          exact Or.inl ⟨[], xs, by simp [hh.1], rfl, hh.2.symm⟩
      | cons y p =>
          have hh := List.cons.inj h
          rcases ih p hh.2 with ⟨a, b, hx, hp, hs⟩ | ⟨a, b, hy, hp, hs⟩
          · exact Or.inl ⟨x :: a, b, by simp [hx, hh.1], by simp [hp, hh.1], hs⟩
          · exact Or.inr ⟨a, b, hy, by simp [hp, hh.1], hs⟩

private theorem split_map {α β : Type*} (f : α → β) (xs : List α)
    (p : List β) (z : β) (s : List β) (h : xs.map f = p ++ z :: s) :
    ∃ a x b, xs = a ++ x :: b ∧ p = a.map f ∧ z = f x ∧ s = b.map f := by
  induction p generalizing xs with
  | nil =>
      cases xs with
      | nil => simp at h
      | cons x xs =>
          have hh := List.cons.inj h
          exact ⟨[], x, xs, rfl, rfl, hh.1.symm, hh.2.symm⟩
  | cons y p ih =>
      cases xs with
      | nil => simp at h
      | cons x xs =>
          have hh := List.cons.inj h
          obtain ⟨a, u, b, hx, hp, hz, hs⟩ := ih xs hh.2
          exact ⟨x :: a, u, b, by simp [hx], by simp [hp, hh.1], hz, hs⟩

private theorem singleton_split {α : Type*} (x z : α) (p s : List α)
    (h : [x] = p ++ z :: s) : p = [] ∧ z = x ∧ s = [] := by
  have hl := congrArg List.length h
  simp only [List.length_singleton, List.length_append, List.length_cons, List.length_nil] at hl
  have hp : p.length = 0 := by omega
  have hs : s.length = 0 := by omega
  have hp' := List.length_eq_zero_iff.mp hp
  have hs' := List.length_eq_zero_iff.mp hs
  subst p; subst s
  exact ⟨rfl, (List.cons.inj h).1.symm, rfl⟩

private theorem smaller_in_prefix {xs p s : List (Finset V)} {A B : Finset V}
    (ho : xs.Pairwise (fun a b => a.card ≤ b.card))
    (h : xs = p ++ B :: s) (hA : A ∈ xs) (hlt : A.card < B.card) : A ∈ p := by
  rw [h] at hA ho
  rcases List.mem_append.mp hA with hp | ht
  · exact hp
  · rcases List.mem_cons.mp ht with he | ht
    · subst A; omega
    · have hBA := (List.pairwise_cons.mp (List.pairwise_append.mp ho).2.1).1 A ht
      omega

private theorem pairwise_map_on {α β : Type*} (f : α → β)
    {R : α → α → Prop} {Q : β → β → Prop} {xs : List α}
    (h : xs.Pairwise R)
    (hf : ∀ x ∈ xs, ∀ y ∈ xs, R x y → Q (f x) (f y)) :
    (xs.map f).Pairwise Q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      obtain ⟨hh, ht⟩ := List.pairwise_cons.mp h
      apply List.pairwise_cons.mpr
      constructor
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        exact hf x (by simp) z (by simp [hz]) (hh z hz)
      · exact ih ht (fun a ha b hb hab => hf a (by simp [ha]) b (by simp [hb]) hab)

private theorem index_faces (xs : List (Symbol V)) (s : Finset V) :
    (∃ i : Fin xs.length, s ∈ (xs.get i).faces) ↔ ∃ q ∈ xs, s ∈ q.faces := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨xs.get i, List.mem_iff_get.mpr ⟨i, rfl⟩, hi⟩
  · rintro ⟨q, hq, hs⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
    exact ⟨i, by simpa only [hi] using hs⟩

private theorem word_face {W : Finset V} {K : Family V} (d : Word W K)
    {q : Symbol V} (hq : q ∈ d.word) {s : Finset V} (hs : s ∈ q.faces) : s ∈ K := by
  cases q with
  | critical S =>
      have he : s = S := by simpa [FiniteProtectedDualWord.Symbol.faces] using hs
      subst s; exact d.critical_data S hq
  | pair L a =>
      rcases (show s = L ∨ s = insert a L by
        simpa [FiniteProtectedDualWord.Symbol.faces] using hs) with rfl | rfl
      · exact (d.pair_data s a hq).1
      · exact (d.pair_data L a hq).2.1

private theorem insert_injective_on {b : V} {A B : Finset V}
    (hA : b ∉ A) (hB : b ∉ B) (h : insert b A = insert b B) : A = B := by
  have hh := congrArg (fun t : Finset V => t.erase b) h
  simpa only [Finset.erase_insert hA, Finset.erase_insert hB] using hh

private theorem pair_face_erase {a : V} {A S : Finset V} (ha : a ∉ A)
    (hS : S ∈ (Symbol.pair A a).faces) : S.erase a = A := by
  rcases (show S = A ∨ S = insert a A by
    simpa [FiniteProtectedDualWord.Symbol.faces] using hS) with rfl | rfl
  · exact Finset.erase_eq_of_notMem ha
  · exact Finset.erase_insert ha

private theorem first_disjoint {a : V} {A B : Finset V}
    (ha : a ∉ A) (hb : a ∉ B) (hAB : A ≠ B) :
    Disjoint (Symbol.pair A a).faces (Symbol.pair B a).faces := by
  apply Finset.disjoint_left.mpr
  intro S hSA hSB
  exact hAB ((pair_face_erase ha hSA).symm.trans (pair_face_erase hb hSB))

private theorem first_partition (a : V) (xs : List (Finset V))
    (hn : xs.Nodup) (ha : ∀ A ∈ xs, a ∉ A) :
    (xs.map (fun A => Symbol.pair A a)).Pairwise
      (fun q r => Disjoint q.faces r.faces) := by
  induction xs with
  | nil => simp
  | cons A tail ih =>
      obtain ⟨hAn, htail⟩ := List.nodup_cons.mp hn
      apply List.pairwise_cons.mpr
      constructor
      · intro q hq
        obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hq
        exact first_disjoint (ha A (by simp)) (ha B (by simp [hB]))
          (fun he => hAn (he.symm ▸ hB))
      · exact ih htail (fun B hB => ha B (by simp [hB]))

private theorem erase_dependency {a : V} {A T : Finset V}
    (hT : T ⊂ insert a A) (hne : T ≠ A) : T.erase a ⊂ A := by
  have hsub : T.erase a ⊆ A := by
    intro x hx
    have hx' := Finset.mem_erase.mp hx
    exact (Finset.mem_insert.mp (hT.subset hx'.2)).resolve_left hx'.1
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro he
  by_cases hat : a ∈ T
  · have ht : T = insert a A := by rw [← he, Finset.insert_erase hat]
    exact hT.ne ht
  · exact hne ((Finset.erase_eq_of_notMem hat).symm.trans he)

private theorem erase_lift_dependency {b : V} {U T : Finset V}
    (hT : T ⊂ insert b U) (hbT : b ∈ T) : T.erase b ⊂ U := by
  have hs : T.erase b ⊆ U := by
    intro x hx
    have hx' := Finset.mem_erase.mp hx
    exact (Finset.mem_insert.mp (hT.subset hx'.2)).resolve_left hx'.1
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, ?_⟩
  intro he
  exact hT.ne (by rw [← he, Finset.insert_erase hbT])

private def emptyPathWord : Word (∅ : Finset V) (pathFamily []) where
  word := [.critical ∅]
  supported := by intro s hs; simpa [mem_pathFamily, pathIndependentOn, pathIndependent, pathEdges] using hs
  pair_data := by intro L v h; simp at h
  critical_data := by
    intro S h
    have he : S = ∅ := by simpa using h
    subst S
    simp [mem_pathFamily, pathIndependentOn, pathIndependent, pathEdges]
  partition := by simp
  covers := by
    intro s
    rw [index_faces]
    simp [mem_pathFamily, pathIndependentOn, pathIndependent, pathEdges,
      FiniteProtectedDualWord.Symbol.faces]
  pair_dependency := by
    intro p s L v h
    have hh := (singleton_split _ _ _ _ h).2.1
    cases hh
  critical_dependency := by
    intro p s S h T hT
    have hh := (singleton_split _ _ _ _ h).2.1
    injection hh with hS
    subst S
    exact (hT.ne (Finset.eq_empty_iff_forall_notMem.mpr
      (fun x hx => Finset.notMem_empty x (hT.subset hx)))).elim

private def singlePathWord (a : V) : Word ({a} : Finset V) (pathFamily [a]) where
  word := [.pair ∅ a]
  supported := by
    intro s hs
    exact (mem_pathIndependentOn _ _).mp ((mem_pathFamily _ _).mp hs) |>.1
  pair_data := by
    intro L v h
    have he : Symbol.pair L v = Symbol.pair ∅ a := by simpa using h
    injection he with hL hv
    subst L
    subst v
    simp [mem_pathFamily, pathIndependentOn, pathIndependent, pathEdges]
  critical_data := by intro S h; simp at h
  partition := by simp
  covers := by
    intro s
    rw [index_faces]
    simp only [List.mem_singleton, exists_eq_left]
    change s ∈ pathFamily [a] ↔ s ∈ (Symbol.pair ∅ a).faces
    have hI : s ∈ pathFamily [a] ↔ s ⊆ ({a} : Finset V) := by
      simp [mem_pathFamily, mem_pathIndependentOn, pathEdges]
    rw [hI]
    constructor
    · intro hs
      by_cases ha : a ∈ s
      · have he : s = {a} := Finset.Subset.antisymm hs
          (Finset.singleton_subset_iff.mpr ha)
        simp [he, FiniteProtectedDualWord.Symbol.faces]
      · have he : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
          intro x hx
          have hx' : x = a := by simpa using hs hx
          exact ha (hx' ▸ hx))
        simp [he, FiniteProtectedDualWord.Symbol.faces]
    · intro hs
      rcases (show s = ∅ ∨ s = {a} by
        simpa [FiniteProtectedDualWord.Symbol.faces] using hs) with rfl | rfl <;> simp
  pair_dependency := by
    intro p s L v h T hT hne
    have he := (singleton_split _ _ _ _ h).2.1
    injection he with hL hv
    subst L
    subst v
    have hTa : a ∉ T := by
      intro ha
      have hEq : T = {a} := Finset.Subset.antisymm hT.subset
        (Finset.singleton_subset_iff.mpr ha)
      exact hT.ne (by simpa using hEq)
    exact (hne (Finset.eq_empty_iff_forall_notMem.mpr (by
      intro x hx
      have hx' : x = a := by simpa using hT.subset hx
      exact hTa (hx' ▸ hx)))).elim
  critical_dependency := by
    intro p s S h
    have he := (singleton_split _ _ _ _ h).2.1
    cases he

/- The only Word input is the induction hypothesis on the strictly shorter
   fourth-vertex suffix. Every field of the larger word is proved below. -/
private def pathWordStep (a b : V) (rest : List V)
    (hd : (a :: b :: rest).Nodup)
    (d : Word rest.tail.toFinset (pathFamily rest.tail)) :
    Word (a :: b :: rest).toFinset (pathFamily (a :: b :: rest)) := by
  let F := pathIndependentOn rest
  let xs := orderedFaces F
  let first := xs.map (fun T => Symbol.pair T a)
  let second := d.word.map (adjoinSymbol b)
  have hr : rest.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2
  have ha : a ∉ b :: rest := (List.nodup_cons.mp hd).1
  have hb : b ∉ rest := (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1
  have hab : a ≠ b := fun h => ha (by simp [h])
  have haR : a ∉ rest := fun h => ha (by simp [h])
  have haF : ∀ T ∈ F, a ∉ T := fun T hT => avoids hT haR
  have hbF : ∀ T ∈ F, b ∉ T := fun T hT => avoids hT hb
  have hGF : pathIndependentOn rest.tail ⊆ F := independent_tail_subset rest hr
  have hxs : ∀ T, T ∈ xs ↔ T ∈ F := fun T => mem_orderedFaces F T
  have hfirst : ∀ T ∈ F, Symbol.pair T a ∈ first := by
    intro T hT
    exact List.mem_map.mpr ⟨T, (hxs T).mpr hT, rfl⟩
  have hvalid : ∀ s, s ∈ pathIndependentOn (a :: b :: rest) ↔
      (s ∈ F ∨ ∃ T ∈ F, insert a T = s) ∨
        ∃ T ∈ pathIndependentOn rest.tail, insert b T = s := by
    intro s
    rw [pathIndependentOn_step a b rest hd]
    simpa only [F, Finset.mem_union, Finset.mem_image]
  have hfirstvalid : ∀ T ∈ F,
      T ∈ pathFamily (a :: b :: rest) ∧ insert a T ∈ pathFamily (a :: b :: rest) := by
    intro T hT
    exact ⟨(mem_pathFamily _ _).mpr ((hvalid T).mpr (Or.inl (Or.inl hT))),
      (mem_pathFamily _ _).mpr ((hvalid _).mpr (Or.inl (Or.inr ⟨T, hT, rfl⟩)))⟩
  have hliftvalid : ∀ T ∈ pathFamily rest.tail,
      insert b T ∈ pathFamily (a :: b :: rest) := by
    intro T hT
    exact (mem_pathFamily _ _).mpr ((hvalid _).mpr
      (Or.inr ⟨T, (mem_pathFamily _ _).mp hT, rfl⟩))
  have hfaceG : ∀ q ∈ d.word, ∀ T ∈ q.faces, T ∈ pathIndependentOn rest.tail := by
    intro q hq T hT
    exact (mem_pathFamily _ _).mp (word_face d hq hT)
  have havoidG : ∀ q ∈ d.word, ∀ T ∈ q.faces, b ∉ T := by
    intro q hq T hT
    exact hbF T (hGF (hfaceG q hq T hT))
  have hfirstFaces : ∀ q ∈ first, ∀ T ∈ q.faces, b ∉ T := by
    intro q hq T hT
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hq
    have hbA := hbF A ((hxs A).mp hA)
    rcases (show T = A ∨ T = insert a A by
      simpa [FiniteProtectedDualWord.Symbol.faces] using hT) with rfl | rfl
    · exact hbA
    · simpa [Ne.symm hab] using hbA
  have hcoverFirst : ∀ T ∈ F, ∃ q ∈ first, T ∈ q.faces := by
    intro T hT
    exact ⟨Symbol.pair T a, hfirst T hT, by simp [FiniteProtectedDualWord.Symbol.faces]⟩
  refine {
    word := first ++ second
    supported := ?_
    pair_data := ?_
    critical_data := ?_
    partition := ?_
    covers := ?_
    pair_dependency := ?_
    critical_dependency := ?_ }
  · intro s hs
    exact (mem_pathIndependentOn _ _).mp ((mem_pathFamily _ _).mp hs) |>.1
  · intro L v hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨T, hT, he⟩ := List.mem_map.mp hp
      have he' : Symbol.pair T a = Symbol.pair L v := he
      injection he' with hL hv
      subst L
      subst v
      have hTF := (hxs T).mp hT
      exact ⟨(hfirstvalid T hTF).1, (hfirstvalid T hTF).2, haF T hTF⟩
    · obtain ⟨q, hq, he⟩ := List.mem_map.mp hp
      cases q with
      | critical S => simp [adjoinSymbol] at he
      | pair A u =>
          have he' : Symbol.pair (insert b A) u = Symbol.pair L v := he
          injection he' with hL hv
          subst L
          subst v
          obtain ⟨hA, hU, hu⟩ := d.pair_data A u hq
          have hbU := hbF _ (hGF ((mem_pathFamily _ _).mp hU))
          have hub : u ≠ b := fun h => hbU (by simp [← h])
          exact ⟨hliftvalid A hA,
            by simpa only [Finset.insert_comm] using hliftvalid (insert u A) hU,
            by simp [hub, hu]⟩
  · intro S hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨T, _, he⟩ := List.mem_map.mp hp
      cases he
    · obtain ⟨q, hq, he⟩ := List.mem_map.mp hp
      cases q with
      | pair A u => simp [adjoinSymbol] at he
      | critical T =>
          have he' : Symbol.critical (insert b T) = Symbol.critical S := he
          injection he' with hs
          subst S
          exact hliftvalid T (d.critical_data T hq)
  · apply List.pairwise_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · exact first_partition a xs (orderedFaces_spec F).1
        (fun A hA => haF A ((hxs A).mp hA))
    · exact pairwise_map_on (adjoinSymbol b) d.partition (by
        intro q hq r hr hqr
        apply Finset.disjoint_left.mpr
        intro T hTq hTr
        obtain ⟨A, hA, hAT⟩ := (mem_adjoinSymbol_faces b q T).mp hTq
        obtain ⟨B, hB, hBT⟩ := (mem_adjoinSymbol_faces b r T).mp hTr
        have he := insert_injective_on (havoidG q hq A hA) (havoidG r hr B hB)
          (hAT.trans hBT.symm)
        exact Finset.disjoint_left.mp hqr hA (he.symm ▸ hB))
    · intro q hq r hr
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
      apply Finset.disjoint_left.mpr
      intro T hTq hTr
      obtain ⟨A, _, hAT⟩ := (mem_adjoinSymbol_faces b u T).mp hTr
      exact hfirstFaces q hq T hTq (hAT ▸ Finset.mem_insert_self b A)
  · intro s
    rw [index_faces, mem_pathFamily, hvalid]
    constructor
    · rintro ((hF | ⟨T, hT, rfl⟩) | ⟨T, hT, rfl⟩)
      · obtain ⟨q, hq, hs⟩ := hcoverFirst s hF
        exact ⟨q, List.mem_append.mpr (Or.inl hq), hs⟩
      · exact ⟨Symbol.pair T a, List.mem_append.mpr (Or.inl (hfirst T hT)),
          by simp [FiniteProtectedDualWord.Symbol.faces]⟩
      · obtain ⟨q, hq, hTq⟩ := (index_faces d.word T).mp
          ((d.covers T).mp ((mem_pathFamily _ _).mpr hT))
        exact ⟨adjoinSymbol b q,
          List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨q, hq, rfl⟩)),
          (mem_adjoinSymbol_faces b q _).mpr ⟨T, hTq, rfl⟩⟩
    · rintro ⟨q, hq, hs⟩
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hq
        have hAF := (hxs A).mp hA
        rcases (show s = A ∨ s = insert a A by
          simpa [FiniteProtectedDualWord.Symbol.faces] using hs) with rfl | rfl
        · exact Or.inl (Or.inl hAF)
        · exact Or.inl (Or.inr ⟨A, hAF, rfl⟩)
      · change q ∈ d.word.map (adjoinSymbol b) at hq
        obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
        obtain ⟨A, hA, rfl⟩ := (mem_adjoinSymbol_faces b q₀ s).mp hs
        exact Or.inr ⟨A, hfaceG q₀ hq₀ A hA, rfl⟩
  · intro p s L v hword T hT hne
    rcases split_append first second p (Symbol.pair L v) s hword with
      ⟨p₁, s₁, h₁, hp, _⟩ | ⟨p₂, s₂, h₂, hp, _⟩
    · obtain ⟨p₀, A, s₀, hx, hpp, he, _⟩ := split_map (fun A => Symbol.pair A a)
        xs p₁ (Symbol.pair L v) s₁ h₁
      have he' : Symbol.pair L v = Symbol.pair A a := he
      injection he' with hL hv
      subst L
      subst v
      have hAxs : A ∈ xs := by rw [hx]; simp
      have hAF := (hxs A).mp hAxs
      have hRA := erase_dependency hT hne
      have hRF : T.erase a ∈ F := pathIndependentOn_lower hAF hRA.subset
      have hRxs : T.erase a ∈ xs := (hxs _).mpr hRF
      have hRp := smaller_in_prefix (orderedFaces_spec F).2.2 hx hRxs
        (Finset.card_lt_card hRA)
      refine ⟨Symbol.pair (T.erase a) a, ?_, ?_⟩
      · rw [hp, hpp]
        exact List.mem_map.mpr ⟨T.erase a, hRp, rfl⟩
      · by_cases hat : a ∈ T
        · have heT := Finset.insert_erase hat
          simp [FiniteProtectedDualWord.Symbol.faces, heT]
        · simp [FiniteProtectedDualWord.Symbol.faces, Finset.erase_eq_of_notMem hat]
    · obtain ⟨p₀, q, s₀, hx, hpp, he, _⟩ := split_map (adjoinSymbol b)
        d.word p₂ (Symbol.pair L v) s₂ h₂
      have hq : q ∈ d.word := by rw [hx]; simp
      cases q with
      | critical S => simp [adjoinSymbol] at he
      | pair A u =>
          have he' : Symbol.pair L v = Symbol.pair (insert b A) u := he
          injection he' with hL hv
          subst L
          subst v
          have hU := (d.pair_data A u hq).2.1
          have hT' : T ⊂ insert b (insert u A) := by
            simpa only [Finset.insert_comm] using hT
          by_cases hbT : b ∈ T
          · have hRT := erase_lift_dependency hT' hbT
            have hRA : T.erase b ≠ A := by
              intro heA
              apply hne
              rw [← heA, Finset.insert_erase hbT]
            obtain ⟨r, hr, hRr⟩ := d.pair_dependency p₀ s₀ A u hx _ hRT hRA
            refine ⟨adjoinSymbol b r, ?_, ?_⟩
            · rw [hp, hpp]
              exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨r, hr, rfl⟩))
            · exact (mem_adjoinSymbol_faces b r T).mpr
                ⟨T.erase b, hRr, Finset.insert_erase hbT⟩
          · have hTU : T ⊆ insert u A := by
              intro x hxT
              have hxb : x ≠ b := fun he => hbT (he ▸ hxT)
              exact (Finset.mem_insert.mp (hT'.subset hxT)).resolve_left hxb
            have hTF : T ∈ F := hGF ((mem_pathFamily _ _).mp
              ((pathFamily rest.tail).lower hTU hU))
            obtain ⟨r, hr, hTr⟩ := hcoverFirst T hTF
            exact ⟨r, by rw [hp]; exact List.mem_append.mpr (Or.inl hr), hTr⟩
  · intro p s S hword T hT
    rcases split_append first second p (Symbol.critical S) s hword with
      ⟨p₁, s₁, h₁, _, _⟩ | ⟨p₂, s₂, h₂, hp, _⟩
    · obtain ⟨_, A, _, _, _, he, _⟩ := split_map (fun A => Symbol.pair A a)
        xs p₁ (Symbol.critical S) s₁ h₁
      cases he
    · obtain ⟨p₀, q, s₀, hx, hpp, he, _⟩ := split_map (adjoinSymbol b)
        d.word p₂ (Symbol.critical S) s₂ h₂
      have hq : q ∈ d.word := by rw [hx]; simp
      cases q with
      | pair A u => simp [adjoinSymbol] at he
      | critical A =>
          have he' : Symbol.critical S = Symbol.critical (insert b A) := he
          injection he' with hs
          subst S
          have hA := d.critical_data A hq
          by_cases hbT : b ∈ T
          · have hRT := erase_lift_dependency hT hbT
            obtain ⟨r, hr, hRr⟩ := d.critical_dependency p₀ s₀ A hx _ hRT
            refine ⟨adjoinSymbol b r, ?_, ?_⟩
            · rw [hp, hpp]
              exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨r, hr, rfl⟩))
            · exact (mem_adjoinSymbol_faces b r T).mpr
                ⟨T.erase b, hRr, Finset.insert_erase hbT⟩
          · have hTA : T ⊆ A := by
              intro x hxT
              have hxb : x ≠ b := fun he => hbT (he ▸ hxT)
              exact (Finset.mem_insert.mp (hT.subset hxT)).resolve_left hxb
            have hTF : T ∈ F := hGF ((mem_pathFamily _ _).mp
              ((pathFamily rest.tail).lower hTA hA))
            obtain ⟨r, hr, hTr⟩ := hcoverFirst T hTF
            exact ⟨r, by rw [hp]; exact List.mem_append.mpr (Or.inl hr), hTr⟩

/-- Actual P03 Word, on arbitrary finite distinct ordered vertices. Recursion
    drops the first three vertices, or all remaining vertices in length two. -/
def pathWordData : (vertices : List V) → vertices.Nodup →
    Word vertices.toFinset (pathFamily vertices)
  | [], _ => emptyPathWord
  | [a], _ => singlePathWord a
  | a :: b :: rest, hd => pathWordStep a b rest hd
      (pathWordData rest.tail
        ((List.nodup_cons.mp (List.nodup_cons.mp hd).2).2.tail))
termination_by vertices _ => vertices.length
decreasing_by
  cases rest <;> simp_all <;> omega

/-- The record's list is the very same public recursive word, not a second
    matching construction. This equality is consumed by the cycle blocks. -/
@[simp] theorem pathWordData_word (vertices : List V) (hd : vertices.Nodup) :
    (pathWordData vertices hd).word = pathWord vertices := by
  induction vertices using pathWord.induct with
  | case1 => simp only [pathWordData, emptyPathWord, pathWord_nil]
  | case2 a => simp only [pathWordData, singlePathWord, pathWord_single]
  | case3 a b rest ih =>
      rw [pathWordData]
      change (orderedFaces (pathIndependentOn rest)).map (fun T => Symbol.pair T a) ++
        (pathWordData rest.tail _).word.map (adjoinSymbol b) = _
      rw [ih, pathWord_cons_cons]

/-- Duplicate labels really invalidate the original arbitrary-list claim:
    [v,v] emits a pair with upper {v}, although its literal edge is {v}. -/
theorem duplicate_path_counterexample (v : V) :
    Symbol.pair ∅ v ∈ pathWord [v, v] ∧
      insert v (∅ : Finset V) ∉ pathFamily [v, v] := by
  constructor
  · simp [pathWord, pathIndependentOn, pathIndependent, pathEdges, orderedFaces]
  · rw [mem_pathFamily, mem_pathIndependentOn]
    intro h
    exact h.2 {v, v} (by simp [pathEdges]) (by simp)

/-- Public source bridge for critical membership; P02's internal lemma is
    private and is deliberately not called through an invented public API. -/
theorem criticalFaces_mem (xs : List (Symbol V)) (S : Finset V) :
    S ∈ criticalFaces xs ↔ Symbol.critical S ∈ xs := by
  induction xs with
  | nil => simp [criticalFaces]
  | cons q xs ih => cases q <;> simp [criticalFaces, ih]

private theorem criticalFaces_append (xs ys : List (Symbol V)) :
    criticalFaces (xs ++ ys) = criticalFaces xs ∪ criticalFaces ys := by
  induction xs with
  | nil => simp [criticalFaces]
  | cons q xs ih => cases q <;> simp [criticalFaces, ih, Finset.insert_union]

private theorem criticalFaces_first (a : V) (xs : List (Finset V)) :
    criticalFaces (xs.map (fun T => Symbol.pair T a)) = ∅ := by
  induction xs with
  | nil => rfl
  | cons T xs ih => simpa only [List.map_cons, criticalFaces] using ih

private theorem criticalFaces_adjoin (a : V) (xs : List (Symbol V)) :
    criticalFaces (xs.map (adjoinSymbol a)) = (criticalFaces xs).image (insert a) := by
  induction xs with
  | nil => simp [criticalFaces]
  | cons q xs ih => cases q <;> simp [criticalFaces, adjoinSymbol, ih]

/-- The actual Word criticals agree with the selected path survivor owner;
    the agreement is proved from the symbol recursion, not from a name. -/
theorem pathWord_critical_eq_selected (vertices : List V) :
    criticalFaces (pathWord vertices) = FiniteIndependentPathGreedy.pathCritical vertices := by
  induction vertices using FiniteIndependentPathGreedy.pathCritical.induct with
  | case1 => simp only [pathWord_nil, criticalFaces, FiniteIndependentPathGreedy.pathCritical, Finset.insert_empty]
  | case2 a => simp only [pathWord_single, criticalFaces, FiniteIndependentPathGreedy.pathCritical]
  | case3 a b =>
      simp only [pathWord, List.tail_nil, criticalFaces_append, criticalFaces_first,
        criticalFaces_adjoin, criticalFaces, Finset.union_empty, Finset.empty_union,
        Finset.image_singleton, Finset.insert_empty, FiniteIndependentPathGreedy.pathCritical]
  | case4 a b c rest ih =>
      simp only [pathWord_cons_cons, List.tail_cons, criticalFaces_append,
        criticalFaces_first, criticalFaces_adjoin, Finset.empty_union, ih,
        FiniteIndependentPathGreedy.pathCritical]

theorem pathWord_critical_formula (vertices : List V) (hd : vertices.Nodup) :
    criticalFaces (pathWord vertices) =
      if vertices.length % 3 = 1 then ∅ else {FiniteIndependentPathGreedy.pathChosen vertices} := by
  rw [pathWord_critical_eq_selected]
  exact (FiniteIndependentPathGreedy.survivors_paths vertices hd).symm.trans
    (FiniteIndependentPathGreedy.survivors_paths_closed vertices hd)

end D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
