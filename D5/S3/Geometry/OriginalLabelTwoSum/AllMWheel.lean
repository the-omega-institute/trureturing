/- GID: D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel
   generality: G
   digest: Literal all-m wheel paths and actual ordered-path Word consumers.

   SOURCE_ONLY_UNCOMPILED. The universal cycle Word, both fillings on their
   full grounds, Gamma iff (including the two obstruction residues), the
   standalone B1 collar with whole/upward/all-critical protection, the consumed
   generic parent compiler, arbitrary markings/physical realizations/all-plane
   supplier, and kernel/native/Reg/gates/remote delivery remain obligations.
   No partial source constructor below is an acceptance claim for that goal.
   NC_W(G)=I(G)^*W and A0^*Z=I(P(4,...,m-1)) retain all original ghosts.
   The previous invalid cycleWordData/Contract/Filling/Gamma proof attempts
   are not exported as proved declarations. Their exact frozen owner remains
   immutable, and the result inventory names every removed attempted API.
-/
import D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.PathWord
import D5.S3.Geometry.OriginalLabelTwoSum.WheelSupplier
import D5.S3.Geometry.OriginalLabelTwoSum.RowIteration

noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
open FiniteProtectedDualWord OriginalLabelTwoSum

abbrev Label (m : Nat) := Fin (m + 1)
def label (m : Nat) (i : Fin m) : Label m := ⟨i.val + 1, by omega⟩
def ground (m : Nat) : Finset (Label m) := (Finset.univ : Finset (Label m)).erase 0
def firstLabel (m : Nat) (hm : 3 ≤ m) : Label m := ⟨1, by omega⟩
def secondLabel (m : Nat) (hm : 3 ≤ m) : Label m := ⟨2, by omega⟩
def lastLabel (m : Nat) : Label m := ⟨m, by omega⟩

def rimIndex (m : Nat) (hm : 0 < m) (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩
def rimEdge (m : Nat) (hm : 0 < m) (i : Fin m) : Finset (Label m) :=
  {label m i, label m (rimIndex m hm i)}
def rimRows (m : Nat) (hm : 0 < m) : Rows (Label m) where
  ground := ground m
  chords := Fin m
  row := rimEdge m hm
  row_supported := by
    intro i x hx
    simp only [rimEdge, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [ground, label]
def wheelRoot (m : Nat) (hm : 0 < m) : Family (Label m) := (rimRows m hm).root
def interfaceRow (m : Nat) (hm : 3 ≤ m) : Fin m := ⟨0, by omega⟩
def pathRoot (m : Nat) (hm : 3 ≤ m) : Family (Label m) :=
  ((rimRows m (by omega)).without (interfaceRow m hm)).root
def rim (m : Nat) (hm : 3 ≤ m) : Finset (Label m) :=
  {firstLabel m hm, secondLabel m hm}
def tailGround (m : Nat) (hm : 3 ≤ m) : Finset (Label m) := ground m \ rim m hm
def A0 (m : Nat) (hm : 3 ≤ m) : Family (Label m) := restrict (tailGround m hm) (pathRoot m hm)
def A1 (m : Nat) (hm : 3 ≤ m) : Family (Label m) :=
  pathRoot m hm ⊔ delta (tailGround m hm)

def starDualCarrier {V : Type*} [DecidableEq V] (W : Finset V) (K : Family V) :
    Set (Finset V) := {s | s ⊆ W ∧ W \ s ∉ K}
def dualIdentity {V : Type*} [DecidableEq V] (W : Finset V) (K L : Family V) : Prop :=
  ∀ s, s ∈ starDualCarrier W K ↔ s ∈ L

/- The bounded increasing segment has its order in its definition. Unlike
   Finset.toList, its first and last vertices are numerical endpoints. -/
def labelInterval (m lo : Nat) : (n : Nat) → lo + n ≤ m + 1 → List (Label m)
  | 0, _ => []
  | n + 1, h => ⟨lo, by omega⟩ :: labelInterval m (lo + 1) n (by omega)

@[simp] theorem labelInterval_length (m lo n : Nat) (h : lo + n ≤ m + 1) :
    (labelInterval m lo n h).length = n := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih => simp only [labelInterval, List.length_cons, ih]

theorem mem_labelInterval (m lo n : Nat) (h : lo + n ≤ m + 1) (x : Label m) :
    x ∈ labelInterval m lo n h ↔ lo ≤ x.val ∧ x.val < lo + n := by
  induction n generalizing lo with
  | zero => simp [labelInterval]
  | succ n ih =>
      simp only [labelInterval, List.mem_cons, ih]
      constructor
      · rintro (he | ⟨hl, hu⟩)
        · have hv := congrArg Fin.val he
          dsimp at hv
          omega
        · omega
      · rintro ⟨hl, hu⟩
        by_cases he : x.val = lo
        · exact Or.inl (Fin.ext he)
        · exact Or.inr ⟨by omega, by omega⟩

theorem labelInterval_nodup (m lo n : Nat) (h : lo + n ≤ m + 1) :
    (labelInterval m lo n h).Nodup := by
  induction n generalizing lo with
  | zero => simp [labelInterval]
  | succ n ih =>
      apply List.nodup_cons.mpr
      exact ⟨by rw [mem_labelInterval]; dsimp; omega, ih (lo + 1) (by omega)⟩

/-- Every edge and both of its actual endpoints are identified. The statement
    includes empty and singleton segments, with no fabricated endpoint. -/
set_option maxHeartbeats 1600000 in
theorem labelInterval_edges (m lo n : Nat) (h : lo + n ≤ m + 1)
    (e : Finset (Label m)) :
    e ∈ pathEdges (labelInterval m lo n h) ↔
      ∃ x y : Label m, lo ≤ x.val ∧ y.val = x.val + 1 ∧
        y.val < lo + n ∧ e = {x, y} := by
  induction n generalizing lo with
  | zero =>
      simp only [labelInterval, pathEdges, Finset.notMem_empty, false_iff]
      rintro ⟨x, y, hx, hy, hu, _⟩
      omega
  | succ n ih =>
      cases n with
      | zero =>
          simp only [labelInterval, pathEdges, Finset.notMem_empty, false_iff]
          rintro ⟨x, y, hx, hy, hu, _⟩
          omega
      | succ n =>
          change e ∈ insert {⟨lo, by omega⟩, ⟨lo + 1, by omega⟩}
            (pathEdges (labelInterval m (lo + 1) (n + 1) (by omega))) ↔ _
          rw [Finset.mem_insert, ih]
          constructor
          · rintro (he | ⟨x, y, hx, hy, hu, he⟩)
            · exact ⟨⟨lo, by omega⟩, ⟨lo + 1, by omega⟩,
                by simp, by simp, by dsimp; omega, he⟩
            · exact ⟨x, y, by omega, hy, by omega, he⟩
          · rintro ⟨x, y, hx, hy, hu, he⟩
            by_cases hxl : x.val = lo
            · left
              have hx' : x = (⟨lo, by omega⟩ : Label m) := Fin.ext hxl
              have hy' : y = (⟨lo + 1, by omega⟩ : Label m) := Fin.ext (by omega)
              simpa only [hx', hy'] using he
            · exact Or.inr ⟨x, y, by omega, hy, by omega, he⟩

private theorem interval_snoc_edges (m lo n : Nat) (h : lo + n ≤ m + 1)
    (hn : 0 < n) (z : Label m) :
    pathEdges (labelInterval m lo n h ++ [z]) =
      pathEdges (labelInterval m lo n h) ∪ {{⟨lo + n - 1, by omega⟩, z}} := by
  induction n generalizing lo with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [labelInterval, pathEdges]
      | succ n =>
          change insert {⟨lo, by omega⟩, ⟨lo + 1, by omega⟩}
            (pathEdges (labelInterval m (lo + 1) (n + 1) (by omega) ++ [z])) = _
          rw [ih (lo + 1) (by omega) (by omega)]
          have he : lo + (n + 1 + 1) - 1 = (lo + 1) + (n + 1) - 1 := by omega
          simp only [labelInterval, pathEdges, he, Finset.insert_union]

/- Canonical paths, including the m=3 and m=4 empty tails. -/
def pathRootPath (m : Nat) (hm : 3 ≤ m) : List (Label m) :=
  labelInterval m 2 (m - 1) (by omega) ++ [firstLabel m hm]
def cyclePath (m : Nat) (hm : 3 ≤ m) : List (Label m) :=
  labelInterval m 3 (m - 3) (by omega)
def cyclePathTail (m : Nat) (hm : 3 ≤ m) : List (Label m) :=
  labelInterval m 4 (m - 4) (by omega)
def cyclePathLast (m : Nat) (hm : 3 ≤ m) : List (Label m) :=
  labelInterval m 2 (m - 3) (by omega)

@[simp] theorem pathRootPath_length (m : Nat) (hm : 3 ≤ m) :
    (pathRootPath m hm).length = m := by simp [pathRootPath]; omega
@[simp] theorem cyclePath_length (m : Nat) (hm : 3 ≤ m) :
    (cyclePath m hm).length = m - 3 := labelInterval_length _ _ _ _
@[simp] theorem cyclePathTail_length (m : Nat) (hm : 3 ≤ m) :
    (cyclePathTail m hm).length = m - 4 := labelInterval_length _ _ _ _
@[simp] theorem cyclePathLast_length (m : Nat) (hm : 3 ≤ m) :
    (cyclePathLast m hm).length = m - 3 := labelInterval_length _ _ _ _

private theorem nodup_snoc {α : Type*} [DecidableEq α] (xs : List α) (z : α)
    (hx : xs.Nodup) (hz : z ∉ xs) : (xs ++ [z]).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      obtain ⟨hxn, hxs⟩ := List.nodup_cons.mp hx
      apply List.nodup_cons.mpr
      constructor
      · intro h
        rcases List.mem_append.mp h with h | h
        · exact hxn h
        · have he : x = z := by simpa using h
          exact hz (by simp [he])
      · exact ih hxs (fun h => hz (by simp [h]))

theorem pathRootPath_nodup (m : Nat) (hm : 3 ≤ m) : (pathRootPath m hm).Nodup := by
  apply nodup_snoc _ _ (labelInterval_nodup _ _ _ _)
  rw [mem_labelInterval]
  simp only [firstLabel]
  omega

theorem cyclePath_nodup (m : Nat) (hm : 3 ≤ m) : (cyclePath m hm).Nodup :=
  labelInterval_nodup _ _ _ _
theorem cyclePathTail_nodup (m : Nat) (hm : 3 ≤ m) : (cyclePathTail m hm).Nodup :=
  labelInterval_nodup _ _ _ _
theorem cyclePathLast_nodup (m : Nat) (hm : 3 ≤ m) : (cyclePathLast m hm).Nodup :=
  labelInterval_nodup _ _ _ _

@[simp] theorem pathRootPath_vertices (m : Nat) (hm : 3 ≤ m) :
    (pathRootPath m hm).toFinset = ground m := by
  ext x
  simp only [pathRootPath, List.mem_toFinset, List.mem_append, mem_labelInterval,
    List.mem_singleton, ground, Finset.mem_erase, Finset.mem_univ, and_true]
  have hx := x.isLt
  have hz : x = 0 ↔ x.val = 0 := Fin.ext_iff
  have hf : x = firstLabel m hm ↔ x.val = 1 := Fin.ext_iff
  simp only [ne_eq, hz, hf]
  omega

@[simp] theorem cyclePath_vertices (m : Nat) (hm : 3 ≤ m) (x : Label m) :
    x ∈ (cyclePath m hm).toFinset ↔ 3 ≤ x.val ∧ x.val < m := by
  simp only [List.mem_toFinset, cyclePath, mem_labelInterval]
  omega
@[simp] theorem cyclePathTail_vertices (m : Nat) (hm : 3 ≤ m) (x : Label m) :
    x ∈ (cyclePathTail m hm).toFinset ↔ 4 ≤ x.val ∧ x.val < m := by
  simp only [List.mem_toFinset, cyclePathTail, mem_labelInterval]
  omega
@[simp] theorem cyclePathLast_vertices (m : Nat) (hm : 3 ≤ m) (x : Label m) :
    x ∈ (cyclePathLast m hm).toFinset ↔ 2 ≤ x.val ∧ x.val + 1 < m := by
  simp only [List.mem_toFinset, cyclePathLast, mem_labelInterval]
  omega

theorem pathRootPath_edges (m : Nat) (hm : 3 ≤ m) (e : Finset (Label m)) :
    e ∈ pathEdges (pathRootPath m hm) ↔
      (∃ x y : Label m, 2 ≤ x.val ∧ y.val = x.val + 1 ∧ y.val ≤ m ∧ e = {x, y}) ∨
        e = {lastLabel m, firstLabel m hm} := by
  unfold pathRootPath
  rw [interval_snoc_edges m 2 (m - 1) (by omega) (by omega),
    Finset.mem_union, labelInterval_edges, Finset.mem_singleton]
  have he : 2 + (m - 1) - 1 = m := by omega
  simp only [he, lastLabel]
  constructor
  · rintro (⟨x, y, hx, hy, hu, hxy⟩ | hlast)
    · exact Or.inl ⟨x, y, hx, hy, by omega, hxy⟩
    · exact Or.inr hlast
  · rintro (⟨x, y, hx, hy, hu, hxy⟩ | hlast)
    · exact Or.inl ⟨x, y, hx, hy, by omega, hxy⟩
    · exact Or.inr hlast

theorem cyclePath_edges (m : Nat) (hm : 3 ≤ m) (e : Finset (Label m)) :
    e ∈ pathEdges (cyclePath m hm) ↔
      ∃ x y : Label m, 3 ≤ x.val ∧ y.val = x.val + 1 ∧ y.val < m ∧ e = {x, y} := by
  rw [cyclePath, labelInterval_edges]
  have he : 3 + (m - 3) = m := by omega
  rw [he]
theorem cyclePathTail_edges (m : Nat) (hm : 3 ≤ m) (e : Finset (Label m)) :
    e ∈ pathEdges (cyclePathTail m hm) ↔
      ∃ x y : Label m, 4 ≤ x.val ∧ y.val = x.val + 1 ∧ y.val < m ∧ e = {x, y} := by
  rw [cyclePathTail, labelInterval_edges]
  by_cases h4 : 4 ≤ m
  · have he : 4 + (m - 4) = m := by omega
    rw [he]
  · have he : m = 3 := by omega
    subst m
    constructor <;> rintro ⟨x, y, hx, hy, hu, he⟩ <;> omega

theorem cyclePathLast_edges (m : Nat) (hm : 3 ≤ m) (e : Finset (Label m)) :
    e ∈ pathEdges (cyclePathLast m hm) ↔
      ∃ x y : Label m, 2 ≤ x.val ∧ y.val = x.val + 1 ∧ y.val + 1 < m ∧ e = {x, y} := by
  rw [cyclePathLast, labelInterval_edges]
  constructor <;> rintro ⟨x, y, hx, hy, hu, he⟩ <;>
    exact ⟨x, y, hx, hy, by omega, he⟩

/-- All canonical distinctness premises are derived from m>=3. -/
def pathRootWordData (m : Nat) (hm : 3 ≤ m) :
    Word (ground m) (pathFamily (pathRootPath m hm)) := by
  rw [← pathRootPath_vertices m hm]
  exact pathWordData _ (pathRootPath_nodup m hm)

def cycleTailWordData (m : Nat) (hm : 3 ≤ m) :
    Word (cyclePathTail m hm).toFinset (pathFamily (cyclePathTail m hm)) :=
  pathWordData _ (cyclePathTail_nodup m hm)
def cycleLastWordData (m : Nat) (hm : 3 ≤ m) :
    Word (cyclePathLast m hm).toFinset (pathFamily (cyclePathLast m hm)) :=
  pathWordData _ (cyclePathLast_nodup m hm)

def cycleEdges (m : Nat) (hm : 3 ≤ m) : Finset (Finset (Label m)) :=
  (Finset.univ : Finset (Fin m)).image (rimEdge m (by omega))
private theorem rimEdge_wrap (m : Nat) (hm : 3 ≤ m) (i : Fin m)
    (hi : i.val + 1 = m) :
    rimEdge m (by omega) i = {lastLabel m, firstLabel m hm} := by
  have hx : label m i = lastLabel m := Fin.ext hi
  have hy : label m (rimIndex m (by omega) i) = firstLabel m hm := by
    apply Fin.ext
    simp [label, rimIndex, firstLabel, hi]
  simp only [rimEdge, hx, hy]

private theorem linear_row_index (m : Nat) (hm : 3 ≤ m) (x y : Label m)
    (hx : 1 ≤ x.val) (hy : y.val = x.val + 1) (hym : y.val ≤ m) :
    ∃ i : Fin m, i.val + 1 = x.val ∧ rimEdge m (by omega) i = {x, y} := by
  let i : Fin m := ⟨x.val - 1, by omega⟩
  have hxi : label m i = x := by apply Fin.ext; dsimp [label, i]; omega
  have his : i.val + 1 < m := by dsimp [i]; omega
  have hyi : label m (rimIndex m (by omega) i) = y := by
    apply Fin.ext
    simp only [label, rimIndex, Nat.mod_eq_of_lt his]
    dsimp [i]
    omega
  exact ⟨i, by dsimp [i]; omega, by simp only [rimEdge, hxi, hyi]⟩

/-- Exact cyclic edges on the original labels, with the wrap edge explicit. -/
theorem cycleEdges_mem (m : Nat) (hm : 3 ≤ m) (e : Finset (Label m)) :
    e ∈ cycleEdges m hm ↔
      (∃ x y : Label m, 1 ≤ x.val ∧ y.val = x.val + 1 ∧ y.val ≤ m ∧ e = {x, y}) ∨
        e = {lastLabel m, firstLabel m hm} := by
  constructor
  · intro he
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
    by_cases hn : i.val + 1 < m
    · left
      refine ⟨label m i, label m (rimIndex m (by omega) i), by simp [label], ?_, ?_, hi.symm⟩
      · simp only [label, rimIndex, Nat.mod_eq_of_lt hn]
      · simp only [label, rimIndex, Nat.mod_eq_of_lt hn]
        omega
    · right
      have hl : i.val + 1 = m := by have := i.isLt; omega
      exact hi.symm.trans (rimEdge_wrap m hm i hl)
  · rintro (⟨x, y, hx, hy, hym, he⟩ | he)
    · obtain ⟨i, _, hi⟩ := linear_row_index m hm x y hx hy hym
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.trans he.symm⟩
    · let i : Fin m := ⟨m - 1, by omega⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _,
        (rimEdge_wrap m hm i (by dsimp [i]; omega)).trans he.symm⟩

/-- Deleting the literal interface row gives exactly the path edge set. -/
theorem pathRootPath_row_edges (m : Nat) (hm : 3 ≤ m) :
    pathEdges (pathRootPath m hm) =
      ((Finset.univ : Finset (Fin m)).erase (interfaceRow m hm)).image
        (rimEdge m (by omega)) := by
  ext e
  rw [pathRootPath_edges]
  constructor
  · rintro (⟨x, y, hx, hy, hym, he⟩ | he)
    · obtain ⟨i, hi, hrow⟩ := linear_row_index m hm x y (by omega) hy hym
      have hin : i ≠ interfaceRow m hm := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [interfaceRow] at hv
        omega
      exact Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hin, Finset.mem_univ _⟩,
        hrow.trans he.symm⟩
    · let i : Fin m := ⟨m - 1, by omega⟩
      have hin : i ≠ interfaceRow m hm := by
        intro heq
        have hv := congrArg Fin.val heq
        dsimp [i, interfaceRow] at hv
        omega
      exact Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hin, Finset.mem_univ _⟩,
        (rimEdge_wrap m hm i (by dsimp [i]; omega)).trans he.symm⟩
  · intro he
    obtain ⟨i, hi, hrow⟩ := Finset.mem_image.mp he
    have hin : i.val ≠ 0 := by
      intro hv
      exact (Finset.mem_erase.mp hi).1 (Fin.ext hv)
    by_cases hn : i.val + 1 < m
    · left
      refine ⟨label m i, label m (rimIndex m (by omega) i), ?_, ?_, ?_, hrow.symm⟩
      · dsimp [label]; omega
      · simp only [label, rimIndex, Nat.mod_eq_of_lt hn]
      · simp only [label, rimIndex, Nat.mod_eq_of_lt hn]; omega
    · right
      have hl : i.val + 1 = m := by have := i.isLt; omega
      exact hrow.symm.trans (rimEdge_wrap m hm i hl)

def cycleIndependentOn (m : Nat) (hm : 3 ≤ m) : Finset (Finset (Label m)) :=
  pathIndependent (ground m) (cycleEdges m hm)
def mapSecond (m : Nat) (hm : 3 ≤ m) : Symbol (Label m) → Symbol (Label m) :=
  adjoinSymbol (secondLabel m hm)
def mapLast (m : Nat) (hm : 3 ≤ m) : Symbol (Label m) → Symbol (Label m) :=
  adjoinSymbol (lastLabel m)

/-- Actual cycle consumer: both recursive blocks use the proved distinct-path
    Word records. Their lists are definitionally mapped through the typed API. -/
def cycleWord (m : Nat) (hm : 3 ≤ m) : List (Symbol (Label m)) :=
  (orderedFaces (pathIndependentOn (cyclePath m hm))).map
      (fun T => .pair T (firstLabel m hm)) ++
    (cycleTailWordData m hm).word.map (mapSecond m hm) ++
    (cycleLastWordData m hm).word.map (mapLast m hm)
def tailWord (m : Nat) (hm : 3 ≤ m) : List (Symbol (Label m)) :=
  (cycleTailWordData m hm).word

@[simp] theorem cycleWord_eq (m : Nat) (hm : 3 ≤ m) :
    cycleWord m hm =
      (orderedFaces (pathIndependentOn (cyclePath m hm))).map
        (fun T => .pair T (firstLabel m hm)) ++
      (pathWord (cyclePathTail m hm)).map (adjoinSymbol (secondLabel m hm)) ++
      (pathWord (cyclePathLast m hm)).map (adjoinSymbol (lastLabel m)) := by
  simp only [cycleWord, cycleTailWordData, cycleLastWordData, pathWordData_word,
    mapSecond, mapLast]
@[simp] theorem tailWord_eq (m : Nat) (hm : 3 ≤ m) :
    tailWord m hm = pathWord (cyclePathTail m hm) := by
  exact pathWordData_word _ _

/- Closed labelled targets are retained as definitions. Their identification
   with cycleWord criticals is still a substantive pending theorem. -/
def labelsCongruent (m r lo : Nat) : Finset (Label m) :=
  (Finset.univ : Finset (Label m)).filter (fun x => lo ≤ x.val ∧ x.val % 3 = r)
def tailCritical (m : Nat) (hm : 3 ≤ m) : Finset (Label m) :=
  if m % 3 = 2 then ∅ else labelsCongruent m 2 5
def cycleCritical (m : Nat) (hm : 3 ≤ m) : Finset (Finset (Label m)) :=
  let y := ground m
  let s₂ := labelsCongruent m 2 2
  let s₃ := labelsCongruent m 0 3
  if m % 3 = 0 then {y \ s₂, y \ s₃}
  else if m % 3 = 1 then {y \ s₂}
  else {y \ insert (lastLabel m) s₃}
def eta0 (m : Nat) (hm : 3 ≤ m) : Finset (Label m) :=
  tailGround m hm \ tailCritical m hm
def eta1 (m : Nat) (hm : 3 ≤ m) : Finset (Label m) := ground m \ labelsCongruent m 2 2
def goodResidue (m : Nat) : Prop := ∃ k, m = 3 * k + 1
def criticalCardProfile (m : Nat) : Nat × Nat × Nat × Nat :=
  if m % 3 = 0 then (1, 2 * (m / 3) - 1, 2, 2 * (m / 3))
  else if m % 3 = 1 then (1, 2 * (m / 3), 1, 2 * (m / 3) + 1)
  else (0, 0, 1, 2 * (m / 3) + 1)

/-- A real good-residue consequence of the actual path word. This is the
    no-critical premise for P02, not a claimed Gamma endpoint or iff theorem. -/
theorem pathRootPath_noCritical (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :
    ∀ q ∈ pathWord (pathRootPath m hm), ¬ q.isCritical := by
  obtain ⟨k, hk⟩ := hg
  have hmod : m % 3 = 1 := by omega
  have hc : criticalFaces (pathWord (pathRootPath m hm)) = ∅ := by
    rw [pathWord_critical_formula _ (pathRootPath_nodup m hm), pathRootPath_length,
      if_pos hmod]
  intro q hq hcrit
  cases q with
  | pair L a => exact hcrit
  | critical S =>
      have hs := (criticalFaces_mem _ S).mpr hq
      rw [hc] at hs
      exact Finset.notMem_empty S hs

/- Pending substantive theorem: cycleWordData : Word (ground m)
   (facets (cycleIndependentOn m hm)) with word=cycleWord m hm.
   Still required: three-block independence decomposition and disjointness,
   full coverage, all cross-block dependencies (especially last→second),
   critical maximality or in residue 1 the explicit upward H of P07, proper
   emitted uppers, exact fixed-ground duals and residue critical equations.
   There is no assumed cycle Word, Contract, Sequence, Filling, or Gamma here.

   In particular residue 1 cannot use critical-only protection: the P07 set
   H consists of the critical S AND its specified whole pairs (a_j,b_j).
   A standalone Q1 proof must run on B1 alone and show each current coface.
   The old constant collarUpper and unbounded Nat-label constructor were
   incorrect attempts; they are not exported or registered as source facts.
-/
end D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
