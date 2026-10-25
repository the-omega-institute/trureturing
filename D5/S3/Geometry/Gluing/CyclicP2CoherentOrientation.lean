/- GID: D5/S3/Geometry/Gluing/CyclicP2CoherentOrientation
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/CyclicP2CoherentOrientation
   mirror-E: none(waiver:full-cut-combinatorial-face-coherence)
   anchors: [mathlib/module/Mathlib.Data.List.Nodup, mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Full oriented positional P2 preserves and reflects coherent face choices. -/

import D5.S3.Geometry.Gluing.CyclicP2GeneratedVertices
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

/-!
SOURCE CANDIDATE ONLY. This file has not been elaborated or admitted.
The imported P1 and P2 candidates are also uncompiled source dependencies.

Coherence is a condition on every pair of distinct actual side positions,
including positions in the same face. A singleton edge occurrence imposes no
condition. No surface, exact-two, closedness or nonempty-word premise is used.
The proof uses lists with multiplicity, not sets of words or darts. In particular,
`occurrence_transport` is proved from the literal P2 words and source rotation;
it is not a field assumed of a transformation.
-/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Geometry.Gluing.CyclicP2CoherentOrientation

open scoped List
open D5.S3.Geometry.Gluing.CyclicP1GeneratedVertices
open D5.S3.Geometry.Gluing.CyclicP2GeneratedVertices (retainDart retainWord)
open D5.S3.Geometry.Gluing.CyclicP2GeneratedVertices.FullCut

/-- Both indices are positions. Neither equal faces nor repeated sides are identified. -/
abbrev Occurrence (P : FiniteCyclicPresentation) :=
  Σ f : Face P, Fin (boundary P f).length

/-- The actual signed dart at an actual face/side position. -/
def dart (P : FiniteCyclicPresentation) (o : Occurrence P) :=
  (boundary P o.1).get o.2

/-- The stored sign bit: positive is false and negative is true. -/
def sign {α : Type} : SignedDart α → Bool
  | .pos _ => false
  | .neg _ => true

private def chooseDart {α : Type} (b : Bool) (d : SignedDart α) :=
  if b then flipDart d else d

private def chooseWord {α : Type} (b : Bool) (w : List (SignedDart α)) :=
  w.map (chooseDart b)

/-- Opposite adjusted signs for every distinct pair over the same edge.
For Bool, inequality means precisely that the two signs are opposite. -/
def CoherentChoices (P : FiniteCyclicPresentation) (r : Face P → Bool) : Prop :=
  ∀ o o' : Occurrence P, o ≠ o' → (dart P o).edge = (dart P o').edge →
    Bool.xor (r o.1) (sign (dart P o)) ≠
      Bool.xor (r o'.1) (sign (dart P o'))

/-- Existence of face choices; no choices satisfying this condition are input data. -/
def Coh (P : FiniteCyclicPresentation) : Prop := ∃ r, CoherentChoices P r

@[simp] private theorem choose_edge {α : Type} (b : Bool) (d : SignedDart α) :
    (chooseDart b d).edge = d.edge := by
  cases b <;> cases d <;> rfl

@[simp] private theorem choose_sign {α : Type} (b : Bool) (d : SignedDart α) :
    sign (chooseDart b d) = Bool.xor b (sign d) := by
  cases b <;> cases d <;> rfl

private theorem dart_ext {α : Type} {a b : SignedDart α}
    (he : a.edge = b.edge) (hs : sign a = sign b) : a = b := by
  cases a <;> cases b <;> simp_all [SignedDart.edge, sign]

private def occurrences (P : FiniteCyclicPresentation) : List (Occurrence P) :=
  (List.finRange P.faces.length).flatMap fun f =>
    (List.finRange (boundary P f).length).map fun i => ⟨f, i⟩

private theorem mem_occurrences (P : FiniteCyclicPresentation) (o : Occurrence P) :
    o ∈ occurrences P := by
  apply List.mem_flatMap.mpr
  refine ⟨o.1, by simp, ?_⟩
  exact List.mem_map.mpr ⟨o.2, by simp, rfl⟩

private theorem occurrences_nodup (P : FiniteCyclicPresentation) :
    (occurrences P).Nodup := by
  unfold occurrences
  rw [List.nodup_flatMap]
  constructor
  · intro f _
    apply (List.nodup_finRange _).map
    intro i j h
    cases h
    rfl
  · apply (List.nodup_finRange _).pairwise_of_forall_ne
    intro f _ g _ hfg
    change Disjoint _ _
    rw [List.disjoint_left]
    intro o ho hg
    rcases List.mem_map.mp ho with ⟨i, _, hi⟩
    rcases List.mem_map.mp hg with ⟨j, _, hj⟩
    exact hfg (congrArg Sigma.fst (hi.trans hj.symm))

/-- Enumerating positions and then reading them is exactly the flattened word list.
This equality retains every position, even when several readings are equal. -/
private theorem map_occurrences {α : Type} (P : FiniteCyclicPresentation)
    (v : Face P → SignedDart (Fin P.edgeCount) → α) :
    (occurrences P).map (fun o => v o.1 (dart P o)) =
      (List.ofFn fun f => (boundary P f).map (v f)).flatten := by
  simp only [occurrences, List.map_flatMap, List.map_map, dart]
  rw [List.ofFn_eq_map, ← List.flatMap_def]
  apply List.flatMap_congr
  intro f _
  rw [← List.ofFn_eq_map, List.ofFn_comp', List.ofFn_get]

private def adjustedDarts (P : FiniteCyclicPresentation) (r : Face P → Bool) :=
  (occurrences P).map fun o => chooseDart (r o.1) (dart P o)

private theorem coherent_iff_nodup (P : FiniteCyclicPresentation) (r : Face P → Bool) :
    CoherentChoices P r ↔ (adjustedDarts P r).Nodup := by
  unfold adjustedDarts
  rw [List.nodup_map_iff_inj_on (occurrences_nodup P)]
  constructor
  · intro h o _ o' _ heq
    by_contra hne
    apply h o o' hne
    · simpa only [choose_edge] using congrArg SignedDart.edge heq
    · simpa only [choose_sign] using congrArg sign heq
  · intro h o o' hne he hs
    apply hne
    apply h o (mem_occurrences P o) o' (mem_occurrences P o')
    apply dart_ext
    · simpa only [choose_edge] using he
    · simpa only [choose_sign] using hs

private theorem choose_retain {n : ℕ} (b : Bool) (d : SignedDart (Fin n)) :
    chooseDart b (retainDart d) = retainDart (chooseDart b d) := by
  cases b <;> cases d <;> rfl

private theorem chooseWord_twice {α : Type} (b : Bool) (w : List (SignedDart α)) :
    chooseWord b (chooseWord b w) = w := by
  have hd : ∀ d : SignedDart α, chooseDart b (chooseDart b d) = d := by
    intro d
    cases b <;> cases d <;> rfl
  simpa only [chooseWord, List.map_map, Function.comp_def, hd, List.map_id]

/-- Stored reversal changes signs and reverses positions, hence gives a permutation
of the sign-flipped occurrences, with no loss of multiplicity. -/
private theorem stored_perm {α : Type} (b : Bool) (w : List (SignedDart α)) :
    (P2.storedWord b w).Perm (chooseWord b w) := by
  cases b with
  | false => simpa [P2.storedWord, chooseWord, chooseDart] using List.Perm.refl w
  | true =>
    simpa [P2.storedWord, inverseWord, chooseWord, chooseDart] using
      (List.reverse_perm w).map flipDart

private theorem append_slide {α : Type} (a b c : List α) :
    ((a ++ b) ++ c).Perm ((a ++ c) ++ b) := by
  simpa only [List.append_assoc] using (List.perm_append_comm (l₁ := b) (l₂ := c)).append_left a

/-- Isolate a face by its index, replace only its block, and keep all other blocks.
The erased list is a list of face INDICES, not a list of face words. -/
private theorem family_replace {α : Type} {n : ℕ} (k : Fin n)
    (F G : Fin n → List α) (H E : List α)
    (hother : ∀ i, i ≠ k → G i = F i)
    (hcut : (G k ++ H).Perm (F k ++ E)) :
    ((List.ofFn G).flatten ++ H).Perm ((List.ofFn F).flatten ++ E) := by
  let rest := (List.finRange n).eraseIdx k.val
  have hp : (k :: rest).Perm (List.finRange n) := by
    simpa [rest] using
      (List.getElem_cons_eraseIdx_perm (l := List.finRange n) (n := k.val)
        (by simpa using k.isLt))
  have hn : k ∉ rest := (hp.nodup_iff.mpr (List.nodup_finRange n)).notMem
  have hr : rest.flatMap G = rest.flatMap F := by
    apply List.flatMap_congr
    intro i hi
    exact hother i (fun h => hn (h ▸ hi))
  have hF : (F k ++ rest.flatMap F).Perm (List.ofFn F).flatten := by
    simpa only [List.flatMap_cons, List.ofFn_eq_map, ← List.flatMap_def] using hp.flatMap_right F
  have hG : (G k ++ rest.flatMap G).Perm (List.ofFn G).flatten := by
    simpa only [List.flatMap_cons, List.ofFn_eq_map, ← List.flatMap_def] using hp.flatMap_right G
  calc
    _ ~ (G k ++ rest.flatMap G) ++ H := hG.symm.append_right H
    _ ~ (G k ++ H) ++ rest.flatMap F := by
      rw [hr]
      exact append_slide _ _ _
    _ ~ (F k ++ E) ++ rest.flatMap F := hcut.append_right _
    _ ~ (F k ++ rest.flatMap F) ++ E := append_slide _ _ _
    _ ~ _ := hF.append_right E

/-- The canonical Fin-ofFn identification, not a change in the target face order. -/
private def splitFace (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (f : Fin (P.faces.length + 1)) : Face (P2.split P cut) :=
  Fin.cast (by simp [P2.split]) f

private def parentFace (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (f : Face (P2.split P cut)) : Face P :=
  Fin.lastCases cut.face.face (fun i => i)
    (Fin.cast (by simp [P2.split]) f)

@[simp] private theorem parent_old (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (f : Face P) : parentFace P cut (splitFace P cut f.castSucc) = f := by
  simp [parentFace, splitFace]

@[simp] private theorem parent_last (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    parentFace P cut (splitFace P cut (Fin.last P.faces.length)) = cut.face.face := by
  simp [parentFace, splitFace]

private theorem split_map_occurrences {α : Type} (P : FiniteCyclicPresentation)
    (cut : P2Cut P) (v : Face (P2.split P cut) → SignedDart (Fin (P.edgeCount + 1)) → α) :
    (occurrences (P2.split P cut)).map (fun o => v o.1 (dart (P2.split P cut) o)) =
      (List.ofFn fun f : Face P =>
        (P2.faceWord P cut f.castSucc).map (v (splitFace P cut f.castSucc))).flatten ++
      (P2.rightBoundary P cut).map (v (splitFace P cut (Fin.last P.faces.length))) := by
  rw [map_occurrences]
  have hi : (List.ofFn fun f : Face (P2.split P cut) =>
      (boundary (P2.split P cut) f).map (v f)) =
      List.ofFn (fun i : Fin (P.faces.length + 1) =>
        (P2.faceWord P cut i).map (v (splitFace P cut i))) := by
    apply List.ext_getElem (by simp [P2.split])
    intro i hi hj
    simp [List.getElem_ofFn, boundary, P2.split, splitFace, List.get_eq_getElem]
  rw [hi, List.ofFn_succ_last]
  simp [P2.faceWord]

/-- Raw selected-child transport, including negative stored traversal and nil pieces. -/
private theorem selected_pair_perm (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (P2.selectedBoundary P cut ++ P2.rightBoundary P cut).Perm
      (retainWord (boundary P cut.face.face) ++
        [chooseDart cut.face.orientation (.pos (P2.freshEdge P)),
         chooseDart cut.face.orientation (.neg (P2.freshEdge P))]) := by
  let b := cut.face.orientation
  have hsource : (chooseWord b (cut.left ++ cut.right)).Perm
      (boundary P cut.face.face) := by
    have ho : (chooseWord b (orientedBoundary P cut.face)).Perm
        (boundary P cut.face.face) := by
      change (chooseWord b (P2.storedWord b (boundary P cut.face.face))).Perm _
      have hs := (stored_perm b (boundary P cut.face.face)).map (chooseDart b)
      change (chooseWord b (P2.storedWord b (boundary P cut.face.face))).Perm
        (chooseWord b (chooseWord b (boundary P cut.face.face))) at hs
      simpa only [chooseWord_twice] using hs
    exact (cut.boundary_rotated.perm.map (chooseDart b)).symm.trans ho
  have hchildren := (stored_perm b (P2.selectedOrientedBoundary P cut)).append
    (stored_perm b (P2.rightOrientedBoundary P cut))
  change (P2.selectedBoundary P cut ++ P2.rightBoundary P cut).Perm
    (chooseWord b (P2.selectedOrientedBoundary P cut) ++
      chooseWord b (P2.rightOrientedBoundary P cut)) at hchildren
  refine hchildren.trans ?_
  have hshuffle :
      ((retainWord (chooseWord b cut.left) ++
        [chooseDart b (.pos (P2.freshEdge P))]) ++
        chooseDart b (.neg (P2.freshEdge P)) :: retainWord (chooseWord b cut.right)).Perm
      (retainWord (chooseWord b (cut.left ++ cut.right)) ++
        [chooseDart b (.pos (P2.freshEdge P)), chooseDart b (.neg (P2.freshEdge P))]) := by
    simpa [chooseWord, retainWord, List.map_append, List.append_assoc] using
      (List.perm_append_comm
        (l₁ := [chooseDart b (.pos (P2.freshEdge P)), chooseDart b (.neg (P2.freshEdge P))])
        (l₂ := retainWord (chooseWord b cut.right))).append_left
          (retainWord (chooseWord b cut.left))
  have hold := (hsource.map retainDart).append_right
    [chooseDart b (.pos (P2.freshEdge P)), chooseDart b (.neg (P2.freshEdge P))]
  simpa only [P2.selectedOrientedBoundary, P2.rightOrientedBoundary, chooseWord,
    retainWord, List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def, choose_retain] using hshuffle.trans hold

/-- Exhaustive occurrence transport with source-face provenance. List.Perm is a
finite sequence of bijective position swaps, so equal readings are retained with
their multiplicities. The two additional positions are exactly the fresh pair. -/
private theorem occurrence_transport (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    ((occurrences (P2.split P cut)).map fun o =>
      (parentFace P cut o.1, dart (P2.split P cut) o)).Perm
      (((occurrences P).map fun o => (o.1, retainDart (dart P o))) ++
        [(cut.face.face, chooseDart cut.face.orientation (.pos (P2.freshEdge P))),
         (cut.face.face, chooseDart cut.face.orientation (.neg (P2.freshEdge P)))]) := by
  rw [split_map_occurrences, map_occurrences]
  simp only [parent_old, parent_last]
  apply family_replace cut.face.face
  · intro f hf
    simp [P2.faceWord, hf, retainWord, List.map_map]
  · simpa [P2.faceWord, List.map_append, List.map_cons, List.map_map] using
      (selected_pair_perm P cut).map (fun d => (cut.face.face, d))

private def liftChoice (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (r : Face P → Bool) (f : Face (P2.split P cut)) : Bool :=
  r (parentFace P cut f)

/-- Map the proved raw positional transport through the source face choices.
Both stored children inherit the unchanged source bit. -/
private theorem adjusted_transport (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (r : Face P → Bool) :
    (adjustedDarts (P2.split P cut) (liftChoice P cut r)).Perm
      (retainWord (adjustedDarts P r) ++
        [chooseDart (r cut.face.face)
          (chooseDart cut.face.orientation (.pos (P2.freshEdge P))),
         chooseDart (r cut.face.face)
          (chooseDart cut.face.orientation (.neg (P2.freshEdge P)))]) := by
  have h := (occurrence_transport P cut).map
    (fun z => chooseDart (r z.1) z.2)
  simpa only [adjustedDarts, liftChoice, retainWord, List.map_map, Function.comp_def,
    List.map_append, List.map_cons, List.map_nil, choose_retain] using h

private theorem retain_injective {n : ℕ} :
    Function.Injective (@retainDart n) := by
  intro a b h
  cases a with
  | pos e =>
    cases b with
    | pos f =>
      have he : e.castSucc = f.castSucc := SignedDart.pos.inj h
      exact congrArg SignedDart.pos (Fin.ext (congrArg Fin.val he))
    | neg _ => cases h
  | neg e =>
    cases b with
    | pos _ => cases h
    | neg f =>
      have he : e.castSucc = f.castSucc := SignedDart.neg.inj h
      exact congrArg SignedDart.neg (Fin.ext (congrArg Fin.val he))

/-- Actual fresh-edge extension/elimination: a disjoint opposite fresh pair adds
no old constraint. This is used on the transported occurrence list. -/
private theorem fresh_extension {n : ℕ} (w : List (SignedDart (Fin n))) (b o : Bool) :
    (retainWord w ++
      [chooseDart b (chooseDart o (.pos (Fin.last n))),
       chooseDart b (chooseDart o (.neg (Fin.last n)))]).Nodup ↔ w.Nodup := by
  have hp : (.pos (Fin.last n) : SignedDart (Fin (n + 1))) ∉ retainWord w := by
    simp only [retainWord, List.mem_map, not_exists, not_and]
    intro d _
    cases d <;> simp [retainDart]
  have hn : (.neg (Fin.last n) : SignedDart (Fin (n + 1))) ∉ retainWord w := by
    simp only [retainWord, List.mem_map, not_exists, not_and]
    intro d _
    cases d <;> simp [retainDart]
  have hnd : (retainWord w).Nodup ↔ w.Nodup :=
    List.nodup_map_iff retain_injective
  cases b <;> cases o <;>
    simp_all [chooseDart, List.nodup_append, List.disjoint_left]

/-- A chosen fresh dart is present in each actual child word. Membership here is
used only to select positions in two different child blocks, whose disjointness
follows from Nodup of the entire position enumeration. -/
private theorem child_fresh_mem (P : FiniteCyclicPresentation) (cut : P2Cut P) (b : Bool) :
    chooseDart b (chooseDart cut.face.orientation (.pos (P2.freshEdge P))) ∈
      chooseWord b (P2.selectedBoundary P cut) ∧
    chooseDart b (chooseDart cut.face.orientation (.neg (P2.freshEdge P))) ∈
      chooseWord b (P2.rightBoundary P cut) := by
  constructor
  · apply ((stored_perm cut.face.orientation (P2.selectedOrientedBoundary P cut)).map
      (chooseDart b)).mem_iff.mpr
    simp [P2.selectedOrientedBoundary, chooseWord]
  · apply ((stored_perm cut.face.orientation (P2.rightOrientedBoundary P cut)).map
      (chooseDart b)).mem_iff.mpr
    simp [P2.rightOrientedBoundary, chooseWord]

/-- The fresh occurrences force equality of the two STORED child bits.
No old occurrence count or nonempty cut condition is used. -/
private theorem child_choices_agree (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (t : Face (P2.split P cut) → Bool) (ht : CoherentChoices (P2.split P cut) t) :
    t (splitFace P cut cut.face.face.castSucc) =
      t (splitFace P cut (Fin.last P.faces.length)) := by
  have hnd := (coherent_iff_nodup (P2.split P cut) t).mp ht
  unfold adjustedDarts at hnd
  rw [split_map_occurrences] at hnd
  have hd := List.disjoint_of_nodup_append hnd
  let b := t (splitFace P cut cut.face.face.castSucc)
  let c := t (splitFace P cut (Fin.last P.faces.length))
  have hl := (child_fresh_mem P cut b).1
  have hr := (child_fresh_mem P cut c).2
  have hl' : chooseDart b (chooseDart cut.face.orientation (.pos (P2.freshEdge P))) ∈
      (List.ofFn fun f : Face P =>
        (P2.faceWord P cut f.castSucc).map
          (chooseDart (t (splitFace P cut f.castSucc)))).flatten := by
    apply List.mem_flatten.mpr
    refine ⟨chooseWord b (P2.selectedBoundary P cut), ?_, hl⟩
    apply List.mem_ofFn.mpr
    exact ⟨cut.face.face, by simp [P2.faceWord, chooseWord, b]⟩
  by_contra hbc
  change b ≠ c at hbc
  have he : chooseDart b (chooseDart cut.face.orientation (.pos (P2.freshEdge P))) =
      chooseDart c (chooseDart cut.face.orientation (.neg (P2.freshEdge P))) := by
    cases hb : b <;> cases hc : c <;> cases ho : cut.face.orientation <;>
      simp_all [chooseDart]
  exact (List.disjoint_left.mp hd hl') (he.symm ▸ hr)

/-- Preservation and reflection of existence of coherent choices for the ACTUAL
full P2 cut. Includes either traversal, every rotation, empty words and one-sided
cuts. It asserts a combinatorial invariant, not orientability of a quotient space. -/
theorem p2_full_coherent_orientation_iff (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    Coh P ↔ Coh (P2.split P cut) := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨liftChoice P cut r, ?_⟩
    apply (coherent_iff_nodup (P2.split P cut) (liftChoice P cut r)).mpr
    apply (adjusted_transport P cut r).nodup_iff.mpr
    exact (fresh_extension (adjustedDarts P r) (r cut.face.face) cut.face.orientation).mpr
      ((coherent_iff_nodup P r).mp hr)
  · rintro ⟨t, ht⟩
    have hagree := child_choices_agree P cut t ht
    let r : Face P → Bool := fun f => t (splitFace P cut f.castSucc)
    have hlift : liftChoice P cut r = t := by
      funext f
      let i : Fin (P.faces.length + 1) := Fin.cast (by simp [P2.split]) f
      have hf : splitFace P cut i = f := by simp [splitFace, i]
      rw [← hf]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [liftChoice, r] using hagree
      · simp [liftChoice, r]
    refine ⟨r, (coherent_iff_nodup P r).mpr ?_⟩
    have hnd := (coherent_iff_nodup (P2.split P cut) t).mp ht
    rw [← hlift] at hnd
    have htransported := (adjusted_transport P cut r).nodup_iff.mp hnd
    exact (fresh_extension (adjustedDarts P r) (r cut.face.face) cut.face.orientation).mp
      htransported

end D5.S3.Geometry.Gluing.CyclicP2CoherentOrientation
