/- GID: D5/S3/Combinatorics/Golomb/NotikSubtreeReplay
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Golomb/NotikSubtreeReplay
   mirror-E: none(waiver:kernel-replayed-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Golomb/NotikCheck8.archivedCertificate8; instance=D5/S3/Combinatorics/Golomb/NotikCheck8.archivedCertificate8
   digest: Checked subtree certificates compose in branch order. -/

import D5.S3.Combinatorics.Golomb.EqualityReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Golomb.Replay

/-- Successful coverage consumes a prefix and leaves any appended certificates untouched. -/
private theorem Tree.cover_append {n : ℕ} {target : ℤ} {data : Array (Static n)}
    {witnesses : Array (RelationWitness n)} {tree : Tree} {path : List (Row n)}
    {table tail : LeafTable} (extra : LeafTable)
    (h : tree.cover target data witnesses path table = some tail) :
    tree.cover target data witnesses path (table ++ extra) = some (tail ++ extra) := by
  induction tree generalizing path table tail with
  | farkas id weights =>
    simp only [Tree.cover, Option.some.injEq] at h ⊢
    rw [h]
  | bound id scale weights =>
    cases hr : totalRhs data weights with
    | none => simp [Tree.cover, hr] at h
    | some rhs =>
      by_cases ht : rhs = (scale : ℤ) * target
      · cases table with
        | nil => simp [Tree.cover, hr, ht] at h
        | cons item table =>
          obtain ⟨key, cert⟩ := item
          cases hc : (key == id && cert.check data (relationRows witnesses)
              (directLookup data path) weights []) <;> simp [Tree.cover, hr, ht, hc] at h ⊢
          exact h
      · simp [Tree.cover, hr, ht] at h ⊢
        rw [h]
  | branch id rel left right ihLeft ihRight =>
    cases hw : witnesses[rel]? with
    | none => simp [Tree.cover, hw] at h
    | some w =>
      cases hl : left.cover target data witnesses (path ++ [branchRow false w.normal]) table with
      | none => simp [Tree.cover, hw, hl] at h
      | some middle =>
        have hr : right.cover target data witnesses (path ++ [branchRow true w.normal]) middle =
            some tail := by simpa [Tree.cover, hw, hl] using h
        simpa [Tree.cover, hw, ihLeft hl] using ihRight hr

/-- Exact lower-bound and equality checks for a subtree at its inherited path. -/
structure SubtreeCertificate {n : ℕ} (target : ℤ) (data : Array (Static n))
    (witnesses : Array (RelationWitness n)) (path : List (Row n)) (tree : Tree)
    (table : LeafTable) : Prop where
  checked : tree.check target (staticRows data) (relationRows witnesses) path = true
  covered : tree.cover target data witnesses path table = some []

/-- Join the negative and positive checks using the archive's witness and traversal order. -/
theorem SubtreeCertificate.branch {n : ℕ} {target : ℤ} {data : Array (Static n)}
    {witnesses : Array (RelationWitness n)} {path : List (Row n)} {id rel : ℕ}
    {left right : Tree} {first second : LeafTable}
    (hi : rel < witnesses.size)
    (hl : SubtreeCertificate target data witnesses (path ++ [branchRow false witnesses[rel].normal]) left first)
    (hr : SubtreeCertificate target data witnesses (path ++ [branchRow true witnesses[rel].normal]) right second) :
    SubtreeCertificate target data witnesses path (.branch id rel left right) (first ++ second) := by
  have hw : witnesses[rel]? = some witnesses[rel] := getElem?_pos witnesses rel hi
  have hm : (relationRows witnesses)[rel]? = some witnesses[rel].normal := by
    rw [relationRows, Array.getElem?_map, hw]
    rfl
  have hc : left.cover target data witnesses (path ++ [branchRow false witnesses[rel].normal]) (first ++ second) =
      some second := Tree.cover_append (tree := left) second hl.covered
  exact ⟨by simp only [Tree.check, hm, hl.checked, hr.checked, Bool.and_self],
    by simpa [Tree.cover, hw, hc] using hr.covered⟩

end D5.S3.Combinatorics.Golomb.Replay
