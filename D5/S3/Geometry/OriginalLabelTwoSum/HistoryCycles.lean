/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryCycles
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryCycles
   mirror-E: none(waiver:physical-history-all-residue-cycles)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Actual fill0 and path lists construct every wheel cycle by the proved size-bounded attachment. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryAttachment
import D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected

/-! SOURCE_ONLY_UNCOMPILED. D10 for EVERY m>=3, including 3,4,5.
The path certificate is extracted from the actual pathRowsOutput. The D8
size premises are derived below, not passed to the cycle constructor. Its
main is fill0 inside Delta(Z), then the emitted path-main subsequence. Its
separate list is the ORIGINAL skipped subsequence, then the path core list.
The frozen Protected owner is an unreviewed source dependency; independent
source review and actual kernel/native checks remain necessary.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles
open OriginalLabelTwoSum AllMWheel HistoryLeafCap HistoryPaths HistoryAttachment
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
open FinitePrescribedPairProtection

private theorem chosen_supported {V : Type*} [DecidableEq V] (vs : List V) :
    FiniteIndependentPathGreedy.pathChosen vs ⊆ vs.toFinset := by
  match vs with
  | [] => simp [FiniteIndependentPathGreedy.pathChosen]
  | [a] => simp [FiniteIndependentPathGreedy.pathChosen]
  | [a,b] => simp [FiniteIndependentPathGreedy.pathChosen]
  | a::b::c::vs =>
      exact Finset.insert_subset (by simp) ((chosen_supported vs).trans (by
        intro x hx
        simp only [List.toFinset_cons, Finset.mem_insert]
        exact Or.inr (Or.inr (Or.inr hx))))
termination_by vs.length

private theorem chosen_card {V : Type*} [DecidableEq V] (vs : List V) (hd : vs.Nodup) :
    (FiniteIndependentPathGreedy.pathChosen vs).card = (vs.length + 1) / 3 := by
  match vs with
  | [] => simp [FiniteIndependentPathGreedy.pathChosen]
  | [a] => simp [FiniteIndependentPathGreedy.pathChosen]
  | [a,b] => simp [FiniteIndependentPathGreedy.pathChosen]
  | a::b::c::vs =>
      have hdT := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2).2
      have hb : b ∉ FiniteIndependentPathGreedy.pathChosen vs := by
        intro h
        have hv := List.mem_toFinset.mp (chosen_supported vs h)
        exact (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1 (by simp [hv])
      rw [FiniteIndependentPathGreedy.pathChosen, Finset.card_insert_of_notMem hb,
        chosen_card vs hdT]
      simp only [List.length_cons]
      omega
termination_by vs.length

private theorem tail_ground_interval (m : Nat) (hm : 3 ≤ m) :
    tailGround m hm = (labelInterval m 3 (m-2) (by omega)).toFinset := by
  ext x
  simp only [tailGround, ground, rim, Finset.mem_sdiff, Finset.mem_erase,
    Finset.mem_univ, and_true, Finset.mem_insert, Finset.mem_singleton,
    List.mem_toFinset, mem_labelInterval, Fin.ext_iff, firstLabel, secondLabel, ne_eq, Fin.val_zero, Fin.val_mk]
  have hx := x.isLt
  omega

private theorem tail_ground_card (m : Nat) (hm : 3 ≤ m) :
    (tailGround m hm).card = m-2 := by
  rw [tail_ground_interval m hm,
    List.toFinset_card_of_nodup (labelInterval_nodup m 3 (m-2) (by omega)),
    labelInterval_length]

private theorem tail_critical_chosen (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 2) :
    tailCritical m hm = FiniteIndependentPathGreedy.pathChosen (cyclePathTail m hm) := by
  ext x
  simp only [tailCritical, if_neg hr, labelsCongruent, Finset.mem_filter,
    Finset.mem_univ, true_and, cyclePathTail, pathChosen_labelInterval]
  have hx := x.isLt
  omega

/-- The exact attachment size, obtained from the real ghost-retaining tail.
At m=3 and 4 the chosen tail is empty and eta is respectively a vertex/edge. -/
theorem eta0_card (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 2) :
    (eta0 m hm).card = if m % 3 = 0 then 2*(m/3)-1 else 2*(m/3) := by
  have hsub : tailCritical m hm ⊆ tailGround m hm := by
    rw [tail_critical_chosen m hm hr]
    exact (chosen_supported _).trans (by
      intro x hx
      rw [tail_ground_interval, List.mem_toFinset, mem_labelInterval]
      have ht := (cyclePathTail_vertices m hm x).mp hx
      omega)
  have hc : (tailCritical m hm).card = ((m-4)+1)/3 := by
    rw [tail_critical_chosen m hm hr,
      chosen_card _ (cyclePathTail_nodup m hm), cyclePathTail_length]
  rw [eta0, Finset.card_sdiff_of_subset hsub, tail_ground_card m hm, hc]
  split_ifs <;> omega

/-- The existing original indexed path root is the literal pathRows root.
Every row, including the wrap edge, is matched using the frozen all-m API. -/
theorem pathRows_pathRoot (m : Nat) (hm : 3 ≤ m) :
    (pathRows (pathRootPath m hm)).root = pathRoot m hm := by
  apply SetLike.ext
  intro s
  rw [pathRows_mem, pathRootPath_vertices, pathRootPath_row_edges]
  constructor
  · rintro ⟨hs, q, hq, hd⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨⟨i, (Finset.mem_erase.mp hi).1⟩, ?_⟩
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hs hx, fun hq => Finset.disjoint_left.mp hd hq hx⟩
  · rintro ⟨i, hs⟩
    refine ⟨hs.trans Finset.sdiff_subset, rimEdge m (by omega) i.val,
      Finset.mem_image.mpr ⟨i.val,
        Finset.mem_erase.mpr ⟨i.property, Finset.mem_univ _⟩, rfl⟩, ?_⟩
    exact Finset.disjoint_left.mpr (fun x hxq hxs => (Finset.mem_sdiff.mp (hs hxs)).2 hxq)

private def castCertificate {V : Type*} [Fintype V] [DecidableEq V]
    {W W' : Finset V} {K K' : Family V} (hW : W = W') (hK : K = K')
    (c : Certificate W K) : Certificate W' K' := by
  subst W'
  subst K'
  exact c

private theorem castCertificate_critical {V : Type*} [Fintype V] [DecidableEq V]
    {W W' : Finset V} {K K' : Family V} (hW : W = W') (hK : K = K')
    (c : Certificate W K) : (castCertificate hW hK c).critical = c.critical := by
  subst W'
  subst K'
  rfl

def pathRootCertificate (m : Nat) (hm : 3 ≤ m) :
    Certificate (ground m) (pathRoot m hm) :=
  castCertificate (pathRootPath_vertices m hm) (pathRows_pathRoot m hm)
    (pathRowsOutput_critical_profile (pathRootPath m hm) (pathRootPath_nodup m hm)
      (by simpa only [pathRootPath_length] using hm)).choose

theorem pathRootCertificate_profile (m : Nat) (hm : 3 ≤ m) :
    PathCriticalProfile m (pathRootCertificate m hm).critical := by
  rw [pathRootCertificate, castCertificate_critical]
  simpa only [pathRootPath_length] using
    (pathRowsOutput_critical_profile (pathRootPath m hm) (pathRootPath_nodup m hm)
      (by simpa only [pathRootPath_length] using hm)).choose_spec.2

/-- Bound used by D8. It is derived from m, never chosen from a desired
certificate. The residue-two new family is empty, so its size bound is vacuous. -/
def attachmentSize (m : Nat) : Nat :=
  if m % 3 = 0 then 2*(m/3)-1 else 2*(m/3)

private theorem new_size (m : Nat) (hm : 3 ≤ m) :
    ∀ q ∈ (fill0 m hm).critical, q.card ≤ attachmentSize m := by
  intro q hq
  rw [fill0_critical] at hq
  by_cases hr : m % 3 = 2
  · simp [hr] at hq
  · have he : q = eta0 m hm := by simpa [hr] using hq
    rw [he, eta0_card m hm hr]
    exact le_rfl

private theorem old_size (m : Nat) (hm : 3 ≤ m) :
    ∀ q ∈ (pathRootCertificate m hm).critical, attachmentSize m ≤ q.card := by
  have hp := pathRootCertificate_profile m hm
  intro q hq
  by_cases h0 : m % 3 = 0
  · obtain ⟨r, hr, hc⟩ := hp.2.1 h0
    have he : q = r := by simpa only [hr, Finset.mem_singleton] using hq
    simp only [attachmentSize, if_pos h0, he, hc, le_refl]
  · by_cases h1 : m % 3 = 1
    · rw [hp.1 h1] at hq
      exact (Finset.notMem_empty q hq).elim
    · have h2 : m % 3 = 2 := by omega
      obtain ⟨r, hr, hc⟩ := hp.2.2 h2
      have he : q = r := by simpa only [hr, Finset.mem_singleton] using hq
      simp only [attachmentSize, if_neg h0, he, hc, le_refl]

/-- Actual original fill0 run in Delta(Z), with E fixed. The empty prefix
adds no labels. Each CURRENT domain is supplied by the existing native lift. -/
def cycleStrip (m : Nat) (hm : 3 ≤ m) :
    Sequence (project (A1 m hm))
      (project (endpoint (pathRoot m hm) (fill0 m hm).critical)) := by
  let f := fill0 m hm
  let S := liftFibre (delta (tailGround m hm)) (endpoint (A0 m hm) f.critical)
    (pathRoot m hm) ∅ (tailGround m hm) (Finset.empty_subset _)
    (Or.inl f.empty_mem) f.main (by simp) (fun _ h => h)
    (by intro x hx; exact (Finset.not_ssubset_empty x hx).elim)
    (by intro t ht h; exact Or.inl ⟨by simpa using h, ht⟩)
  have hstart : pathRoot m hm ⊔ rawJoin (delta ∅) (delta (tailGround m hm)) = A1 m hm := by
    rw [(rawJoin_unit _).1]
    rfl
  have hend : pathRoot m hm ⊔ rawJoin (delta ∅) (endpoint (A0 m hm) f.critical) =
      endpoint (pathRoot m hm) f.critical := by
    rw [(rawJoin_unit _).1]
    change pathRoot m hm ⊔ (A0 m hm ⊔ facets f.critical) = pathRoot m hm ⊔ facets f.critical
    rw [← sup_assoc, sup_eq_left.mpr (show A0 m hm ≤ pathRoot m hm from inf_le_left)]
  exact S.cast (congrArg project hstart) (congrArg project hend)

/-- fill0's original pair order is preserved literally. -/
theorem cycleStrip_pairs (m : Nat) (hm : 3 ≤ m) :
    (cycleStrip m hm).pairs.map (fun P => (P.lower, P.upper)) =
      (fill0 m hm).main.pairs.map (fun P => (P.lower, P.upper)) := by
  simp only [cycleStrip, Sequence.pairs_cast, liftFibre_pairs, Finset.empty_union]

private def afterStrip (m : Nat) (hm : 3 ≤ m) :
    Certificate (ground m) (endpoint (pathRoot m hm) (fill0 m hm).critical) :=
  boundedAttachment (ground m) (pathRoot m hm) (pathRootCertificate m hm)
    (fill0 m hm).critical (attachmentSize m)
    (fun q hq => ((fill0 m hm).critical_supported q hq).trans Finset.sdiff_subset)
    (fill0 m hm).cells.nonempty
    (by
      intro q hq hE
      exact (fill0 m hm).cells.absent q hq
        ⟨hE, (fill0 m hm).critical_supported q hq⟩)
    (fun q hq s hs => ((fill0 m hm).cells.boundary q hq s hs).1)
    (new_size m hm) (old_size m hm)

/-- ALL-RESIDUE actual cycle certificate, without any supplied desired path,
cycle, core or profile. Widths 3,4,5 use the same proved constructor. -/
def cycleCertificate (m : Nat) (hm : 3 ≤ m) : Certificate (ground m) (A1 m hm) where
  supported := by
    intro s hs
    exact hs.elim
      (fun hs => (((rimRows m (by omega)).without (interfaceRow m hm)).root_supported s hs))
      (fun hs => hs.trans Finset.sdiff_subset)
  core := (afterStrip m hm).core
  critical := (afterStrip m hm).critical
  vertex := (afterStrip m hm).vertex
  vertex_mem := (afterStrip m hm).vertex_mem
  core_supported := (afterStrip m hm).core_supported
  critical_supported := (afterStrip m hm).critical_supported
  cells := (afterStrip m hm).cells
  main := (cycleStrip m hm).append (afterStrip m hm).main
  separate := (afterStrip m hm).separate

/-- Both actual sources of critical tops, with no discarded residue. -/
theorem cycleCertificate_critical (m : Nat) (hm : 3 ≤ m) :
    (cycleCertificate m hm).critical =
      (pathRootCertificate m hm).critical ∪ (fill0 m hm).critical := rfl

/-- Exact main list: original fill0, then the emitted path pairs. -/
theorem cycleCertificate_main_pairs (m : Nat) (hm : 3 ≤ m) :
    (cycleCertificate m hm).main.pairs.map (fun P => (P.lower, P.upper)) =
      (fill0 m hm).main.pairs.map (fun P => (P.lower, P.upper)) ++
      (emitted (pathRootCertificate m hm).main.pairs (fill0 m hm).critical).map
        (fun P => (P.lower, P.upper)) := by
  simp only [cycleCertificate, Sequence.pairs_append, List.map_append, cycleStrip_pairs]
  rw [afterStrip, boundedAttachment_main_pairs]

/-- Exact C-ALONE list: ORIGINAL skipped order, then the actual path C-only
list. No critical top is in this sequence's starting domain. -/
theorem cycleCertificate_separate_pairs (m : Nat) (hm : 3 ≤ m) :
    (cycleCertificate m hm).separate.pairs.map (fun P => (P.lower, P.upper)) =
      (skipped (pathRootCertificate m hm).main.pairs (fill0 m hm).critical).map
        (fun P => (P.lower, P.upper)) ++
      (pathRootCertificate m hm).separate.pairs.map (fun P => (P.lower, P.upper)) := by
  change (afterStrip m hm).separate.pairs.map _ = _
  rw [afterStrip, boundedAttachment_separate_pairs]

/-- Consume the literal original indexed wheel API, on its unchanged ground. -/
def wheelRowsOutput (m : Nat) (hm : 3 ≤ m) :
    Output (rimRows m (by omega)).ground (rimRows m (by omega)).root :=
  changeOutput (.strong (cycleCertificate m hm)) (wheelRoot_eq_A1 m hm).symm

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles
