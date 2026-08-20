/- GID: D5/S1/Words/ReturnWords/GoldenWindowCounts
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: counts append one letter; for m<=n, equal factors give equal counts; golden factors give equal cuts; for m<=n, equal cuts give equal counts. -/

import Mathlib
import D5.S1.Words.ReturnWords.GoldenRankArcs

/- Provenance: Native proof over pinned mathlib. -/

/-!
SEARCH RECEIPT

Queries and outcomes:
* `rg -n \
  'window_count_succ|window_counts_eq_of_selected_eq|'\
  'window_counts_eq_of_factor_eq|selected_eq_of_factor_eq' \
  D5 --glob '*.lean'`
  hit the two golden private groups in `GoldenFactorComplexity.lean` and
  `GoldenOccurrenceGaps.lean`, the mechanical private group in
  `MechanicalFactorComplexity.lean`, and an additional private successor lemma
  in `MechanicalUniformRecurrence.lean`; it found no public declaration.
* `rg -n \
  'window_count_succ|window_counts_eq_of_selected_eq|'\
  'window_counts_eq_of_factor_eq|selected_eq_of_factor_eq' \
  .lake/packages/mathlib/Mathlib .lake/packages/batteries/Batteries \
  /Users/lexa/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean \
  --glob '*.lean'`
  had no hits in any of the three pinned library trees.
* `rg -n 'range_add_one|card_filter|filter_insert|sum_range_succ|countP_cons' \
  .lake/packages/mathlib/Mathlib --glob '*.lean'`
  hit the generic finite-set and list counting API, including
  `Finset.range_add_one`, `Finset.filter_insert`, and `List.countP_cons`.
* `rg -n 'range_add_one|card_filter|filter_insert|sum_range_succ|countP_cons' \
  .lake/packages/batteries/Batteries \
  /Users/lexa/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean \
  --glob '*.lean'`
  hit `List.countP_cons` and its uses in Lean core and one Batteries use; it did
  not hit a theorem about the repository's window-count definition.
* `rg -n \
  'ofFn_inj|ofFn.*Injective|take.*ofFn|ofFn.*take|countP.*take|filter.*take' \
  .lake/packages/mathlib/Mathlib --glob '*.lean'`
  hit `List.ofFn_inj`, `List.ofFn_injective`, and
  `Fin.ofFn_take_eq_take_ofFn`; none states equality of the repository's
  bounded window counts.
* `rg -n \
  'filter_eq_filter|filter_congr|eq_of_subset_of_card_le|card_filter.*filter|filter.*card.*eq' \
  .lake/packages/mathlib/Mathlib --glob '*.lean'`
  hit `Finset.filter_congr` and `Finset.eq_of_subset_of_card_le`; no hit
  identified equality of two linearly ordered cuts from equality of golden
  factors.
* `rg -n \
  '^theorem .*factor_eq_iff.*rank_eq|^theorem .*rank.*factor|'\
  '^noncomputable def goldenCylinderEndpoint(Set)?|'\
  '^noncomputable def goldenPhase' \
  D5/S1/Words --glob '*.lean'`
  hit the public `golden_factor_eq_iff_cylinder_rank_eq`, `goldenPhase`,
  `goldenCylinderEndpoint`, and `goldenCylinderEndpointSet` declarations.
* `rg -n \
  'goldenWindowTrueCount.*=.*goldenWindowTrueCount|'\
  'goldenCylinderEndpointSet.*filter|goldenFactor n i = goldenFactor n j' \
  D5 --glob '*.lean'`
  hit the private copies, private downstream selected-endpoint arguments, and
  the public factor/rank equivalence; it found no public declaration with any
  target conclusion under a different name.
* `rg -n -C 6 'SL-028' docs/develop/spec/golden-ledger-repo-spec.md tools D5 \
  --glob '*.cs' --glob '*.md' --glob '*.lean'`
  had no hit in this checkout. Thus the requested description of SL-028 is not
  treated as machine evidence here; the manual same-statement search above was
  still performed.

Candidates INSPECTED:
* `List.countP_cons`, Lean core
  `Init/Data/List/Count.lean:60`.
* `Finset.range_add_one`, pinned mathlib
  `Mathlib/Data/Finset/Range.lean:79`.
* `Finset.filter_insert`, pinned mathlib
  `Mathlib/Data/Finset/Basic.lean:370`.
* `Finset.card_insert_of_notMem`, pinned mathlib
  `Mathlib/Data/Finset/Card.lean:104`.
* `List.ofFn_inj`, pinned mathlib
  `Mathlib/Data/List/OfFn.lean:189`.
* `Fin.ofFn_take_eq_take_ofFn`, pinned mathlib
  `Mathlib/Data/Fin/Tuple/Take.lean:140`.
* `Finset.filter_congr`, pinned mathlib
  `Mathlib/Data/Finset/Filter.lean:176`.
* `Finset.eq_of_subset_of_card_le`, pinned mathlib
  `Mathlib/Data/Finset/Card.lean:277`.
* `golden_factor_eq_iff_cylinder_rank_eq`,
  `D5/S1/Words/ReturnWords/GoldenOccurrenceGaps.lean:199`.
* `goldenCylinderEndpoint` and `goldenCylinderEndpointSet`,
  `D5/S1/Words/ReturnWords/GoldenRankArcs.lean:16,20`.

Lemmas the proofs ACTUALLY USE:
* `Finset.range_add_one`, `Finset.filter_insert`, and
  `Finset.card_insert_of_notMem` establish the successor recurrence.
* `List.ofFn_inj` transports factor equality to pointwise letter equality.
* `Finset.ext` transports those letter equalities to filtered-range equality.
* `golden_factor_eq_iff_cylinder_rank_eq` converts between factor equality and
  the already-public cylinder rank.
* `Finset.eq_of_subset_of_card_le` identifies nested phase cuts of equal size.

Reassociation, the `Nat`-to-`Int` casts occurring only in the frozen indicator
proofs, unfolding, simplification, and finite-index bound transport are
bookkeeping. After removing that bookkeeping, the substantive-reasoning counts
are respectively one, two, two, and three: insert the new endpoint into the
count; recover pointwise letters and transport the restricted filter; convert
factor equality to equal rank and identify nested equal-cardinality cuts; and
convert equal selections to equal rank, then to equal factors, then invoke the
restricted-count theorem.

The golden flavour is not definitionally the mechanical flavour at the golden
slope. `goldenWord` is defined from the Fibonacci-word tower, whereas
`lowerMechanicalWord goldenMechanicalSlope 0 (i + 1) = goldenWord i` is a
proved bridge with a one-index shift. Accordingly, golden factors and window
counts correspond to mechanical factors and counts at intercept zero and start
`i + 1`, not by definitional instantiation. The phases agree only after matching
the same shift: the mechanical phase is `fract (rho + i * alpha)`, while
`goldenPhase i` is `fract ((i + 1) * goldenMechanicalSlope)`.

Generality is `I`. The selection statements use the concrete golden phase and
golden cylinder endpoints, and the weakest repository import that supplies the
public endpoint/rank interface is instance-level. The successor and
factor-prefix count statements are freely generalized to an arbitrary Boolean
word; their golden and mechanical copies follow by direct instantiation. The
two selection statements do not freely generalize beyond the golden interface
without adding an abstract rank/selection structure or hypotheses that install
the desired conclusion mechanism.

The chosen GID is `D5/S1/Words/ReturnWords/GoldenWindowCounts`. An earlier draft
of this file sat under `Words/Mechanical`; review rejected that address because no
published declaration here carries the mechanical-word parameters, and this
paragraph then conceded that the natural address was `Words/ReturnWords`. The file
was relocated accordingly by the orchestrator. Measured bucket size for
`Words/ReturnWords` on `origin/dev` at relocation time was eleven, so this file
makes twelve, at but not over the strictly-greater-than-12 split threshold.

No `rank`, `rank_le`, selected-rank lemma, or window-count indicator theorem is
added to the public surface. All four target lemmas can be published using the
existing public golden rank/endpoint interface; the indicator arithmetic and
the rank implementation remain encapsulated in frozen modules.

The inspected-candidate list is not claimed to be exhaustive.
-/

namespace D5.S1.Words.ReturnWords.GoldenWindowCounts

/-- Appending one letter updates a Boolean-word true count by its indicator. -/
theorem window_count_succ (word : Nat → Bool) (i m : Nat) :
    ((Finset.range (m + 1)).filter fun k => word (i + k) = true).card =
      ((Finset.range m).filter fun k => word (i + k) = true).card +
        if word (i + m) = true then 1 else 0 := by
  classical
  rw [Finset.range_add_one, Finset.filter_insert]
  have hm : m ∉ (Finset.range m).filter (fun k => word (i + k) = true) := by
    simp
  by_cases h : word (i + m) = true
  · rw [if_pos h, Finset.card_insert_of_notMem hm, if_pos h]
  · rw [if_neg h, if_neg h, Nat.add_zero]

/-- Equal Boolean-word factors have equal true counts in every shorter prefix. -/
theorem window_counts_eq_of_factor_eq (word : Nat → Bool) {n i j m : Nat}
    (hm : m ≤ n)
    (h : List.ofFn (fun k : Fin n => word (i + k)) =
      List.ofFn (fun k : Fin n => word (j + k))) :
    ((Finset.range m).filter fun k => word (i + k) = true).card =
      ((Finset.range m).filter fun k => word (j + k) = true).card := by
  have hletters : (fun k : Fin n => word (i + k)) =
      fun k : Fin n => word (j + k) := List.ofFn_inj.mp h
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk, hw⟩
    exact ⟨hk, by rw [← congrFun hletters ⟨k, hk.trans_le hm⟩]; exact hw⟩
  · rintro ⟨hk, hw⟩
    exact ⟨hk, by rw [congrFun hletters ⟨k, hk.trans_le hm⟩]; exact hw⟩

/-- Equal golden factors select the same cylinder endpoints below their phases. -/
theorem selected_eq_of_factor_eq {n i j : Nat}
    (h : goldenFactor n i = goldenFactor n j) :
    (goldenCylinderEndpointSet n).filter (fun x => x ≤ goldenPhase i) =
      (goldenCylinderEndpointSet n).filter (fun x => x ≤ goldenPhase j) := by
  have hrank : goldenCylinderRank n i = goldenCylinderRank n j :=
    (golden_factor_eq_iff_cylinder_rank_eq n i j).mp h
  rcases le_total (goldenPhase i) (goldenPhase j) with hij | hji
  · apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans hij⟩
    · change goldenCylinderRank n j ≤ goldenCylinderRank n i
      exact hrank.ge
  · symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans hji⟩
    · change goldenCylinderRank n i ≤ goldenCylinderRank n j
      exact hrank.le

/-- Equal golden cylinder selections give equal true counts in every shorter window. -/
theorem window_counts_eq_of_selected_eq {n i j m : Nat} (hm : m ≤ n)
    (h : (goldenCylinderEndpointSet n).filter (fun x => x ≤ goldenPhase i) =
      (goldenCylinderEndpointSet n).filter (fun x => x ≤ goldenPhase j)) :
    goldenWindowTrueCount i m = goldenWindowTrueCount j m := by
  have hrank : goldenCylinderRank n i = goldenCylinderRank n j := by
    change ((goldenCylinderEndpointSet n).filter (fun x => x ≤ goldenPhase i)).card =
      ((goldenCylinderEndpointSet n).filter (fun x => x ≤ goldenPhase j)).card
    exact congrArg Finset.card h
  have hfactor := (golden_factor_eq_iff_cylinder_rank_eq n i j).mpr hrank
  change List.ofFn (fun k : Fin n => goldenWord (i + k)) =
    List.ofFn (fun k : Fin n => goldenWord (j + k)) at hfactor
  exact window_counts_eq_of_factor_eq goldenWord hm hfactor

#print axioms window_count_succ
#print axioms window_counts_eq_of_selected_eq
#print axioms window_counts_eq_of_factor_eq
#print axioms selected_eq_of_factor_eq

end D5.S1.Words.ReturnWords.GoldenWindowCounts
