/- GID: D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.actual_chromatic_number_six; instance=D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.catalogue_proper
   digest: Supplied exact six-bit orthogonality catalogue and complete proof transfer. -/

import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows00
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows01
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows02
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows03
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows04
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows05
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows06
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows07
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows08
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows09
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows10
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows11
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows12
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows13
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows14
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows15
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows16
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows17
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows18
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows19
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows20
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows21
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows22
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows23
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows24
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows25
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows26
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows27
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows28
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows29
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows30
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows31
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows32
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows33
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows34
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows35
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows36
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows37
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows38
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows39
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows40
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows41
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows42
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows43
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueRows44
import D5.S3.Combinatorics.Orthogonality.SixBitSubmoduleBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BinaryOrthogonality

/- The supplied Lean 4.33.0 source used native_decide for the following
four obligations. Its recorded provenance includes the four generated
catalogue_covers/catalogue_proper/clique_valid/clique_adjacent native axioms.
That historical evidence is retained in the scientific handoff. Current
admission instead requires ordinary kernel reduction of these same exact
predicates and unchanged tables; no native-evaluation axiom is added here.
All row blocks retain every vector and pair predicate; their soundness
proofs recover the original Covers and Proper statements. -/
private theorem all_rows_checked (i : Fin dimensionSix.count) :
    dimensionSix.rowCheck i.val = true := by
  have hi : i.val < 2825 := i.isLt
  by_cases h00 : i.val < 10
  · exact (checkAll_spec _ _).mp checked_rows_00 i.val h00
  by_cases h01 : i.val < 74
  · have h := (checkAll_spec _ _).mp checked_rows_01 (i.val - 10) (by omega)
    have he : 10 + (i.val - 10) = i.val := by omega
    simpa only [he] using h
  by_cases h02 : i.val < 138
  · have h := (checkAll_spec _ _).mp checked_rows_02 (i.val - 74) (by omega)
    have he : 74 + (i.val - 74) = i.val := by omega
    simpa only [he] using h
  by_cases h03 : i.val < 202
  · have h := (checkAll_spec _ _).mp checked_rows_03 (i.val - 138) (by omega)
    have he : 138 + (i.val - 138) = i.val := by omega
    simpa only [he] using h
  by_cases h04 : i.val < 266
  · have h := (checkAll_spec _ _).mp checked_rows_04 (i.val - 202) (by omega)
    have he : 202 + (i.val - 202) = i.val := by omega
    simpa only [he] using h
  by_cases h05 : i.val < 330
  · have h := (checkAll_spec _ _).mp checked_rows_05 (i.val - 266) (by omega)
    have he : 266 + (i.val - 266) = i.val := by omega
    simpa only [he] using h
  by_cases h06 : i.val < 394
  · have h := (checkAll_spec _ _).mp checked_rows_06 (i.val - 330) (by omega)
    have he : 330 + (i.val - 330) = i.val := by omega
    simpa only [he] using h
  by_cases h07 : i.val < 458
  · have h := (checkAll_spec _ _).mp checked_rows_07 (i.val - 394) (by omega)
    have he : 394 + (i.val - 394) = i.val := by omega
    simpa only [he] using h
  by_cases h08 : i.val < 522
  · have h := (checkAll_spec _ _).mp checked_rows_08 (i.val - 458) (by omega)
    have he : 458 + (i.val - 458) = i.val := by omega
    simpa only [he] using h
  by_cases h09 : i.val < 586
  · have h := (checkAll_spec _ _).mp checked_rows_09 (i.val - 522) (by omega)
    have he : 522 + (i.val - 522) = i.val := by omega
    simpa only [he] using h
  by_cases h10 : i.val < 650
  · have h := (checkAll_spec _ _).mp checked_rows_10 (i.val - 586) (by omega)
    have he : 586 + (i.val - 586) = i.val := by omega
    simpa only [he] using h
  by_cases h11 : i.val < 714
  · have h := (checkAll_spec _ _).mp checked_rows_11 (i.val - 650) (by omega)
    have he : 650 + (i.val - 650) = i.val := by omega
    simpa only [he] using h
  by_cases h12 : i.val < 778
  · have h := (checkAll_spec _ _).mp checked_rows_12 (i.val - 714) (by omega)
    have he : 714 + (i.val - 714) = i.val := by omega
    simpa only [he] using h
  by_cases h13 : i.val < 842
  · have h := (checkAll_spec _ _).mp checked_rows_13 (i.val - 778) (by omega)
    have he : 778 + (i.val - 778) = i.val := by omega
    simpa only [he] using h
  by_cases h14 : i.val < 906
  · have h := (checkAll_spec _ _).mp checked_rows_14 (i.val - 842) (by omega)
    have he : 842 + (i.val - 842) = i.val := by omega
    simpa only [he] using h
  by_cases h15 : i.val < 970
  · have h := (checkAll_spec _ _).mp checked_rows_15 (i.val - 906) (by omega)
    have he : 906 + (i.val - 906) = i.val := by omega
    simpa only [he] using h
  by_cases h16 : i.val < 1034
  · have h := (checkAll_spec _ _).mp checked_rows_16 (i.val - 970) (by omega)
    have he : 970 + (i.val - 970) = i.val := by omega
    simpa only [he] using h
  by_cases h17 : i.val < 1098
  · have h := (checkAll_spec _ _).mp checked_rows_17 (i.val - 1034) (by omega)
    have he : 1034 + (i.val - 1034) = i.val := by omega
    simpa only [he] using h
  by_cases h18 : i.val < 1162
  · have h := (checkAll_spec _ _).mp checked_rows_18 (i.val - 1098) (by omega)
    have he : 1098 + (i.val - 1098) = i.val := by omega
    simpa only [he] using h
  by_cases h19 : i.val < 1226
  · have h := (checkAll_spec _ _).mp checked_rows_19 (i.val - 1162) (by omega)
    have he : 1162 + (i.val - 1162) = i.val := by omega
    simpa only [he] using h
  by_cases h20 : i.val < 1290
  · have h := (checkAll_spec _ _).mp checked_rows_20 (i.val - 1226) (by omega)
    have he : 1226 + (i.val - 1226) = i.val := by omega
    simpa only [he] using h
  by_cases h21 : i.val < 1354
  · have h := (checkAll_spec _ _).mp checked_rows_21 (i.val - 1290) (by omega)
    have he : 1290 + (i.val - 1290) = i.val := by omega
    simpa only [he] using h
  by_cases h22 : i.val < 1418
  · have h := (checkAll_spec _ _).mp checked_rows_22 (i.val - 1354) (by omega)
    have he : 1354 + (i.val - 1354) = i.val := by omega
    simpa only [he] using h
  by_cases h23 : i.val < 1482
  · have h := (checkAll_spec _ _).mp checked_rows_23 (i.val - 1418) (by omega)
    have he : 1418 + (i.val - 1418) = i.val := by omega
    simpa only [he] using h
  by_cases h24 : i.val < 1546
  · have h := (checkAll_spec _ _).mp checked_rows_24 (i.val - 1482) (by omega)
    have he : 1482 + (i.val - 1482) = i.val := by omega
    simpa only [he] using h
  by_cases h25 : i.val < 1610
  · have h := (checkAll_spec _ _).mp checked_rows_25 (i.val - 1546) (by omega)
    have he : 1546 + (i.val - 1546) = i.val := by omega
    simpa only [he] using h
  by_cases h26 : i.val < 1674
  · have h := (checkAll_spec _ _).mp checked_rows_26 (i.val - 1610) (by omega)
    have he : 1610 + (i.val - 1610) = i.val := by omega
    simpa only [he] using h
  by_cases h27 : i.val < 1738
  · have h := (checkAll_spec _ _).mp checked_rows_27 (i.val - 1674) (by omega)
    have he : 1674 + (i.val - 1674) = i.val := by omega
    simpa only [he] using h
  by_cases h28 : i.val < 1802
  · have h := (checkAll_spec _ _).mp checked_rows_28 (i.val - 1738) (by omega)
    have he : 1738 + (i.val - 1738) = i.val := by omega
    simpa only [he] using h
  by_cases h29 : i.val < 1866
  · have h := (checkAll_spec _ _).mp checked_rows_29 (i.val - 1802) (by omega)
    have he : 1802 + (i.val - 1802) = i.val := by omega
    simpa only [he] using h
  by_cases h30 : i.val < 1930
  · have h := (checkAll_spec _ _).mp checked_rows_30 (i.val - 1866) (by omega)
    have he : 1866 + (i.val - 1866) = i.val := by omega
    simpa only [he] using h
  by_cases h31 : i.val < 1994
  · have h := (checkAll_spec _ _).mp checked_rows_31 (i.val - 1930) (by omega)
    have he : 1930 + (i.val - 1930) = i.val := by omega
    simpa only [he] using h
  by_cases h32 : i.val < 2058
  · have h := (checkAll_spec _ _).mp checked_rows_32 (i.val - 1994) (by omega)
    have he : 1994 + (i.val - 1994) = i.val := by omega
    simpa only [he] using h
  by_cases h33 : i.val < 2122
  · have h := (checkAll_spec _ _).mp checked_rows_33 (i.val - 2058) (by omega)
    have he : 2058 + (i.val - 2058) = i.val := by omega
    simpa only [he] using h
  by_cases h34 : i.val < 2186
  · have h := (checkAll_spec _ _).mp checked_rows_34 (i.val - 2122) (by omega)
    have he : 2122 + (i.val - 2122) = i.val := by omega
    simpa only [he] using h
  by_cases h35 : i.val < 2250
  · have h := (checkAll_spec _ _).mp checked_rows_35 (i.val - 2186) (by omega)
    have he : 2186 + (i.val - 2186) = i.val := by omega
    simpa only [he] using h
  by_cases h36 : i.val < 2314
  · have h := (checkAll_spec _ _).mp checked_rows_36 (i.val - 2250) (by omega)
    have he : 2250 + (i.val - 2250) = i.val := by omega
    simpa only [he] using h
  by_cases h37 : i.val < 2378
  · have h := (checkAll_spec _ _).mp checked_rows_37 (i.val - 2314) (by omega)
    have he : 2314 + (i.val - 2314) = i.val := by omega
    simpa only [he] using h
  by_cases h38 : i.val < 2442
  · have h := (checkAll_spec _ _).mp checked_rows_38 (i.val - 2378) (by omega)
    have he : 2378 + (i.val - 2378) = i.val := by omega
    simpa only [he] using h
  by_cases h39 : i.val < 2506
  · have h := (checkAll_spec _ _).mp checked_rows_39 (i.val - 2442) (by omega)
    have he : 2442 + (i.val - 2442) = i.val := by omega
    simpa only [he] using h
  by_cases h40 : i.val < 2570
  · have h := (checkAll_spec _ _).mp checked_rows_40 (i.val - 2506) (by omega)
    have he : 2506 + (i.val - 2506) = i.val := by omega
    simpa only [he] using h
  by_cases h41 : i.val < 2634
  · have h := (checkAll_spec _ _).mp checked_rows_41 (i.val - 2570) (by omega)
    have he : 2570 + (i.val - 2570) = i.val := by omega
    simpa only [he] using h
  by_cases h42 : i.val < 2698
  · have h := (checkAll_spec _ _).mp checked_rows_42 (i.val - 2634) (by omega)
    have he : 2634 + (i.val - 2634) = i.val := by omega
    simpa only [he] using h
  by_cases h43 : i.val < 2762
  · have h := (checkAll_spec _ _).mp checked_rows_43 (i.val - 2698) (by omega)
    have he : 2698 + (i.val - 2698) = i.val := by omega
    simpa only [he] using h
  have h := (checkAll_spec _ _).mp checked_rows_44 (i.val - 2762) (by omega)
  have he : 2762 + (i.val - 2762) = i.val := by omega
  simpa only [he] using h

theorem catalogue_covers : dimensionSix.Covers := by
  apply dimensionSix.covers_of_bit_rows (by decide +kernel)
  intro i
  exact (dimensionSix.rowCheck_sound i (all_rows_checked i)).2.2.1

theorem catalogue_proper : dimensionSix.Proper := by
  apply dimensionSix.proper_of_bit_rows
  · intro i
    exact ⟨(dimensionSix.rowCheck_sound i (all_rows_checked i)).1,
      (dimensionSix.rowCheck_sound i (all_rows_checked i)).2.1⟩
  · intro i
    exact (dimensionSix.rowCheck_sound i (all_rows_checked i)).2.2.2.1
  · intro i
    exact (dimensionSix.rowCheck_sound i (all_rows_checked i)).2.2.2.2

theorem fifteen_colorable : graph.Colorable 15 :=
  dimensionSix.colorable catalogue_covers catalogue_proper

def cliqueIndex (i : Fin 15) : Fin dimensionSix.count :=
  ⟨cliqueIndices[i.val]! % dimensionSix.count, Nat.mod_lt _ dimensionSix.positive⟩

instance (U : Finset Vector) : Decidable (IsSpace U) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem clique_valid : ∀ i : Fin 15,
    IsSpace (dimensionSix.space (cliqueIndex i)) ∧
    dimensionSix.space (cliqueIndex i) ≠ {0} := by decide +kernel

def cliqueVertex (i : Fin 15) : Vertex :=
  ⟨dimensionSix.space (cliqueIndex i), clique_valid i⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem clique_adjacent : ∀ i j : Fin 15, i ≠ j →
    graph.Adj (cliqueVertex i) (cliqueVertex j) := by decide +kernel

/-- The full graph on all nonzero binary subspaces in six coordinates. -/
theorem chromatic_number_six : graph.chromaticNumber = 15 := by
  apply le_antisymm fifteen_colorable.chromaticNumber_le
  exact SimpleGraph.le_chromaticNumber_of_pairwise_adj (by simp) cliqueVertex
    (fun i j h => clique_adjacent i j h)

/-- The complete supplied certificate reaches every actual nonzero binary
Submodule, including the whole space. The mask theorem is used through the
proved graph isomorphism, rather than identified with the target by name. -/
theorem actual_chromatic_number_six :
    (D5.S3.Combinatorics.Orthogonality.NikandishClique.orthogonalityGraph 6).chromaticNumber = 15 := by
  exact (SimpleGraph.chromaticNumber_congr
    D5.S3.Combinatorics.Orthogonality.SixBitSubmoduleBridge.graphIso).symm.trans
      chromatic_number_six

#print axioms Catalogue.complete
#print axioms Catalogue.colorable
#print axioms chromatic_number_six
#print axioms actual_chromatic_number_six

end BinaryOrthogonality
