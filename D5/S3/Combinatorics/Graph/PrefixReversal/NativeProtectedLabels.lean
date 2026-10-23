/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The last two selected labels are a fixed protected pair under actual frame growth. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels

open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply

/-- The penultimate selected label is fixed when new labels are prepended. -/
def protectedP {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k) : Fin (m + 1) :=
  F.selected[k - 2]'(by rw [F.selected_length]; omega)

/-- The final selected label is fixed by the same actual frame growth. -/
def protectedQ {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k) : Fin (m + 1) :=
  F.selected[k - 1]'(by rw [F.selected_length]; omega)

/-- The distinguished pair contains two different actual selected labels;
neither can be the terminal or any label in the independent base. -/
theorem native_protected_labels {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k) :
    protectedP F hk ≠ protectedQ F hk ∧
      protectedP F hk ∈ F.selected ∧ protectedQ F hk ∈ F.selected ∧
      protectedP F hk ∉ F.base ∧ protectedQ F hk ∉ F.base ∧
      protectedP F hk ≠ F.terminal ∧ protectedQ F hk ≠ F.terminal := by
  have hprefix := (List.nodup_append'.mp F.full_nodup).1
  have hs := (List.nodup_append'.mp hprefix).1
  have hbase := (List.nodup_append'.mp hprefix).2.2
  have ht := (List.nodup_append'.mp F.full_nodup).2.2
  have hp : protectedP F hk ∈ F.selected := List.getElem_mem _
  have hq : protectedQ F hk ∈ F.selected := List.getElem_mem _
  refine ⟨?_, hp, hq, ?_, ?_, ?_, ?_⟩
  · intro he
    have hi := hs.getElem_inj_iff.mp he
    omega
  · exact fun hb => List.disjoint_left.mp hbase hp hb
  · exact fun hb => List.disjoint_left.mp hbase hq hb
  · intro he
    exact List.disjoint_left.mp ht (List.mem_append.mpr (Or.inl hp))
      (by simpa only [List.mem_singleton] using he)
  · intro he
    exact List.disjoint_left.mp ht (List.mem_append.mpr (Or.inl hq))
      (by simpa only [List.mem_singleton] using he)

/-- The native next-frame constructor prepends exactly one label. Both
protected labels keep their literal identities, without relabelling. -/
theorem native_protected_labels_prepend {m k : ℕ} (F : SupplyFrame m k)
    (G : SupplyFrame m (k + 1)) (hk : 2 ≤ k) (u : Fin (m + 1))
    (hselected : G.selected = u :: F.selected) :
    protectedP G (by omega) = protectedP F hk ∧
      protectedQ G (by omega) = protectedQ F hk := by
  constructor
  · simp only [protectedP, hselected,
      show k + 1 - 2 = (k - 2) + 1 by omega, List.getElem_cons_succ]
  · simp only [protectedQ, hselected,
      show k + 1 - 1 = (k - 1) + 1 by omega, List.getElem_cons_succ]

/-- Rotating a child base leaves the selected list unchanged. This
identity needs no agreement between independently chosen cycle witnesses. -/
theorem native_protected_labels_same_selected {m k : ℕ} (F G : SupplyFrame m k)
    (hk : 2 ≤ k) (hselected : G.selected = F.selected) :
    protectedP G hk = protectedP F hk ∧ protectedQ G hk = protectedQ F hk := by
  simp only [protectedP, protectedQ, hselected, and_self]

#print axioms native_protected_labels
#print axioms native_protected_labels_prepend
#print axioms native_protected_labels_same_selected

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
