/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/CleanRoots
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: A cut smaller than host order leaves a label with no one-label outside cut support. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.Connectivity

/-! Clean roots are counted using the supports of members of one fixed cut. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}

/-- The host labels whose singleton configurations belong to the cut. -/
noncomputable def deletedLabels (C : Finset (Configuration H)) : Finset V := by
  classical
  exact Finset.univ.filter fun v => (⟨{v}, visible_singleton H v⟩ : Configuration H) ∈ C

/-- A surviving label with no cut configuration supported only on it outside deleted labels. -/
def CleanRoot (C : Finset (Configuration H)) (w : V) : Prop :=
  w ∉ deletedLabels C ∧ ∀ T ∈ C, T.val \ deletedLabels C ≠ {w}

theorem exists_cleanRoot (C : Finset (Configuration H))
    (hc : C.card < Fintype.card V) : ∃ w, CleanRoot C w := by
  classical
  by_contra hn
  have hdirty : ∀ w, w ∉ deletedLabels C →
      ∃ T ∈ C, T.val \ deletedLabels C = {w} := by
    intro w hw
    have hnc : ¬ CleanRoot C w := fun h => hn ⟨w, h⟩
    have hex : ¬ ∀ T ∈ C, T.val \ deletedLabels C ≠ {w} := fun h => hnc ⟨hw, h⟩
    push_neg at hex
    exact hex
  have hpay : ∀ w, ∃ T ∈ C,
      if w ∈ deletedLabels C then T.val = {w} else T.val \ deletedLabels C = {w} := by
    intro w
    by_cases hw : w ∈ deletedLabels C
    · refine ⟨⟨{w}, visible_singleton H w⟩, ?_, by simp [hw]⟩
      simpa only [deletedLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hw
    · obtain ⟨T, hTC, hTw⟩ := hdirty w hw
      exact ⟨T, hTC, by simpa [hw] using hTw⟩
  choose f hfC hf using hpay
  have hinj : Function.Injective f := by
    intro w z he
    have hv := congrArg Subtype.val he
    by_cases hw : w ∈ deletedLabels C <;> by_cases hz : z ∈ deletedLabels C
    · have hfw : (f w).val = {w} := by simpa [hw] using hf w
      have hfz : (f z).val = {z} := by simpa [hz] using hf z
      rw [hfw, hfz] at hv
      exact Finset.singleton_injective hv
    · have hfw : (f w).val = {w} := by simpa [hw] using hf w
      have hfz : (f z).val \ deletedLabels C = {z} := by simpa [hz] using hf z
      rw [← hv, hfw] at hfz
      have hempty : ({w} : Finset V) \ deletedLabels C = ∅ := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
        intro h
        simpa [h] using hw
      rw [hempty] at hfz
      simp at hfz
    · have hfw : (f w).val \ deletedLabels C = {w} := by simpa [hw] using hf w
      have hfz : (f z).val = {z} := by simpa [hz] using hf z
      rw [hv, hfz] at hfw
      have hempty : ({z} : Finset V) \ deletedLabels C = ∅ := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
        intro h
        simpa [h] using hz
      rw [hempty] at hfw
      simp at hfw
    · have hfw : (f w).val \ deletedLabels C = {w} := by simpa [hw] using hf w
      have hfz : (f z).val \ deletedLabels C = {z} := by simpa [hz] using hf z
      rw [hv, hfz] at hfw
      exact (Finset.singleton_injective hfw).symm
  have hsub : Finset.univ.image f ⊆ C := by
    intro T hT
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hT
    exact hfC w
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ] at hcard
  omega


private theorem clean_support_survives (C : Finset (Configuration H)) {w : V}
    (hw : CleanRoot C w) (T : Configuration H)
    (hT : T.val \ deletedLabels C = {w}) : T ∉ C :=
  fun hTC => hw.2 T hTC hT

private theorem clean_pair_survives (hH : H.Connected) (C : Finset (Configuration H))
    {u w : V} (hw : CleanRoot C w) (hu : u ∈ deletedLabels C) :
    (⟨{u, w}, visible_pair hH u w⟩ : Configuration H) ∉ C := by
  apply clean_support_survives C hw
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  have := hw.1
  aesop

theorem clean_root_pair_nonvisible (hH : H.Connected)
    (C : Finset (Configuration H)) (s : Configuration H) {u v w : V}
    (huv : u ≠ v) (hw : CleanRoot C w)
    (hu : u ∈ deletedLabels C) (hv : v ∈ deletedLabels C)
    (hB : CutReach (reconfiguration H) C s ⟨{u, v}, visible_pair hH u v⟩)
    (hwout : ¬ CutReach (reconfiguration H) C s ⟨{w}, visible_singleton H w⟩) :
    ¬ Visible H {u, v, w} := by
  intro hT
  have huw : u ≠ w := fun h => hw.1 (h ▸ hu)
  have hvw : v ≠ w := fun h => hw.1 (h ▸ hv)
  let T : Configuration H := ⟨{u, v, w}, hT⟩
  have hTC : T ∉ C := by
    apply clean_support_survives C hw
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    have := hw.1
    aesop
  have hBT : (reconfiguration H).Adj ⟨{u, v}, visible_pair hH u v⟩ T := by
    change MixedMove H {u, v} {u, v, w}
    have hh := mixedMove_insert H ({u, v} : Finset V) (x := w) (by simp [huw.symm, hvw.symm])
    convert hh using 1 <;> ext z <;> simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto
  have hTP : (reconfiguration H).Adj T ⟨{u, w}, visible_pair hH u w⟩ := by
    change MixedMove H {u, v, w} {u, w}
    have hh := mixedMove_erase H ({u, v, w} : Finset V) (x := v) (by simp)
    have he : ({u, v, w} : Finset V).erase v = {u, w} := by
      ext z
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [he] at hh
    exact hh
  have hPW : (reconfiguration H).Adj ⟨{u, w}, visible_pair hH u w⟩
      ⟨{w}, visible_singleton H w⟩ := by
    change MixedMove H {u, w} {w}
    have hh := mixedMove_erase H ({u, w} : Finset V) (x := u) (by simp)
    have he : ({u, w} : Finset V).erase u = {w} := by
      ext z
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [he] at hh
    exact hh
  have hwC : (⟨{w}, visible_singleton H w⟩ : Configuration H) ∉ C := by
    intro h
    apply hw.1
    simpa [deletedLabels] using h
  exact hwout (cutReach_step (cutReach_step (cutReach_step hB hBT hTC) hTP
    (clean_pair_survives hH C hw hu)) hPW hwC)

theorem clean_root_pair_nonadjacent (hH : H.Connected)
    (C : Finset (Configuration H)) (s : Configuration H) {u v w : V}
    (huv : u ≠ v) (hw : CleanRoot C w)
    (hu : u ∈ deletedLabels C) (hv : v ∈ deletedLabels C)
    (hB : CutReach (reconfiguration H) C s ⟨{u, v}, visible_pair hH u v⟩)
    (hwout : ¬ CutReach (reconfiguration H) C s ⟨{w}, visible_singleton H w⟩) :
    ¬ H.Adj u w := by
  intro huwH
  have huw : u ≠ w := fun h => hw.1 (h ▸ hu)
  have hvw : v ≠ w := fun h => hw.1 (h ▸ hv)
  have hBP : (reconfiguration H).Adj ⟨{u, v}, visible_pair hH u v⟩
      ⟨{v, w}, visible_pair hH v w⟩ := by
    change MixedMove H {u, v} {v, w}
    refine ⟨?_, Or.inr ⟨u, w, ?_, ?_, huwH⟩⟩
    · intro he
      have hm : u ∈ ({v, w} : Finset V) := he ▸ (by simp)
      simpa [huv, huw] using hm
    · ext z
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · ext z
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      aesop
  have hPW : (reconfiguration H).Adj ⟨{v, w}, visible_pair hH v w⟩
      ⟨{w}, visible_singleton H w⟩ := by
    change MixedMove H {v, w} {w}
    have hh := mixedMove_erase H ({v, w} : Finset V) (x := v) (by simp)
    have he : ({v, w} : Finset V).erase v = {w} := by
      ext z
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [he] at hh
    exact hh
  have hwC : (⟨{w}, visible_singleton H w⟩ : Configuration H) ∉ C := by
    intro h
    apply hw.1
    simpa [deletedLabels] using h
  exact hwout (cutReach_step (cutReach_step hB hBP (clean_pair_survives hH C hw hv)) hPW hwC)

end D5.S3.Combinatorics.Graph.MutualVisibility
