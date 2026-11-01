/- GID: D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Complete powers and triangle-free complements have exact native maximal-independent spectra. -/
import D5.S3.Combinatorics.Graph.Walks.FiniteDistancePower

set_option autoImplicit false
namespace FiniteDistancePower
open SimpleGraph Finset
open WellCoveredPowerCliqueProduct (IsMaximalIndep WellCovered power)
open MatchingCliqueCycle (spectrum)
noncomputable section
variable {V W : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Complement transport uses the existing embedding-complement supplier and the same vertex bijection. -/
def complementIso {X Y : Type} {J : SimpleGraph X} {K : SimpleGraph Y}
    (e : J ≃g K) : Jᶜ ≃g Kᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := (SimpleGraph.Embedding.complEquiv e.toEmbedding).map_rel_iff'

private theorem edist_hom_le {X Y : Type} {J : SimpleGraph X} {K : SimpleGraph Y}
    (f : J →g K) (u v : X) : K.edist (f u) (f v) ≤ J.edist u v := by
  by_cases hr : J.Reachable u v
  · obtain ⟨p,hp⟩ := hr.exists_walk_length_eq_edist
    calc
      K.edist (f u) (f v) ≤ ((p.map f).length : ℕ∞) := (p.map f).edist_le
      _ = J.edist u v := by simpa only [SimpleGraph.Walk.length_map] using hp
  · rw [J.edist_eq_top_of_not_reachable hr]
    exact le_top

/-- The same length-preserving native walk maps also preserve extended distance. -/
theorem edist_iso {X Y : Type} {J : SimpleGraph X} {K : SimpleGraph Y}
    (e : J ≃g K) (u v : X) : K.edist (e u) (e v) = J.edist u v := by
  apply le_antisymm
  · exact edist_hom_le e.toHom u v
  · have h := edist_hom_le e.symm.toHom (e u) (e v)
    change J.edist (e.symm (e u)) (e.symm (e v)) ≤ K.edist (e u) (e v) at h
    simpa only [e.symm_apply_apply] using h

/-- Natural distance transport follows without imposing connectedness on either graph. -/
theorem dist_iso {X Y : Type} {J : SimpleGraph X} {K : SimpleGraph Y}
    (e : J ≃g K) (u v : X) : K.dist (e u) (e v) = J.dist u v := by
  exact congrArg ENat.toNat (edist_iso e u v)

/-- Native graph isomorphisms retain the exact diameter, including the disconnected junk value. -/
theorem diam_iso {X Y : Type} {J : SimpleGraph X} {K : SimpleGraph Y}
    (e : J ≃g K) : K.diam = J.diam := by
  apply congrArg ENat.toNat
  rw [SimpleGraph.ediam_eq_iSup_iSup_edist,SimpleGraph.ediam_eq_iSup_iSup_edist]
  apply le_antisymm
  · apply iSup_le
    intro u
    apply iSup_le
    intro v
    obtain ⟨x,rfl⟩ := e.surjective u
    obtain ⟨y,rfl⟩ := e.surjective v
    rw [edist_iso]
    exact le_iSup_of_le x (le_iSup_of_le y le_rfl)
  · apply iSup_le
    intro u
    apply iSup_le
    intro v
    rw [← edist_iso e u v]
    exact le_iSup_of_le (e u) (le_iSup_of_le (e v) le_rfl)

/-- The spectrum of a nonempty complete graph consists exactly of singleton vertex sets. -/
theorem spectrum_top [Nonempty V] : spectrum (⊤ : SimpleGraph V) = {1} := by
  classical
  ext k
  constructor
  · rintro ⟨I,hI,rfl⟩
    have hne : I.Nonempty := by
      by_contra h
      have hempty : I = ∅ := not_nonempty_iff_eq_empty.mp h
      obtain ⟨v⟩ := ‹Nonempty V›
      obtain ⟨u,hu,_⟩ := hI.2 v (by simp [hempty])
      simpa [hempty] using hu
    obtain ⟨u,hu⟩ := hne
    have hsingle : I = {u} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hu,?_⟩
      intro v hv
      by_contra h
      exact hI.1 v hv u hu h (by exact h)
    simp [hsingle]
  · intro hk
    have hk' : k=1 := hk
    subst k
    obtain ⟨v⟩ := ‹Nonempty V›
    refine ⟨{v},⟨?_,?_⟩,by simp⟩
    · intro x hx y hy hne _
      simp only [mem_singleton] at hx hy
      exact hne (hx.trans hy.symm)
    · intro x hx
      exact ⟨v,by simp,by simpa using hx⟩

/-- The frozen connected power is complete as soon as the exponent reaches the diameter. -/
theorem power_eq_top_of_diam_le (hc : G.Connected) {d : ℕ} (hd : G.diam ≤ d) :
    power G d = ⊤ := by
  letI : Nonempty V := hc.nonempty
  ext u v
  change (u ≠ v ∧ G.dist u v ≤ d) ↔ u ≠ v
  exact ⟨And.left,fun h => ⟨h,(G.dist_le_diam (connected_iff_ediam_ne_top.mp hc)).trans hd⟩⟩

/-- A graph is well-covered exactly when its attained native spectrum is a subsingleton. -/
theorem wellCovered_iff_spectrum : WellCovered G ↔ (spectrum G).Subsingleton := by
  constructor
  · intro h k hk l hl
    obtain ⟨I,hI,rfl⟩ := hk
    obtain ⟨J,hJ,rfl⟩ := hl
    exact h I J hI hJ
  · intro h I J hI hJ
    exact h ⟨I,hI,rfl⟩ ⟨J,hJ,rfl⟩

/-- Any triangle-free graph with no isolated vertices has complement spectrum exactly `{2}`. -/
theorem spectrum_complement_triangleFree [Nonempty V]
    (hneighbor : ∀ u : V, ∃ v, G.Adj u v)
    (htriangle : ∀ u v w : V, G.Adj u v → G.Adj v w → G.Adj w u → False) :
    spectrum Gᶜ = {2} := by
  classical
  have hcard (I : Finset V) (hI : IsMaximalIndep Gᶜ I) : I.card = 2 := by
    have hclique (x : V) (hx : x∈I) (y : V) (hy : y∈I) (hne : x≠y) : G.Adj x y := by
      by_contra hn
      exact hI.1 x hx y hy hne ⟨hne,hn⟩
    have hne : I.Nonempty := by
      by_contra h
      have hempty := not_nonempty_iff_eq_empty.mp h
      obtain ⟨v⟩ := ‹Nonempty V›
      obtain ⟨u,hu,_⟩ := hI.2 v (by simp [hempty])
      simpa [hempty] using hu
    obtain ⟨u,hu⟩ := hne
    have hother : ∃ v∈I, v≠u := by
      by_contra hn
      have hsingle : I={u} := eq_singleton_iff_unique_mem.mpr ⟨hu,by simpa using hn⟩
      obtain ⟨v,huv⟩ := hneighbor u
      have hv : v∉I := by simpa [hsingle] using huv.ne.symm
      obtain ⟨w,hw,ha⟩ := hI.2 v hv
      have hw' : w=u := by simpa [hsingle] using hw
      exact ha.2 (hw' ▸ huv.symm)
    obtain ⟨v,hv,hvu⟩ := hother
    have hIeq : I={u,v} := by
      apply le_antisymm
      · intro w hw
        by_cases hwu : w=u
        · simp [hwu]
        by_cases hwv : w=v
        · simp [hwv]
        exact (htriangle u v w (hclique u hu v hv hvu.symm)
          (hclique v hv w hw (Ne.symm hwv)) (hclique w hw u hu hwu)).elim
      · intro w hw
        simp only [Finset.mem_insert,Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hu
        · exact hv
    rw [hIeq,card_pair hvu.symm]
  ext k
  constructor
  · rintro ⟨I,hI,rfl⟩
    exact hcard I hI
  · intro hk
    have hk' : k=2 := hk
    subst k
    obtain ⟨I,hI⟩ := Gᶜ.maximumIndepSet_exists
    have hm := (CayleySquare.maximal_iff _ _).mpr (hI.isMaximalIndepSet I)
    exact ⟨I,hm,hcard I hm⟩

end
end FiniteDistancePower
