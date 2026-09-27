/- GID: D5/S3/Combinatorics/Graph/ColoredPrivateResidual
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ColoredPrivateResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Positive private deletion preserves mixed degrees and excludes singleton leaves. -/

import D5.S3.Combinatorics.Graph.ColoredReciprocalDeletion

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ColoredPrivateResidual

open Finset
open D5.S3.Combinatorics.Graph.ColoredReciprocalDeletion

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Deleting a nonempty set of positive-debt private mixed vertices preserves
degree two at mixed vertices and leaves no singleton color class of degree one. -/
theorem positive_private_residual
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 3)) (W : Finset V)
    (hW : W.Nonempty)
    (hmixed : ∀ w ∈ W, Mixed G c w)
    (hdegree : ∀ v, Mixed G c v → G.degree v = 2)
    (hprivate : ∀ w ∈ W, ∀ v, G.Adj w v →
      ¬ Mixed G c v ∧ ∀ u, G.Adj v u → Mixed G c u → u = w)
    (hpositive : ∀ w ∈ W, 0 < debt G w) :
    (∀ v : {v // v ∉ W},
      Mixed (G.induce {v | v ∉ W}) (fun x => c x.val) v →
      (G.induce {v | v ∉ W}).degree v = 2) ∧
    (∀ v : {v // v ∉ W},
      (Finset.univ.filter (fun x : {v // v ∉ W} => c x.val = c v.val)) = {v} →
      (G.induce {v | v ∉ W}).degree v ≠ 1) := by
  classical
  constructor
  · intro v hv
    obtain ⟨a, b, ha, hb, hab⟩ := hv
    have hm : Mixed G c v.val := ⟨a.val, b.val, ha, hb, hab⟩
    have hkeep : G.neighborSet v.val ⊆ {v | v ∉ W} := by
      intro u hu huW
      exact (hprivate u huW v.val hu.symm).1 hm
    exact (G.degree_induce_of_neighborSet_subset (s := {v | v ∉ W}) (v := v) hkeep).trans
      (hdegree v.val hm)
  · obtain ⟨w, hw⟩ := hW
    obtain ⟨r, z, hwr, hwz, hrz⟩ := hmixed w hw
    have hrz_ne : r ≠ z := fun h => hrz (congrArg c h)
    have hnw : G.neighborFinset w = {r, z} := by
      apply (eq_of_subset_of_card_le ?_ ?_).symm
      · simpa only [insert_subset_iff, singleton_subset_iff, G.mem_neighborFinset]
          using And.intro hwr hwz
      · simp [hrz_ne, hdegree w (hmixed w hw)]
    have hp := hpositive w hw
    have hdebt : debt G w = 1 / 6 - (1 / 2 : ℚ) *
        (1 / (G.degree r + 1 : ℚ) + 1 / (G.degree z + 1 : ℚ)) := by
      simp [debt, hnw, hrz_ne]
    rw [hdebt] at hp
    have strict_degree (d e : ℕ)
        (h : (0 : ℚ) < 1 / 6 - 1 / 2 * (1 / (d + 1) + 1 / (e + 1))) :
        3 ≤ d := by
      have hd : (0 : ℚ) < d + 1 := by positivity
      have he : (0 : ℚ) < 1 / (e + 1 : ℚ) := by positivity
      have hlt : (1 : ℚ) / (d + 1) < 1 / 3 := by linarith
      have hcross := (div_lt_div_iff₀ hd (by norm_num : (0 : ℚ) < 3)).mp hlt
      have hgt : (2 : ℚ) < d := by linarith
      have : 2 < d := by exact_mod_cast hgt
      omega
    have hdr := strict_degree (G.degree r) (G.degree z) hp
    have hdz := strict_degree (G.degree z) (G.degree r) (by simpa [add_comm] using hp)
    have survive (x : V) (hx : G.Adj w x) : x ∉ W :=
      fun hxW => (hprivate w hw x hx).1 (hmixed x hxW)
    have residual_degree (x : V) (hx : G.Adj w x) :
        (G.induce {v | v ∉ W}).degree ⟨x, survive x hx⟩ + 1 = G.degree x := by
      have hinter : G.neighborFinset x ∩ ({v | v ∉ W} : Set V).toFinset =
          (G.neighborFinset x).erase w := by
        ext u
        simp only [mem_inter, Set.mem_toFinset, mem_erase, G.mem_neighborFinset]
        constructor
        · rintro ⟨hxu, hu⟩
          exact ⟨fun he => hu (he ▸ hw), hxu⟩
        · rintro ⟨huw, hxu⟩
          refine ⟨hxu, fun huW => ?_⟩
          exact huw ((hprivate w hw x hx).2 u hxu (hmixed u huW))
      have hc := congrArg Finset.card (G.map_neighborFinset_induce (s := {v | v ∉ W})
        (⟨x, survive x hx⟩ : {v // v ∉ W}))
      simp only [card_map, SimpleGraph.card_neighborFinset_eq_degree] at hc
      rw [hc, hinter]
      exact card_erase_add_one ((G.mem_neighborFinset x w).mpr hx.symm)
    let r' : {v // v ∉ W} := ⟨r, survive r hwr⟩
    let z' : {v // v ∉ W} := ⟨z, survive z hwz⟩
    have hdr' : 2 ≤ (G.induce {v | v ∉ W}).degree r' := by
      have := residual_degree r hwr
      change (G.induce {v | v ∉ W}).degree r' + 1 = G.degree r at this
      omega
    have hdz' : 2 ≤ (G.induce {v | v ∉ W}).degree z' := by
      have := residual_degree z hwz
      change (G.induce {v | v ∉ W}).degree z' + 1 = G.degree z at this
      omega
    have hcolors : ({c w, c r, c z} : Finset (Fin 3)) = univ := by
      apply eq_univ_of_card
      simp [c.valid hwr, c.valid hwz, hrz]
    intro v hs hv
    have unique (u : {v // v ∉ W}) (hu : c u.val = c v.val) : u = v := by
      exact mem_singleton.mp (hs ▸ (mem_filter.mpr ⟨mem_univ u, hu⟩))
    have hc : c v.val = c w ∨ c v.val = c r ∨ c v.val = c z := by
      have := hcolors.symm ▸ mem_univ (c v.val)
      simpa only [mem_insert, mem_singleton] using this
    rcases hc with hcw | hcr | hcz
    · have hsub : (G.induce {v | v ∉ W}).neighborFinset r' ⊆
          univ.filter (fun x : {v // v ∉ W} => c x.val = c v.val) := by
        intro u hu
        have hru : G.Adj r u.val := ((G.induce {v | v ∉ W}).mem_neighborFinset r' u).mp hu
        have huc : c u.val = c w := by
          by_contra hne
          exact (hprivate w hw r hwr).1 ⟨u.val, w, hru, hwr.symm, hne⟩
        exact mem_filter.mpr ⟨mem_univ u, huc.trans hcw.symm⟩
      have hb := card_le_card hsub
      rw [hs, card_singleton, SimpleGraph.card_neighborFinset_eq_degree] at hb
      omega
    · have he : r' = v := unique r' hcr.symm
      rw [he] at hdr'
      omega
    · have he : z' = v := unique z' hcz.symm
      rw [he] at hdz'
      omega

end D5.S3.Combinatorics.Graph.ColoredPrivateResidual
