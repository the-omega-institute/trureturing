/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeKernelSupport]
   utility: none
   digest: The binary image of a partial shell records the cut between selected and omitted coordinates. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeKernelSupport
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

/-! In characteristic two, the image of a partial shell records the cut
between selected and omitted coordinate directions. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubePartialShell

open Finset
open scoped BigOperators
open BalancedCriticalSpectrum (Q flip)
open BalancedCubeGirth (flip_comm)
open BalancedCubeComponentBoundary (flip_injective)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel (adjacency)
open BinaryCubeKernelSupport (binarySites)

/-- Indicator of a selected part of the open shell about a vertex. -/
def shellWord {n : ℕ} (c : Q n) (S : Finset (Fin n)) (x : Q n) : ZMod 2 :=
  if x ∈ S.image (flip c) then 1 else 0

private theorem one_flip_value {n : ℕ} (c : Q n) (S : Finset (Fin n)) (j : Fin n) :
    shellWord c S (flip c j) = if j ∈ S then 1 else 0 := by
  have hm : flip c j ∈ S.image (flip c) ↔ j ∈ S := by
    simp only [mem_image]
    exact ⟨fun ⟨i, hi, hij⟩ => (flip_injective c hij) ▸ hi, fun hj => ⟨j, hj, rfl⟩⟩
  simp only [shellWord, hm]

private theorem two_flip_diff {n : ℕ} (c : Q n) {a b : Fin n} (hab : a ≠ b) :
    (univ.filter fun i => flip (flip c a) b i ≠ c i) = {a, b} := by
  ext i
  by_cases ha : i = a
  · subst i
    cases hc : c a <;> simp [BalancedCriticalSpectrum.flip, hab, hc]
  · by_cases hb : i = b
    · subst i
      cases hc : c b <;> simp [BalancedCriticalSpectrum.flip, hab.symm, hc]
    · have hflip : flip (flip c a) b i = c i := by
        simp [BalancedCriticalSpectrum.flip, Function.update_of_ne, ha, hb]
      simp [hflip, ha, hb]

private theorem double_flip_ne_center {n : ℕ} (c : Q n) {a b : Fin n} (hab : a ≠ b) :
    flip (flip c a) b ≠ c := by
  intro he
  have hc := congrFun he a
  cases h : c a <;> simp [BalancedCriticalSpectrum.flip, hab, h] at hc

private theorem double_flip_axes {n : ℕ} (c : Q n) {a b i j : Fin n}
    (hab : a ≠ b) (hij : i ≠ j)
    (he : flip (flip c a) b = flip (flip c i) j) :
    (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  have h : ({a, b} : Finset (Fin n)) = {i, j} := by
    rw [← two_flip_diff c hab, ← two_flip_diff c hij, he]
  have ha : a ∈ ({i, j} : Finset (Fin n)) := h ▸ by simp
  have hb : b ∈ ({i, j} : Finset (Fin n)) := h ▸ by simp
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hab (ha.trans hb.symm)).elim
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact (hab (ha.trans hb.symm)).elim

private theorem shellWord_off_double_flip {n : ℕ} (c : Q n) (S : Finset (Fin n))
    {a b j : Fin n} (hab : a ≠ b) (hja : j ≠ a) (hjb : j ≠ b) :
    shellWord c S (flip (flip (flip c a) b) j) = 0 := by
  have hnot : flip (flip (flip c a) b) j ∉ S.image (flip c) := by
    intro hm
    obtain ⟨i, _, he⟩ := mem_image.mp hm
    have he' : flip (flip c a) b = flip (flip c i) j := by
      rw [he, BalancedCriticalSpectrum.flip_flip]
    by_cases hij : i = j
    · subst i
      rw [BalancedCriticalSpectrum.flip_flip] at he'
      exact double_flip_ne_center c hab he'
    · rcases double_flip_axes c hab hij he' with ⟨_, e⟩ | ⟨e, _⟩
      · exact hjb e.symm
      · exact hja e.symm
  simp [shellWord, hnot]

private theorem adjacency_at_double_flip {n : ℕ} (c : Q n) (S : Finset (Fin n))
    {a b : Fin n} (hab : a ≠ b) :
    adjacency (shellWord c S) (flip (flip c a) b) =
      (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) := by
  rw [adjacency]
  rw [← Finset.sum_subset (show ({a, b} : Finset (Fin n)) ⊆ univ from subset_univ _)]
  · rw [sum_insert (by simp [hab]), sum_singleton]
    rw [flip_comm (flip c a) b a, BalancedCriticalSpectrum.flip_flip, BalancedCriticalSpectrum.flip_flip, one_flip_value, one_flip_value, add_comm]
  · intro j _ hj
    simp only [mem_insert, mem_singleton, not_or] at hj
    exact shellWord_off_double_flip c S hab hj.1 hj.2

private theorem adjacency_at_center {n : ℕ} (c : Q n) (S : Finset (Fin n)) :
    adjacency (shellWord c S) c = (S.card : ZMod 2) := by
  simp only [adjacency, one_flip_value]
  rw [← sum_filter]
  simp

private theorem off_center_exists {n : ℕ} (c : Q n) (S : Finset (Fin n)) {y : Q n}
    (hy : y ≠ c) (hne : adjacency (shellWord c S) y ≠ 0) :
    ∃ a ∈ S, ∃ b ∉ S, y = flip (flip c a) b := by
  have hnonzero : ∃ b : Fin n, shellWord c S (flip y b) ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Finset.sum_eq_zero fun b _ => h b)
  obtain ⟨b, hb⟩ := hnonzero
  have hm : flip y b ∈ S.image (flip c) := by
    by_contra hn
    exact hb (by simp [shellWord, hn])
  obtain ⟨a, ha, he⟩ := mem_image.mp hm
  have hyab : y = flip (flip c a) b := by rw [he, BalancedCriticalSpectrum.flip_flip]
  have hab : a ≠ b := by
    intro h
    subst b
    exact hy (by simpa only [BalancedCriticalSpectrum.flip_flip] using hyab)
  have hbS : b ∉ S := by
    intro hbS
    rw [hyab, adjacency_at_double_flip c S hab] at hne
    exact hne (by simp [ha, hbS, ZModModule.add_self])
  exact ⟨a, ha, b, hbS, hyab⟩

private theorem image_card {n : ℕ} (c : Q n) (S : Finset (Fin n)) :
    ((S.product Sᶜ).image (fun ab => flip (flip c ab.1) ab.2)).card =
      S.card * (n - S.card) := by
  classical
  rw [card_image_of_injOn]
  · calc
      _ = S.card * Sᶜ.card := Finset.card_product S Sᶜ
      _ = _ := by rw [Finset.card_compl, Fintype.card_fin]
  · intro a ha b hb he
    have haS := mem_product.mp ha
    have hbS := mem_product.mp hb
    have hna := mem_compl.mp haS.2
    have hnb := mem_compl.mp hbS.2
    have ha12 : a.1 ≠ a.2 := fun h => hna (h ▸ haS.1)
    have hb12 : b.1 ≠ b.2 := fun h => hnb (h ▸ hbS.1)
    rcases double_flip_axes c ha12 hb12 he with ⟨h₁, h₂⟩ | ⟨h₁, _⟩
    · exact Prod.ext h₁ h₂
    · exact (hnb (h₁ ▸ haS.1)).elim

/-- Away from the center, the nonzero binary image of a partial shell
has one site per selected-omitted coordinate pair. -/
theorem partial_shell_outside_card {n : ℕ} (c : Q n) (S : Finset (Fin n)) :
    ((binarySites (adjacency (shellWord c S))).erase c).card =
      S.card * (n - S.card) := by
  classical
  have himage : (binarySites (adjacency (shellWord c S))).erase c =
      (S.product Sᶜ).image (fun ab => flip (flip c ab.1) ab.2) := by
    ext y
    rw [mem_erase]
    constructor
    · rintro ⟨hy, hs⟩
      have hne : adjacency (shellWord c S) y ≠ 0 := (mem_filter.mp hs).2
      obtain ⟨a, ha, b, hb, rfl⟩ := off_center_exists c S hy hne
      exact mem_image.mpr ⟨(a, b), mem_product.mpr ⟨ha, mem_compl.mpr hb⟩, rfl⟩
    · intro hy
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp hy
      obtain ⟨ha, hb⟩ := mem_product.mp hab
      have hn := mem_compl.mp hb
      have hne : a ≠ b := fun h => hn (h ▸ ha)
      refine ⟨double_flip_ne_center c hne, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
      rw [adjacency_at_double_flip c S hne]
      simp [ha, hn]
  rw [himage, image_card]

/-- The remaining coefficient is at the center and is the parity of the
selected directions. Together these give the exact binary image weight. -/
theorem partial_shell_image_card {n : ℕ} (c : Q n) (S : Finset (Fin n)) :
    (binarySites (adjacency (shellWord c S))).card =
      S.card * (n - S.card) + S.card % 2 := by
  classical
  let image := binarySites (adjacency (shellWord c S))
  have hout : (image.erase c).card = S.card * (n - S.card) := partial_shell_outside_card c S
  by_cases hc : c ∈ image
  · rw [card_erase_of_mem hc] at hout
    have hs : (S.card : ZMod 2) ≠ 0 := by
      simpa only [adjacency_at_center] using (mem_filter.mp hc).2
    have hmod : S.card % 2 = 1 := by
      have hz : S.card % 2 ≠ 0 := by
        intro h
        exact hs ((ZMod.natCast_eq_zero_iff S.card 2).mpr (Nat.dvd_of_mod_eq_zero h))
      omega
    change image.card = _
    have hpos : 0 < image.card := card_pos.mpr ⟨c, hc⟩
    omega
  · rw [erase_eq_of_notMem hc] at hout
    have hs : (S.card : ZMod 2) = 0 := by
      by_contra h
      exact hc (mem_filter.mpr ⟨mem_univ _, by simpa only [adjacency_at_center] using h⟩)
    have hmod : S.card % 2 = 0 := Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff S.card 2).mp hs)
    simpa only [hmod, add_zero] using hout

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubePartialShell
