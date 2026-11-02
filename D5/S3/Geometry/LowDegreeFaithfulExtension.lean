/- GID: D5/S3/Geometry/LowDegreeFaithfulExtension
   generality: G
   mirror-B: D5/B/S3/Geometry/LowDegreeFaithfulExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: Restore low-degree vertices without moving a faithful partial placement. -/
module

public import D5.S3.Geometry.SphereSectionAvoidance
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.UnitDistance.Basic

/-! Fixed-placement restoration by choosing points on spheres and common
unit-distance loci. All forbidden sections and collisions are finite. -/

noncomputable section
public section

open Set Metric
open scoped InnerProductSpace

namespace D5.S3.Geometry.LowDegreeFaithfulExtension

local notation "E₅" => EuclideanSpace ℝ (Fin 5)

private theorem choose_no_neighbors {ι κ : Type*} [Finite ι] [Finite κ]
    (z : ι → E₅) (q : κ → E₅) :
    ∃ p : E₅, (∀ i, dist p (z i) ≠ 1) ∧ ∀ j, p ≠ q j := by
  let K : Submodule ℝ E₅ := ⊤
  have hd : 2 ≤ Module.finrank ℝ K := by simp [K]
  have : Nontrivial K := Module.finrank_pos_iff (R := ℝ) |>.mp (by omega)
  obtain ⟨w, hw⟩ := exists_norm_eq K (by norm_num : (0 : ℝ) ≤ 2)
  obtain ⟨w, _, _, hz, hq⟩ :=
    SphereSectionAvoidance.exists_on_affine_sphere_avoiding K hd 0
      (by norm_num : (0 : ℝ) < 2) isOpen_univ
      ⟨w, Set.mem_univ _, hw⟩ z q (by
        intro i _ heq
        nlinarith [sq_nonneg ‖z i - 0‖])
  exact ⟨(w : E₅), by simpa using hz, by simpa using hq⟩

private theorem choose_one_neighbor {ι κ : Type*} [Finite ι] [Finite κ]
    (b : E₅) (z : ι → E₅) (q : κ → E₅) (hz : ∀ i, z i ≠ b) :
    ∃ p : E₅, dist p b = 1 ∧ (∀ i, dist p (z i) ≠ 1) ∧ ∀ j, p ≠ q j := by
  let K : Submodule ℝ E₅ := ⊤
  have hd : 2 ≤ Module.finrank ℝ K := by simp [K]
  have : Nontrivial K := Module.finrank_pos_iff (R := ℝ) |>.mp (by omega)
  obtain ⟨w, hw⟩ := exists_norm_eq K (by norm_num : (0 : ℝ) ≤ 1)
  have hp (i : ι) (h : K.orthogonalProjectionOnto (z i - b) = 0) :
      (1 : ℝ) ^ 2 + ‖z i - b‖ ^ 2 ≠ 1 := by
    have hzero : z i - b = 0 := by
      simpa [K] using Submodule.orthogonalProjectionOnto_eq_zero_iff.mp h
    exact (hz i (sub_eq_zero.mp hzero)).elim
  obtain ⟨w, _, hw, hz, hq⟩ :=
    SphereSectionAvoidance.exists_on_affine_sphere_avoiding K hd b
      (by norm_num : (0 : ℝ) < 1) isOpen_univ
      ⟨w, Set.mem_univ _, hw⟩ z q hp
  refine ⟨b + (w : E₅), ?_, hz, hq⟩
  simpa [dist_eq_norm] using hw

private theorem choose_two_neighbors {ι κ : Type*} [Finite ι] [Finite κ]
    (b c : E₅) (hbc : b ≠ c) (hdiam : dist b c < 2)
    (z : ι → E₅) (q : κ → E₅) (hz : ∀ i, z i ≠ b ∧ z i ≠ c) :
    ∃ p : E₅, dist p b = 1 ∧ dist p c = 1 ∧
      (∀ i, dist p (z i) ≠ 1) ∧ ∀ j, p ≠ q j := by
  let m := (1 / 2 : ℝ) • (b + c)
  let a := (1 / 2 : ℝ) • (b - c)
  have hb : m + a = b := by dsimp [m, a]; module
  have hc : m - a = c := by dsimp [m, a]; module
  have ha : a ≠ 0 := by
    simpa [a, sub_eq_zero] using hbc
  have hanorm : ‖a‖ = dist b c / 2 := by
    simp [a, norm_smul, dist_eq_norm, div_eq_mul_inv, mul_comm]
  have ha1 : ‖a‖ < 1 := by rw [hanorm]; linarith
  let K := (ℝ ∙ a)ᗮ
  have hdim : Module.finrank ℝ K = 4 := by
    have h := (ℝ ∙ a).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton ha] at h
    have he : Module.finrank ℝ E₅ = 5 := by simp
    dsimp [K]
    omega
  let R := Real.sqrt (1 - ‖a‖ ^ 2)
  have hR2 : R ^ 2 = 1 - ‖a‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_nonneg a])
  have hR : 0 < R := Real.sqrt_pos.mpr (by nlinarith [norm_nonneg a])
  have : Nontrivial K := Module.finrank_pos_iff (R := ℝ) |>.mp (by omega)
  obtain ⟨w, hw⟩ := exists_norm_eq K hR.le
  have hproper (i : ι) (hp : K.orthogonalProjectionOnto (z i - m) = 0) :
      R ^ 2 + ‖z i - m‖ ^ 2 ≠ 1 := by
    intro heq
    have hmem : z i - m ∈ ℝ ∙ a := by
      have h := Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hp
      simpa only [K, Submodule.orthogonal_orthogonal] using h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    have hn : |t| * ‖a‖ = ‖a‖ := by
      have he : ‖z i - m‖ = ‖a‖ := by nlinarith [norm_nonneg (z i - m), norm_nonneg a]
      simpa only [← ht, norm_smul, Real.norm_eq_abs] using he
    have ht1 : |t| = 1 := mul_right_cancel₀ (norm_ne_zero_iff.mpr ha) (by simpa using hn)
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ht1 with ht1 | ht1
    · have he : z i = b := by
        rw [ht1, one_smul] at ht
        calc
          z i = m + (z i - m) := by abel
          _ = m + a := by rw [← ht]
          _ = b := hb
      exact (hz i).1 he
    · have he : z i = c := by
        rw [ht1, neg_one_smul] at ht
        calc
          z i = m + (z i - m) := by abel
          _ = m + -a := by rw [← ht]
          _ = c := by simpa only [sub_eq_add_neg] using hc
      exact (hz i).2 he
  obtain ⟨w, _, hwR, hwz, hwq⟩ :=
    SphereSectionAvoidance.exists_on_affine_sphere_avoiding K (by omega) m hR
      isOpen_univ ⟨w, Set.mem_univ _, hw⟩ z q hproper
  have hinner : ⟪a, (w : E₅)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
  refine ⟨m + (w : E₅), ?_, ?_, hwz, hwq⟩
  · have hd : dist (m + (w : E₅)) b ^ 2 = R ^ 2 + ‖a‖ ^ 2 := by
      rw [← hb, dist_eq_norm]
      have he : m + (w : E₅) - (m + a) = (w : E₅) - a := by abel
      rw [he, norm_sub_sq_real, real_inner_comm, hinner]
      simpa using congrArg (fun t : ℝ => t ^ 2) hwR
    nlinarith [dist_nonneg (x := m + (w : E₅)) (y := b)]
  · have hd : dist (m + (w : E₅)) c ^ 2 = R ^ 2 + ‖a‖ ^ 2 := by
      rw [← hc, dist_eq_norm]
      have he : m + (w : E₅) - (m - a) = (w : E₅) + a := by abel
      rw [he, norm_add_sq_real, real_inner_comm, hinner]
      simpa using congrArg (fun t : ℝ => t ^ 2) hwR
    nlinarith [dist_nonneg (x := m + (w : E₅)) (y := c)]

private theorem choose_neighbors {ι : Type*} [Finite ι]
    (p : ι → E₅) (hinj : Function.Injective p) (N : Finset ι) (hN : N.card ≤ 2)
    (hdiam : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → dist (p i) (p j) < 2) :
    ∃ x : E₅, (∀ i, dist x (p i) = 1 ↔ i ∈ N) ∧ ∀ i, x ≠ p i := by
  classical
  have hc : N.card = 0 ∨ N.card = 1 ∨ N.card = 2 := by omega
  rcases hc with hc | hc | hc
  · have hN0 : N = ∅ := Finset.card_eq_zero.mp hc
    obtain ⟨x, hx, hxp⟩ := choose_no_neighbors p p
    exact ⟨x, by simpa [hN0] using hx, hxp⟩
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
    obtain ⟨x, hxb, hxz, hxp⟩ := choose_one_neighbor (p b)
      (fun i : {i : ι // i ≠ b} => p i.val) p
      (fun i => fun he => i.property (hinj he))
    refine ⟨x, fun i => ?_, hxp⟩
    by_cases hi : i = b
    · simpa [hi] using hxb
    · simp [hi, hxz ⟨i, hi⟩]
  · obtain ⟨b, c, hbc, rfl⟩ := Finset.card_eq_two.mp hc
    obtain ⟨x, hxb, hxc, hxz, hxp⟩ := choose_two_neighbors (p b) (p c)
      (fun he => hbc (hinj he)) (hdiam b (by simp) c (by simp) hbc)
      (fun i : {i : ι // i ≠ b ∧ i ≠ c} => p i.val) p
      (fun i => ⟨fun he => i.property.1 (hinj he), fun he => i.property.2 (hinj he)⟩)
    refine ⟨x, fun i => ?_, hxp⟩
    by_cases hib : i = b
    · simp [hib, hxb]
    by_cases hic : i = c
    · simp [hic, hxc]
    · simp [hib, hic, hxz ⟨i, hib, hic⟩]

private theorem insert_vertex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (a : V) (ha : a ∉ s) (p : s → E₅)
    (hinj : Function.Injective p)
    (hfaith : ∀ u v : s, G.Adj u.val v.val ↔ dist (p u) (p v) = 1)
    (hdegree : G.degree a ≤ 2)
    (hdiam : ∀ u v : s, G.Adj a u.val → G.Adj a v.val →
      u ≠ v → dist (p u) (p v) < 2) :
    ∃ p' : ↥(insert a s : Finset V) → E₅, Function.Injective p' ∧
      (∀ u v : ↥(insert a s : Finset V), G.Adj u.val v.val ↔ dist (p' u) (p' v) = 1) ∧
      ∀ u : s, p' ⟨u.val, Finset.mem_insert_of_mem u.property⟩ = p u := by
  classical
  let N := (G.neighborFinset a).subtype (fun v => v ∈ s)
  have hN : N.card ≤ 2 := by
    calc
      N.card = ((G.neighborFinset a).filter (fun v => v ∈ s)).card := Finset.card_subtype _ _
      _ ≤ (G.neighborFinset a).card := Finset.card_filter_le _ _
      _ ≤ 2 := hdegree
  obtain ⟨x, hx, hxp⟩ := choose_neighbors p hinj N hN (by
    intro u hu v hv huv
    exact hdiam u v (by simpa [N] using hu) (by simpa [N] using hv) huv)
  have hxadj (u : s) : dist x (p u) = 1 ↔ G.Adj a u.val := by
    simpa [N] using hx u
  let p' : ↥(insert a s : Finset V) → E₅ := fun v =>
    if hv : v.val = a then x
    else p ⟨v.val, (Finset.mem_insert.mp v.property).resolve_left hv⟩
  have hold (u : s) : p' ⟨u.val, Finset.mem_insert_of_mem u.property⟩ = p u := by
    have hu : u.val ≠ a := by intro he; exact ha (he ▸ u.property)
    simp [p', hu]
  have hnew : p' ⟨a, Finset.mem_insert_self a s⟩ = x := by simp [p']
  have hsplit (u : ↥(insert a s : Finset V)) :
      u = ⟨a, Finset.mem_insert_self a s⟩ ∨
        ∃ v : s, u = ⟨v.val, Finset.mem_insert_of_mem v.property⟩ := by
    rcases Finset.mem_insert.mp u.property with hu | hu
    · exact Or.inl (Subtype.ext hu)
    · exact Or.inr ⟨⟨u.val, hu⟩, rfl⟩
  refine ⟨p', ?_, ?_, hold⟩
  · intro u v he
    rcases hsplit u with rfl | ⟨u, rfl⟩ <;>
      rcases hsplit v with rfl | ⟨v, rfl⟩
    · rfl
    · rw [hnew, hold] at he
      exact (hxp v he).elim
    · rw [hold, hnew] at he
      exact (hxp u he.symm).elim
    · rw [hold, hold] at he
      exact Subtype.ext (congrArg (fun w : s => w.val) (hinj he))
  · intro u v
    rcases hsplit u with rfl | ⟨u, rfl⟩ <;>
      rcases hsplit v with rfl | ⟨v, rfl⟩
    · simp
    · rw [hnew, hold]
      exact (hxadj v).symm
    · rw [hold, hnew, dist_comm]
      exact (G.adj_comm u.val a).trans (hxadj u).symm
    · rw [hold, hold]
      exact hfaith u v

/-- Restore all omitted vertices of degree at most two, while fixing every
old position. All neighbors of an omitted vertex must belong to the retained
set `B`, and distinct retained `B` positions must be strictly less than two
apart. The result is one injective map on the original carrier, faithful on
all ordered pairs, including diagonals and isolates. -/
theorem exists_faithful_extension {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B s : Finset V) (hBs : B ⊆ s) (p : s → E₅)
    (hinj : Function.Injective p)
    (hfaith : ∀ u v : s, G.Adj u.val v.val ↔ dist (p u) (p v) = 1)
    (hdiam : ∀ (b : V) (hb : b ∈ B) (c : V) (hc : c ∈ B), b ≠ c →
      dist (p ⟨b, hBs hb⟩) (p ⟨c, hBs hc⟩) < 2)
    (hneighbors : ∀ a ∉ s, G.neighborFinset a ⊆ B)
    (hdegree : ∀ a ∉ s, G.degree a ≤ 2) :
    ∃ P : V → E₅, Function.Injective P ∧
      (∀ u v : V, G.Adj u v ↔ dist (P u) (P v) = 1) ∧
      ∀ u : s, P u.val = p u := by
  classical
  generalize hn : (Finset.univ \ s).card = n
  induction n generalizing s with
  | zero =>
    have hs (v : V) : v ∈ s := by
      have he : Finset.univ \ s = ∅ := Finset.card_eq_zero.mp hn
      have hv : v ∉ Finset.univ \ s := by rw [he]; simp
      simpa using hv
    let P : V → E₅ := fun v => p ⟨v, hs v⟩
    refine ⟨P, ?_, ?_, ?_⟩
    · intro u v he
      exact congrArg Subtype.val (hinj he)
    · intro u v
      exact hfaith ⟨u, hs u⟩ ⟨v, hs v⟩
    · intro u
      rfl
  | succ n ih =>
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (Finset.univ \ s).card by omega)
    have has : a ∉ s := (Finset.mem_sdiff.mp ha).2
    obtain ⟨p', hinj', hfaith', hagree⟩ := insert_vertex G s a has p hinj hfaith
      (hdegree a has) (by
        intro u v hau hav huv
        have huB := hneighbors a has ((G.mem_neighborFinset a u.val).mpr hau)
        have hvB := hneighbors a has ((G.mem_neighborFinset a v.val).mpr hav)
        exact hdiam u.val huB v.val hvB (fun he => huv (Subtype.ext he)))
    have hBs' : B ⊆ insert a s := fun b hb => Finset.mem_insert_of_mem (hBs hb)
    have hn' : (Finset.univ \ insert a s).card = n := by
      have he : Finset.univ \ insert a s = (Finset.univ \ s).erase a := by
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          not_or, Finset.mem_erase]
      rw [he, Finset.card_erase_of_mem ha, hn]
      omega
    obtain ⟨P, hPinj, hPfaith, hPold⟩ := ih (insert a s) hBs' p' hinj' hfaith'
      (by
        intro b hb c hc hbc
        rw [hagree ⟨b, hBs hb⟩, hagree ⟨c, hBs hc⟩]
        exact hdiam b hb c hc hbc)
      (by intro v hv; exact hneighbors v (fun h => hv (Finset.mem_insert_of_mem h)))
      (by intro v hv; exact hdegree v (fun h => hv (Finset.mem_insert_of_mem h))) hn'
    refine ⟨P, hPinj, hPfaith, fun u => ?_⟩
    exact (hPold ⟨u.val, Finset.mem_insert_of_mem u.property⟩).trans (hagree u)

end D5.S3.Geometry.LowDegreeFaithfulExtension
