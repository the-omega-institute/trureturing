import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixPartnerWeightsProbe

/-! Sort coordinate deficits and send each designated smaller half to the
true side. Signed covariance transports a switching through this cube action. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced flip flip_adj)
attribute [local instance] Classical.propDecidable
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private adjacent_exists_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private coordinate_profile_for_partner_cap orderedDeficits orderedDeficits_complete
  sum_ofFn_int from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe

private def orient {n : ℕ} (b : Q n) (p : Fin n ≃ Fin n) : Q n ≃ Q n where
  toFun x i := decide (x (p i) = b (p i))
  invFun y i := decide (y (p.symm i) = b i)
  left_inv x := by
    funext i
    change decide (decide (x (p (p.symm i)) = b (p (p.symm i))) = b i) = x i
    rw [p.apply_symm_apply]
    cases hx : x i <;> cases hb : b i <;> simp [hx, hb]
  right_inv y := by
    funext i
    change decide (decide (y (p.symm (p i)) = b (p i)) = b (p i)) = y i
    rw [p.symm_apply_apply]
    cases hy : y i <;> cases hb : b (p i) <;> simp [hy, hb]

private lemma orient_flip {n : ℕ} (b : Q n) (p : Fin n ≃ Fin n) (x : Q n) (i : Fin n) :
    orient b p (flip x i) = flip (orient b p x) (p.symm i) := by
  funext j
  by_cases hj : j = p.symm i
  · subst j
    cases hx : x i <;> cases hb : b i <;>
      simp [orient, BalancedCriticalSpectrum.flip, hx, hb]
  · have h : p j ≠ i := fun e => hj (p.eq_symm_apply.mpr e)
    simp [orient, BalancedCriticalSpectrum.flip, hj, h]

private lemma orient_hamming {n : ℕ} (b : Q n) (p : Fin n ≃ Fin n) (x y : Q n) :
    hammingDist (orient b p x) (orient b p y) = hammingDist x y := by
  unfold hammingDist
  simp only [card_filter]
  rw [← Equiv.sum_comp p (fun i => if x i ≠ y i then (1 : ℕ) else 0)]
  apply sum_congr rfl
  intro i _
  change (if decide (x (p i) = b (p i)) ≠ decide (y (p i) = b (p i)) then 1 else 0) =
    if x (p i) ≠ y (p i) then 1 else 0
  cases hx : x (p i) <;> cases hy : y (p i) <;> cases hb : b (p i) <;>
    simp [hx, hy, hb]

private lemma cube_action_regular_balanced {n d : ℕ} {C : Finset (Q n)}
    (g : Q n ≃ Q n) (p : Fin n ≃ Fin n)
    (hg : ∀ x i, g (BalancedCriticalSpectrum.flip x i) =
      BalancedCriticalSpectrum.flip (g x) (p i))
    (hreg : ((hypercube n).induce (C : Set (Q n))).IsRegularOfDegree d)
    (hb : IsBalanced C) :
    ((hypercube n).induce (C.image g : Set (Q n))).IsRegularOfDegree d ∧
      IsBalanced (C.image g) := by
  classical
  have hm (y : Q n) : y ∈ C.image g ↔ g.symm y ∈ C := by
    constructor
    · rintro hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      simpa using hx
    · intro hy
      exact mem_image.mpr ⟨g.symm y, hy, g.apply_symm_apply y⟩
  let e : (C : Set (Q n)) ≃ (C.image g : Set (Q n)) :=
    { toFun := fun x => ⟨g x, mem_image.mpr ⟨x, x.property, rfl⟩⟩
      invFun := fun y => ⟨g.symm y, (hm y).mp y.property⟩
      left_inv := fun x => Subtype.ext (g.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (g.apply_symm_apply y) }
  let f : ((hypercube n).induce (C : Set (Q n))) ≃g
      ((hypercube n).induce (C.image g : Set (Q n))) :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        change (hypercube n).Adj (g x.val) (g y.val) ↔ (hypercube n).Adj x.val y.val
        constructor
        · intro h
          obtain ⟨i, hi⟩ := adjacent_exists_flip h
          have he : y.val = flip x.val (p.symm i) := g.injective (by
            rw [hi, hg, p.apply_symm_apply])
          rw [he]
          exact flip_adj _ _
        · intro h
          obtain ⟨i, hi⟩ := adjacent_exists_flip h
          rw [hi, hg]
          exact flip_adj _ _ }
  constructor
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact (f.degree_eq x).trans (hreg.degree_eq x)
  · obtain ⟨theta, ht, he, _⟩ := HuangCubeCovariance.exists_signed_covariance g p hg
    obtain ⟨sigma, hs⟩ := hb
    refine ⟨fun y => theta (g.symm y) * sigma (g.symm y), ?_, ?_⟩
    · intro y hy
      rcases ht (g.symm y) with h | h <;>
        rcases hs.1 _ ((hm y).mp hy) with h' | h' <;> simp [h, h']
    · intro x hx y hy hxy
      obtain ⟨j, hj⟩ := adjacent_exists_flip hxy
      let i := p.symm j
      have hy' : y = g (flip (g.symm x) i) := by
        rw [hg, g.apply_symm_apply]
        simpa [i] using hj
      have he' := he (g.symm x) i
      rw [g.apply_symm_apply] at he'
      have hyC : flip (g.symm x) i ∈ C := by
        simpa [hy'] using (hm y).mp hy
      rw [hy']
      simp only [g.symm_apply_apply]
      rw [he', hs.2 _ ((hm x).mp hx) _ hyC (flip_adj _ _)]
      ring

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

/-- A 66-point balanced cubic support admits coordinates in which the
smaller sides are true and their deficits are nondecreasing. -/
theorem exists_sorted_minority_cube_support {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ), S.card = 66 ∧
      ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧ IsBalanced S ∧
      (∀ x ∈ S, ∀ y ∈ S, hammingDist x y ≤ 7) ∧
      Monotone r ∧ (∀ i, 0 ≤ r i ∧ r i ≤ 5) ∧
      (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      (∀ x ∈ S, (∑ i, if x i then r i else 0) ≤ ((∑ i, r i) - 4) / 2) ∧
      110 * (∑ i, r i) ≤ 198 * (((∑ i, r i) - 4) / 2) + 6 * ∑ i, (r i) ^ 2 := by
  classical
  have hcap : ∀ x ∈ C, (shell C x 7).card ≤ 8 :=
    fun _ hx => sixty_six_distance_seven_le_eight hC hreg hb hd hx
  obtain ⟨b, r, hr, hc, hw, hm⟩ := coordinate_profile_for_partner_cap hC hreg hb 8 hcap
  let p := Tuple.sort r
  let g := orient b p
  let S := C.image g
  have hS : S.card = 66 := (card_image_of_injective _ g.injective).trans hC
  have hT := cube_action_regular_balanced g p.symm (orient_flip b p) hreg hb
  have hsums : (∑ i, r (p i)) = ∑ i, r i := Equiv.sum_comp p r
  have hsq : (∑ i, (r (p i)) ^ 2) = ∑ i, (r i) ^ 2 :=
    Equiv.sum_comp p (fun i => (r i) ^ 2)
  refine ⟨S, r ∘ p, hS, hT.1, hT.2, ?_, Tuple.monotone_sort r, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_image.mp hy
    rw [orient_hamming b p]
    exact hd x' hx' y' hy'
  · intro i
    have hlo : (23 : ℤ) ≤ (C.filter (fun x => x (p i) = b (p i))).card := by
      exact_mod_cast huang_balanced_cubic_sixty_six_half_ge_twenty_three hC hreg hb
        (p i) (b (p i))
    have hi := hc (p i)
    change 0 ≤ r (p i) ∧ r (p i) ≤ 5
    exact ⟨(hr (p i)).1, by linarith only [hlo, hi]⟩
  · intro i
    have hf : S.filter (fun x => x i = true) =
        (C.filter (fun x => x (p i) = b (p i))).image g := by
      ext x
      simp only [S, mem_filter, mem_image]
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, h⟩
        exact ⟨y, ⟨hy, by simpa [g, orient] using h⟩, rfl⟩
      · rintro ⟨y, ⟨hy, h⟩, rfl⟩
        exact ⟨⟨y, hy, rfl⟩, by simpa [g, orient] using h⟩
    rw [hf, card_image_of_injective _ g.injective]
    exact hc (p i)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    have he : (∑ i, if g y i then (r ∘ p) i else 0) =
        ∑ i, if y i = b i then r i else 0 := by
      simpa [g, orient, Function.comp_def] using
        Equiv.sum_comp p (fun i => if y i = b i then r i else 0)
    rw [he]
    simp only [Function.comp_apply, hsums]
    have hw' := hw y hy
    omega
  · simp only [Function.comp_apply, hsums, hsq]
    have harg : (∑ i, r i) - 12 + (8 : ℕ) = (∑ i, r i) - 4 := by omega
    simpa only [harg] using hm

#print axioms exists_sorted_minority_cube_support

private def capEightMoment (profile : List ℤ) : Prop :=
  110 * profile.sum ≤ 198 * ((profile.sum - 4) / 2) + 6 * (profile.map (· ^ 2)).sum

private instance (profile : List ℤ) : Decidable (capEightMoment profile) := by
  unfold capEightMoment
  infer_instance

/-- The sorted profiles satisfying the exact half bound and the eighth-partner
moment bound. -/
def sixtySixCandidateProfiles : List (List ℤ) :=
  (orderedDeficits 9 0).filter fun profile => decide (capEightMoment profile)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- The kernel checks the count of all nine-coordinate profiles.
theorem sixtySixCandidateProfiles_length : sixtySixCandidateProfiles.length = 251 := by
  decide +kernel

theorem sorted_deficits_mem_sixtySixCandidateProfiles (r : Fin 9 → ℤ)
    (hs : Monotone r) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 5)
    (hm : 110 * (∑ i, r i) ≤ 198 * (((∑ i, r i) - 4) / 2) + 6 * ∑ i, (r i) ^ 2) :
    List.ofFn r ∈ sixtySixCandidateProfiles := by
  have hb : ∀ x ∈ List.ofFn r, 0 ≤ x ∧ x ≤ 5 := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hr i
  have hordered := orderedDeficits_complete (le_refl (0 : ℤ))
    hs.sortedLE_ofFn.pairwise hb
  unfold sixtySixCandidateProfiles
  rw [List.mem_filter, decide_eq_true_eq]
  refine ⟨by simpa using hordered, ?_⟩
  unfold capEightMoment
  rw [List.map_ofFn, sum_ofFn_int, sum_ofFn_int]
  exact hm

#print axioms sixtySixCandidateProfiles_length
#print axioms sorted_deficits_mem_sixtySixCandidateProfiles

end D5.S3.Combinatorics.Graph.HypercubeCritical
