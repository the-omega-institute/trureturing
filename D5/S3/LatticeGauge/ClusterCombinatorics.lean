/- GID: D5/S3/LatticeGauge/ClusterCombinatorics
   generality: G
   mirror-B: none(waiver:covered-by-lattice-reflection-positivity4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rooted plaquette components, their expansion, and their geometric count. -/

import D5.S3.LatticeGauge.Basic

/-!
Omega original.

Rooted plaquette components, their expansion, and their geometric count.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Matrix Filter

namespace Omega.LatticeGauge

section Components

variable {P : Type*} [Fintype P] [DecidableEq P]
variable (roots : Finset P) (adj : P → P → Prop) [DecidableRel adj]

noncomputable def rootedComponent (occupied : Finset P) : Finset P := by
  classical
  exact occupied.filter fun p => ∃ r ∈ roots, r ∈ occupied ∧
    Relation.ReflTransGen (fun a b => a ∈ occupied ∧ b ∈ occupied ∧ adj a b) r p

def exterior (S : Finset P) : Finset P :=
  Finset.univ.filter fun p => p ∉ roots ∧ p ∉ S ∧ ∀ q ∈ S, ¬ adj q p

omit [Fintype P] [DecidableRel adj] in
private theorem mem_rootedComponent {occupied : Finset P} {p : P} :
    p ∈ rootedComponent roots adj occupied ↔ p ∈ occupied ∧ ∃ r ∈ roots, r ∈ occupied ∧
      Relation.ReflTransGen (fun a b => a ∈ occupied ∧ b ∈ occupied ∧ adj a b) r p := by
  classical
  simp [rootedComponent]

omit [Fintype P] [DecidableRel adj] in
private theorem rootedComponent_least {occupied S : Finset P}
    (hroot : ∀ p ∈ roots, p ∈ occupied → p ∈ S)
    (hstep : ∀ p ∈ S, ∀ q ∈ occupied, adj p q → q ∈ S) :
    rootedComponent roots adj occupied ⊆ S := by
  intro p hp
  obtain ⟨hpo, r, hr, hro, path⟩ := (mem_rootedComponent roots adj).mp hp
  clear hp hpo
  induction path with
  | refl => exact hroot r hr hro
  | tail _ step ih => exact hstep _ ih _ step.2.1 step.2.2

omit [Fintype P] [DecidableRel adj] in
private theorem rootedComponent_root {occupied : Finset P} {p : P}
    (hr : p ∈ roots) (hp : p ∈ occupied) : p ∈ rootedComponent roots adj occupied :=
  (mem_rootedComponent roots adj).mpr ⟨hp, p, hr, hp, .refl⟩

omit [Fintype P] [DecidableRel adj] in
private theorem rootedComponent_step {occupied : Finset P} {p q : P}
    (hp : p ∈ rootedComponent roots adj occupied) (hq : q ∈ occupied) (h : adj p q) :
    q ∈ rootedComponent roots adj occupied := by
  obtain ⟨hpo, r, hr, hro, path⟩ := (mem_rootedComponent roots adj).mp hp
  exact (mem_rootedComponent roots adj).mpr ⟨hq, r, hr, hro, path.tail ⟨hpo, hq, h⟩⟩

omit [Fintype P] [DecidableRel adj] in
private theorem rootedComponent_mono {S T : Finset P} (h : S ⊆ T) :
    rootedComponent roots adj S ⊆ rootedComponent roots adj T :=
  rootedComponent_least roots adj (fun _ hr hp => rootedComponent_root roots adj hr (h hp))
    fun _ hp _ hq hAdj => rootedComponent_step roots adj hp (h hq) hAdj

omit [Fintype P] [DecidableRel adj] in
private theorem rootedComponent_idem (occupied : Finset P) :
    rootedComponent roots adj (rootedComponent roots adj occupied) =
      rootedComponent roots adj occupied := by
  apply le_antisymm (rootedComponent_mono roots adj fun _ hp => ((mem_rootedComponent roots adj).mp hp).1)
  intro p hp
  obtain ⟨hpo, r, hr, hro, path⟩ := (mem_rootedComponent roots adj).mp hp
  clear hp hpo
  induction path with
  | refl => exact rootedComponent_root roots adj hr (rootedComponent_root roots adj hr hro)
  | tail path step ih =>
    exact rootedComponent_step roots adj ih ((mem_rootedComponent roots adj).mpr
      ⟨step.2.1, r, hr, hro, path.tail step⟩) step.2.2

private theorem sdiff_rootedComponent_subset_exterior (occupied : Finset P) :
    occupied \ rootedComponent roots adj occupied ⊆ exterior roots adj (rootedComponent roots adj occupied) := by
  intro p hp
  obtain ⟨hpo, hpS⟩ := Finset.mem_sdiff.mp hp
  simpa only [exterior, Finset.mem_filter, Finset.mem_univ, true_and] using
    ⟨fun hr => hpS (rootedComponent_root roots adj hr hpo), hpS,
      fun _ hq h => hpS (rootedComponent_step roots adj hq hpo h)⟩

private theorem rootedComponent_union_exterior {S T : Finset P}
    (hS : rootedComponent roots adj S = S) (hT : T ⊆ exterior roots adj S) :
    rootedComponent roots adj (S ∪ T) = S := by
  apply le_antisymm
  swap
  · nth_rw 1 [← hS]
    exact rootedComponent_mono roots adj Finset.subset_union_left
  apply rootedComponent_least roots adj
  · intro p hr hp
    refine (Finset.mem_union.mp hp).resolve_right fun hpT => ?_
    exact ((Finset.mem_filter.mp (hT hpT)).2).1 hr
  · intro p hp q hq h
    refine (Finset.mem_union.mp hq).resolve_right fun hqT => ?_
    exact ((Finset.mem_filter.mp (hT hqT)).2).2.2 p hp h

theorem prod_component_expansion {R : Type*} [CommSemiring R] (t : P → R) :
    (∏ p, (1 + t p)) = ∑ S ∈ Finset.univ.powerset.filter (fun S => rootedComponent roots adj S = S),
      (∏ p ∈ S, t p) * ∏ p ∈ exterior roots adj S, (1 + t p) := by
  classical
  rw [Finset.prod_one_add]
  simp_rw [Finset.prod_one_add, Finset.mul_sum]
  rw [Finset.sum_sigma' _ _ (fun S T => (∏ p ∈ S, t p) * ∏ p ∈ T, t p)]
  refine Finset.sum_bij' (fun X _ => ⟨rootedComponent roots adj X, X \ rootedComponent roots adj X⟩)
    (fun ST _ => ST.1 ∪ ST.2) ?_ ?_ ?_ ?_ ?_
  · intro X _
    simp [rootedComponent_idem, sdiff_rootedComponent_subset_exterior]
  · simp
  · intro X _
    exact Finset.union_sdiff_of_subset fun _ hp => ((mem_rootedComponent roots adj).mp hp).1
  · intro ST hST
    obtain ⟨S,T⟩ := ST
    obtain ⟨hS, hT⟩ := by simpa using hST
    have hTS : Disjoint T S := Finset.disjoint_left.mpr fun _ hpT hpS =>
      ((Finset.mem_filter.mp (hT hpT)).2).2.1 hpS
    simp [rootedComponent_union_exterior roots adj hS hT, show (S ∪ T) \ S = T by rw [Finset.union_comm]; exact Finset.union_sdiff_cancel_right hTS]
  · intro X _
    have hS : rootedComponent roots adj X ⊆ X := fun _ hp => ((mem_rootedComponent roots adj).mp hp).1
    nth_rw 1 [← Finset.union_sdiff_of_subset hS]
    rw [Finset.prod_union Finset.disjoint_sdiff]

noncomputable def componentFamilyWhere (keep : Finset P → Prop) : Finset (Finset P) := by
  classical
  exact Finset.univ.powerset.filter fun S => rootedComponent roots adj S = S ∧ keep S

noncomputable def componentFamily (A : ℕ) : Finset (Finset P) :=
  componentFamilyWhere roots adj (fun S => A ≤ S.card)

end Components

section Counting

variable {P : Type*} [Fintype P] [DecidableEq P]
variable (adj : P → P → Prop) [DecidableRel adj]

private def neighbors (p : P) : Finset P :=
  Finset.univ.filter fun q => adj p q

private noncomputable def componentLevel (roots : Finset P) (n : ℕ) : Finset (Finset P) := by
  classical
  exact Finset.univ.powerset.filter fun S => rootedComponent roots adj S = S ∧ S.card = n

omit [Fintype P] [DecidableRel adj] in
private theorem component_erase_root_of_absent {roots S : Finset P} {r : P}
    (hS : rootedComponent roots adj S = S) (hr : r ∉ S) :
    rootedComponent (roots.erase r) adj S = S := by
  apply le_antisymm (fun _ hp => ((mem_rootedComponent _ adj).mp hp).1)
  calc
    S = rootedComponent roots adj S := hS.symm
    _ ⊆ rootedComponent (roots.erase r) adj S :=
      rootedComponent_least roots adj
        (fun p hp hps => rootedComponent_root (roots.erase r) adj
          (Finset.mem_erase.mpr ⟨fun e => hr (e ▸ hps), hp⟩) hps)
        fun _ hp _ hq hadj => rootedComponent_step (roots.erase r) adj hp hq hadj

private theorem component_erase_root_of_present {roots S : Finset P} (r : P)
    (hS : rootedComponent roots adj S = S) :
    rootedComponent (roots.erase r ∪ neighbors adj r) adj (S.erase r) = S.erase r := by
  let R := roots.erase r ∪ neighbors adj r
  let X := rootedComponent R adj (S.erase r)
  apply le_antisymm (fun _ hp => ((mem_rootedComponent _ adj).mp hp).1)
  have hle : S ⊆ insert r X := by
    rw [← hS]
    apply rootedComponent_least roots adj
    · intro p hpr hps
      by_cases h : p = r
      · simp [h]
      · exact Finset.mem_insert_of_mem (rootedComponent_root R adj
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hpr⟩))
          (Finset.mem_erase.mpr ⟨h, hps⟩))
    · intro p hp q hq hadj
      by_cases h : q = r
      · simp [h]
      · apply Finset.mem_insert_of_mem
        have hq' := Finset.mem_erase.mpr ⟨h, hq⟩
        rcases Finset.mem_insert.mp hp with he | hp'
        · subst p
          exact rootedComponent_root R adj
            (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩)) hq'
        · exact rootedComponent_step R adj hp' hq' hadj
  intro p hp
  exact (Finset.mem_insert.mp (hle (Finset.mem_of_mem_erase hp))).resolve_left (Finset.ne_of_mem_erase hp)

private theorem componentLevel_card_le (D : ℕ) (hD : ∀ p, (neighbors adj p).card ≤ D)
    (roots : Finset P) (n : ℕ) :
    (componentLevel adj roots n).card ≤ (roots.card + D * (n - 1)).choose n := by
  classical
  by_cases hn : n = 0
  · subst n
    rw [Nat.choose_zero_right]
    apply (Finset.card_le_one).mpr
    intro S hS T hT
    have hs : S.card = 0 := by simpa [componentLevel] using (Finset.mem_filter.mp hS).2.2
    have ht : T.card = 0 := by simpa [componentLevel] using (Finset.mem_filter.mp hT).2.2
    rw [Finset.card_eq_zero.mp hs, Finset.card_eq_zero.mp ht]
  by_cases hR : roots = ∅
  · subst roots
    have hE : componentLevel adj ∅ n = ∅ := by
      ext S
      have hEmpty : rootedComponent ∅ adj S = ∅ := by
        ext p
        simp [mem_rootedComponent]
      simp only [componentLevel, hEmpty, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
        true_and, Finset.notMem_empty, iff_false]
      rintro ⟨rfl, h⟩
      exact hn h.symm
    simp [hE]
  obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hR
  let H := componentLevel adj roots n
  let R₀ := roots.erase r
  let R₁ := R₀ ∪ neighbors adj r
  have hR₀ : R₀.card = roots.card - 1 := Finset.card_erase_of_mem hr
  have hR₁ : R₁.card ≤ R₀.card + D :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left (hD r) _)
  have hsub : H.filter (fun S => r ∉ S) ⊆ componentLevel adj R₀ n := by
    intro S hS
    have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      component_erase_root_of_absent adj hs.1 (Finset.mem_filter.mp hS).2, hs.2⟩
  have hmaps : Set.MapsTo (fun S : Finset P => S.erase r)
      (H.filter (fun S => r ∈ S)) (componentLevel adj R₁ (n-1)) := by
    intro S hS
    have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      component_erase_root_of_present adj r hs.1,
      by rw [Finset.card_erase_of_mem ((Finset.mem_filter.mp hS).2), hs.2]⟩
  have hinj : Set.InjOn (fun S : Finset P => S.erase r) (H.filter (fun S => r ∈ S)) := by
    intro S hS T hT hST
    change S.erase r = T.erase r at hST
    rw [← Finset.insert_erase ((Finset.mem_filter.mp hS).2), ← Finset.insert_erase ((Finset.mem_filter.mp hT).2), hST]
  have hpart := Finset.card_filter_add_card_filter_not (s := H) (p := fun S => r ∈ S)
  have h₀ := componentLevel_card_le D hD R₀ n
  have h₁ := componentLevel_card_le D hD R₁ (n-1)
  have hsplit : (roots.card + D * (n-1)).choose n =
      (R₀.card + D * (n-1)).choose (n-1) + (R₀.card + D * (n-1)).choose n := by
    have hr' : 0 < roots.card := Finset.card_pos.mpr ⟨r, hr⟩
    have heq : roots.card + D * (n-1) = R₀.card + D * (n-1) + 1 := by omega
    have hn' : n = n-1+1 := by omega
    rw [heq]
    simpa only [← hn'] using Nat.choose_succ_succ' (R₀.card + D * (n-1)) (n-1)
  change H.card ≤ _
  rw [← hpart, hsplit]
  apply Nat.add_le_add _ ((Finset.card_le_card hsub).trans h₀)
  apply (Finset.card_le_card_of_injOn _ hmaps hinj).trans (h₁.trans _)
  by_cases hk : n = 1
  · simp [hk]
  apply Nat.choose_le_choose
  have heq : n-1 = (n-1-1)+1 := by omega
  have heq' : D * (n-1) = D * (n-1-1) + D := by
    calc
      _ = D * ((n-1-1) + 1) := congrArg (D * ·) heq
      _ = _ := by rw [Nat.mul_add, Nat.mul_one]
  omega
termination_by roots.card + D * n
decreasing_by
  · change R₀.card + D * n < roots.card + D * n
    have : 0 < roots.card := Finset.card_pos.mpr ⟨r, hr⟩
    omega
  · change R₁.card + D * (n-1) < roots.card + D * n
    have hh : n = (n-1)+1 := by omega
    have hD' : D * n = D * (n-1) + D := by nth_rw 1 [hh]; simp [Nat.mul_add]
    have : 0 < roots.card := Finset.card_pos.mpr ⟨r, hr⟩
    omega

private theorem choose_mul_twenty_le (k : ℕ) : (20 * k).choose k ≤ 60 ^ k := by
  have h := Finset.single_le_sum
    (f := fun i => (1 / 20 : ℝ) ^ i * 1 ^ (20 * k - i) * ((20 * k).choose i : ℝ))
    (fun _ _ => by positivity) (Finset.mem_range.mpr (by omega : k < 20 * k + 1))
  rw [← add_pow] at h
  simp only [one_pow, mul_one] at h
  have hexp : ((1 / 20 : ℝ) + 1) ^ 20 ≤ 3 := by
    have he : (1 + (20 : ℝ)⁻¹) ^ (20 : ℕ) ≤ Real.exp 1 := by
      exact Real.one_add_inv_pow_le_exp (n := 20)
    apply le_of_lt
    convert he.trans_lt Real.exp_one_lt_three using 1
    ring
  have hp : ((1 / 20 : ℝ) + 1) ^ (20 * k) ≤ 3 ^ k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hexp _
  have ha : ((20*k).choose k : ℝ) * (1 / 20 : ℝ) ^ k ≤ 3 ^ k := by
    simpa only [mul_comm] using h.trans hp
  have hb := mul_le_mul_of_nonneg_right ha (show 0 ≤ (20 : ℝ) ^ k by positivity)
  have heq : (1 / 20 : ℝ) ^ k * 20 ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [mul_assoc, heq, mul_one, ← mul_pow] at hb
  exact_mod_cast hb

private theorem componentLevel_singleton_le (hD : ∀ p, (neighbors adj p).card ≤ 20)
    (r : P) (k : ℕ) : (componentLevel adj {r} (k+1)).card ≤ 60 ^ k := by
  classical
  let H := componentLevel adj {r} (k+1)
  have hr (S : Finset P) (hS : S ∈ H) : r ∈ S := by
    obtain ⟨hC, hcard⟩ := (Finset.mem_filter.mp hS).2
    have hpos : 0 < S.card := by omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    obtain ⟨_, q, hqr, hqs, _⟩ := (mem_rootedComponent {r} adj).mp (hC.symm ▸ hp)
    simpa [Finset.mem_singleton.mp hqr] using hqs
  have hmaps : Set.MapsTo (fun S : Finset P => S.erase r) H
      (componentLevel adj (neighbors adj r) k) := by
    intro S hS
    obtain ⟨hC, hc⟩ := (Finset.mem_filter.mp hS).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_, ?_⟩
    · simpa using component_erase_root_of_present adj r hC
    · change (S.erase r).card = k
      rw [Finset.card_erase_of_mem (hr S hS), hc, Nat.add_sub_cancel]
  have hinj : Set.InjOn (fun S : Finset P => S.erase r) H := by
    intro S hS T hT hST
    change S.erase r = T.erase r at hST
    rw [← Finset.insert_erase (hr S hS), ← Finset.insert_erase (hr T hT), hST]
  calc
    H.card ≤ (componentLevel adj (neighbors adj r) k).card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ ((neighbors adj r).card + 20 * (k-1)).choose k :=
      componentLevel_card_le adj 20 hD _ _
    _ ≤ (20 * k).choose k := by
      by_cases hk : k = 0
      · simp [hk]
      apply Nat.choose_le_choose
      have heq : 20 * k = 20 * (k-1) + 20 := by omega
      have hdeg := hD r
      omega
    _ ≤ _ := choose_mul_twenty_le k

private theorem componentLevel_clique_le (roots : Finset P)
    (hD : ∀ p, (neighbors adj p).card ≤ 20)
    (hclique : ∀ p ∈ roots, ∀ q ∈ roots, p ≠ q → adj p q) (k : ℕ) :
    (componentLevel adj roots (k+1)).card ≤ roots.card * 60 ^ k := by
  classical
  have hsub : componentLevel adj roots (k+1) ⊆ roots.biUnion (fun r => componentLevel adj {r} (k+1)) := by
    intro S hS
    obtain ⟨hC, hc⟩ := (Finset.mem_filter.mp hS).2
    have hpos : 0 < S.card := by omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    obtain ⟨_, r, hr, hrs, _⟩ := (mem_rootedComponent roots adj).mp (hC.symm ▸ hp)
    refine Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_, hc⟩⟩
    have hrC : r ∈ rootedComponent {r} adj S := rootedComponent_root _ _ (by simp) hrs
    apply le_antisymm (fun _ h => ((mem_rootedComponent _ adj).mp h).1)
    calc
      S = rootedComponent roots adj S := hC.symm
      _ ⊆ rootedComponent {r} adj S := by
        apply rootedComponent_least roots adj _ (fun _ h _ hq ha => rootedComponent_step _ _ h hq ha)
        intro q hqr hq
        by_cases h : r = q
        · simpa only [h] using hrC
        · exact rootedComponent_step _ _ hrC hq (hclique r hr q hqr h)
  calc
    _ ≤ (roots.biUnion (fun r => componentLevel adj {r} (k+1))).card := Finset.card_le_card hsub
    _ ≤ ∑ r ∈ roots, (componentLevel adj {r} (k+1)).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ roots, 60 ^ k := Finset.sum_le_sum fun r _ => componentLevel_singleton_le adj hD r k
    _ = _ := by simp

theorem componentFamily_finite_geometric_le (roots : Finset P)
    (hroots : roots.card ≤ 6) (hD : ∀ p, (neighbors adj p).card ≤ 20)
    (hclique : ∀ p ∈ roots, ∀ q ∈ roots, p ≠ q → adj p q)
    {A : ℕ} (hA : 0 < A) {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 60 ≤ c) (hq : c * δ < 1) :
    ∑ S ∈ componentFamily roots adj A, δ ^ S.card ≤
      (6 / c) * (c * δ) ^ A * ((1 - (c * δ) ^ (Fintype.card P - A + 1)) / (1 - c * δ)) := by
  classical
  let F := componentFamily roots adj A
  let q := c * δ
  let M := Finset.range (Fintype.card P - A + 1)
  have hc' : 0 < c := by linarith
  have hM : ∀ S ∈ F, S.card - A ∈ M := fun S _ => Finset.mem_range.mpr (by
    have hh := Finset.card_le_univ S
    omega)
  have hfib (i : ℕ) : F.filter (fun S => S.card - A = i) = componentLevel adj roots (A+i) := by
    ext S
    simp only [F, componentFamily, componentFamilyWhere, componentLevel, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and]
    constructor
    · rintro ⟨⟨hC, hA'⟩, hi⟩
      exact ⟨hC, by omega⟩
    · rintro ⟨hC, hi⟩
      exact ⟨⟨hC, by omega⟩, by omega⟩
  have hlevel (i : ℕ) :
      (∑ S ∈ F.filter (fun S => S.card - A = i), δ ^ S.card) ≤ (6 / c) * q ^ A * q ^ i := by
    rw [hfib]
    have heq : A + i = (A+i-1)+1 := by omega
    let k := A+i-1
    have hcount : ((componentLevel adj roots (A+i)).card : ℝ) ≤ (6 : ℝ) * c ^ k := by
      calc
        _ ≤ (roots.card : ℝ) * (60 : ℝ) ^ k := by
          have h := componentLevel_clique_le adj roots hD hclique k
          rw [show k+1 = A+i from heq.symm] at h
          exact_mod_cast h
        _ ≤ _ := mul_le_mul (by exact_mod_cast hroots)
          (pow_le_pow_left₀ (by norm_num) hc _) (by positivity) (by norm_num)
    calc
      (∑ S ∈ componentLevel adj roots (A+i), δ ^ S.card) =
          (componentLevel adj roots (A+i)).card * δ ^ (A+i) := by
        calc
          _ = ∑ _S ∈ componentLevel adj roots (A+i), δ ^ (A+i) :=
            Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_filter.mp hS).2.2]
          _ = _ := by simp
      _ ≤ 6 * c ^ k * δ ^ (A+i) := mul_le_mul_of_nonneg_right hcount (pow_nonneg hδ _)
      _ = _ := by
        unfold q
        rw [mul_assoc (6 / c), ← pow_add, mul_pow, show c ^ (A+i) = c ^ k * c by
          rw [← pow_succ, show k+1 = A+i from heq.symm]]
        field_simp
  change ∑ S ∈ F, δ ^ S.card ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hM (fun S => δ ^ S.card)]
  calc
    _ ≤ ∑ i ∈ M, (6 / c) * q ^ A * q ^ i := Finset.sum_le_sum fun i _ => hlevel i
    _ = _ := by
      rw [← Finset.mul_sum]
      have hsum : ∑ i ∈ M, q ^ i = (1 - q ^ (Fintype.card P - A + 1)) / (1 - q) := by
        simpa [M, Nat.Ico_zero_eq_range] using
          (geom_sum_Ico' (show q ≠ 1 from hq.ne) (Nat.zero_le (Fintype.card P - A + 1)))
      rw [hsum]

end Counting

end Omega.LatticeGauge
