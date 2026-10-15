/- GID: D5/S3/VertexAlgebra/BcGhostBpZForm
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostBpZForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual full-support bc Fock carrier has a finite graded-reverse BPZ kernel.
-/

import D5.S3.VertexAlgebra.BcGhostExteriorOperators
import D5.S3.VertexAlgebra.BcGhostNumber
import D5.S3.VertexAlgebra.BcGhostSuperStateField
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostBpZForm

noncomputable section

open D5.S3.VertexAlgebra.BcGhostFockSupport
open D5.S3.VertexAlgebra.BcGhostExteriorOperators
open D5.S3.VertexAlgebra.BcGhostNumber

abbrev GhostFock := Fock ℂ

def basis (S : Finset ℕ) : GhostFock := Finsupp.single S 1

def topSites : Finset ℕ := {1, 3, 5}

def topGhost : GhostFock := c (-1) (c 0 (c 1 vacuum))

def topCoeff (v : GhostFock) : ℂ := -v topSites

def rho (i : ℕ) : ℕ :=
  if i ∈ topSites then 6 - i else if i % 2 = 0 then i + 7 else i - 7

theorem rho_top_mem_iff (i : ℕ) : rho i ∈ topSites ↔ i ∈ topSites := by
  by_cases hi : i ∈ topSites
  · have hcases : i = 1 ∨ i = 3 ∨ i = 5 := by simpa [topSites] using hi
    rcases hcases with rfl | rfl | rfl <;> simp [rho, topSites]
  · by_cases hsmall : i < 7
    · have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [rho, topSites]
    · have hlarge : 7 ≤ i := by omega
      by_cases heven : i % 2 = 0
      · have hnot : i + 7 ∉ topSites := by
          simp [topSites]
        simp [rho, hi, heven, hnot]
      · have hodd : i % 2 = 1 := by omega
        have hnot : i - 7 ∉ topSites := by
          simp [topSites]
          omega
        simp [rho, hi, hodd, hnot]

theorem rho_involutive (i : ℕ) : rho (rho i) = i := by
  by_cases hi : i ∈ topSites
  · have hcases : i = 1 ∨ i = 3 ∨ i = 5 := by simpa [topSites] using hi
    rcases hcases with rfl | rfl | rfl <;> simp [rho, topSites]
  · by_cases hsmall : i < 7
    · have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [rho, topSites] at hi ⊢
    · have hlarge : 7 ≤ i := by omega
      by_cases heven : i % 2 = 0
      · have hnot : i + 7 ∉ topSites := by
          simp [topSites]
        have hodd : (i + 7) % 2 = 1 := by omega
        simp [rho, hi, heven, hnot, hodd]
      · have hodd : i % 2 = 1 := by omega
        have hnot : i - 7 ∉ topSites := by
          simp [topSites]
          omega
        have heven : (i - 7) % 2 = 0 := by omega
        simp [rho, hi, hodd, hnot, heven, Nat.sub_add_cancel hlarge]

theorem rho_injective : Function.Injective rho := by
  intro i j hij
  rw [← rho_involutive i, ← rho_involutive j, hij]

def chi (S : Finset ℕ) : Finset ℕ :=
  (S \ topSites).image rho ∪ topSites \ (S ∩ topSites).image rho

theorem mem_chi_iff (S : Finset ℕ) (i : ℕ) :
    i ∈ chi S ↔ (i ∉ topSites ∧ rho i ∈ S) ∨ (i ∈ topSites ∧ rho i ∉ S) := by
  classical
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hjtop : j ∉ topSites := (Finset.mem_sdiff.mp hj).2
      have hjs : j ∈ S := (Finset.mem_sdiff.mp hj).1
      have hrho : rho j ∉ topSites := by
        intro h
        exact hjtop ((rho_top_mem_iff j).mp h)
      refine Or.inl ⟨hrho, ?_⟩
      rw [rho_involutive j]
      exact hjs
    · have hitop : i ∈ topSites := (Finset.mem_sdiff.mp hi).1
      have hnot : i ∉ (S ∩ topSites).image rho := (Finset.mem_sdiff.mp hi).2
      refine Or.inr ⟨hitop, ?_⟩
      intro his
      apply hnot
      refine Finset.mem_image.mpr ⟨rho i,
        Finset.mem_inter.mpr ⟨his, (rho_top_mem_iff i).2 hitop⟩, ?_⟩
      rw [rho_involutive i]
  · rintro (hi | hi)
    · have hmem : rho i ∈ S \ topSites := by
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · exact hi.2
        · intro htop
          exact hi.1 ((rho_top_mem_iff i).mp htop)
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_image.mpr ⟨rho i, hmem, rho_involutive i⟩)
    · apply Finset.mem_union.mpr
      refine Or.inr (Finset.mem_sdiff.mpr ⟨hi.1, ?_⟩)
      intro himage
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp himage
      have hj' := Finset.mem_inter.mp hj
      have : j = rho i := by
        apply rho_injective
        rw [rho_involutive i, hji]
      exact hi.2 (this ▸ hj'.1)

theorem chi_involutive (S : Finset ℕ) : chi (chi S) = S := by
  classical
  ext i
  simp only [mem_chi_iff]
  by_cases hi : i ∈ topSites
  · simp [hi, rho_top_mem_iff, rho_involutive]
  · simp [hi, rho_top_mem_iff, rho_involutive]

theorem rho_parity_outside (i : ℕ) (hi : i ∉ topSites) :
    rho i % 2 = 1 ↔ i % 2 = 0 := by
  by_cases hsmall : i < 7
  · have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [rho, topSites] at hi ⊢
  · have hlarge : 7 ≤ i := by omega
    by_cases heven : i % 2 = 0
    · have hpar : (i + 7) % 2 = 1 := by omega
      simp [rho, hi, heven, hpar]
    · have hodd : i % 2 = 1 := by omega
      have hsub : (i - 7) % 2 = 0 := by
        have hadd : i - 7 + 7 = i := Nat.sub_add_cancel hlarge
        have hmod := congrArg (fun n => n % 2) hadd
        simp [Nat.add_mod, hodd] at hmod
        have hlt : (i - 7) % 2 < 2 := Nat.mod_lt _ (by decide)
        omega
      simp [rho, hi, hodd, hsub]

theorem topSites_all_odd (i : ℕ) (hi : i ∈ topSites) : i % 2 = 1 := by
  have hcases : i = 1 ∨ i = 3 ∨ i = 5 := by simpa [topSites] using hi
  rcases hcases with rfl | rfl | rfl <;> decide

private theorem rho_image_injective (S : Finset ℕ) :
    Set.InjOn rho S := by
  intro i hi j hj h
  exact rho_injective h

private theorem chi_even_filter (S : Finset ℕ) :
    (chi S).filter (fun i => i % 2 = 0) =
      ((S \ topSites).filter (fun i => i % 2 = 1)).image rho := by
  classical
  let outsideImage := (S \ topSites).image rho
  let topRemainder := topSites \ (S ∩ topSites).image rho
  have houtside : outsideImage.filter (fun i => i % 2 = 0) =
      ((S \ topSites).filter (fun i => i % 2 = 1)).image rho := by
    rw [Finset.filter_image]
    congr 1
    ext i
    by_cases hi : i ∈ S \ topSites
    · simp only [Finset.mem_filter, hi, true_and]
      have hp := rho_parity_outside i (Finset.mem_sdiff.mp hi).2
      omega
    · simp [hi]
  have htop : topRemainder.filter (fun i => i % 2 = 0) = ∅ := by
    ext i
    by_cases hi : i ∈ topRemainder
    · have hitop := (Finset.mem_sdiff.mp hi).1
      have htopodd := topSites_all_odd i hitop
      have hpar : i % 2 ≠ 0 := by omega
      simp [hi, hpar]
    · simp [hi]
  change (outsideImage ∪ topRemainder).filter (fun i => i % 2 = 0) = _
  rw [Finset.filter_union, houtside, htop, Finset.union_empty]

private theorem chi_odd_filter (S : Finset ℕ) :
    (chi S).filter (fun i => i % 2 = 1) =
      ((S \ topSites).filter (fun i => i % 2 = 0)).image rho ∪
        (topSites \ (S ∩ topSites).image rho) := by
  classical
  let outsideImage := (S \ topSites).image rho
  let topRemainder := topSites \ (S ∩ topSites).image rho
  have houtside : outsideImage.filter (fun i => i % 2 = 1) =
      ((S \ topSites).filter (fun i => i % 2 = 0)).image rho := by
    rw [Finset.filter_image]
    congr 1
    ext i
    by_cases hi : i ∈ S \ topSites
    · simp only [Finset.mem_filter, hi, true_and]
      exact rho_parity_outside i (Finset.mem_sdiff.mp hi).2
    · simp [hi]
  have htop : topRemainder.filter (fun i => i % 2 = 1) = topRemainder := by
    ext i
    by_cases hi : i ∈ topRemainder
    · have hitop := (Finset.mem_sdiff.mp hi).1
      simp [hi, topSites_all_odd i hitop]
    · simp [hi]
  change (outsideImage ∪ topRemainder).filter (fun i => i % 2 = 1) = _
  rw [Finset.filter_union, houtside, htop]

private theorem chi_parts_disjoint (S : Finset ℕ) :
    Disjoint ((S \ topSites).image rho)
      (topSites \ (S ∩ topSites).image rho) := by
  rw [Finset.disjoint_left]
  intro i hi htop
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  have hjoutside : j ∉ topSites := (Finset.mem_sdiff.mp hj).2
  exact hjoutside ((rho_top_mem_iff j).mp (Finset.mem_sdiff.mp htop).1)

private theorem chi_top_card (S : Finset ℕ) :
    (topSites \ (S ∩ topSites).image rho).card = 3 - (S ∩ topSites).card := by
  have hsub : (S ∩ topSites).image rho ⊆ topSites := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (rho_top_mem_iff j).2 (Finset.mem_inter.mp hj).2
  rw [Finset.card_sdiff_of_subset hsub,
    Finset.card_image_of_injOn (rho_image_injective (S ∩ topSites))]
  norm_num [topSites]

private theorem degree_parts (S : Finset ℕ) :
    degree S =
      (((S \ topSites).filter (fun i => i % 2 = 1)).card : ℤ) +
        (S ∩ topSites).card -
        ((S \ topSites).filter (fun i => i % 2 = 0)).card := by
  have hodd : S.filter (fun i => i % 2 = 1) =
      (S \ topSites).filter (fun i => i % 2 = 1) ∪ (S ∩ topSites) := by
    ext i
    by_cases hi : i ∈ S
    · by_cases hitop : i ∈ topSites
      · have hpar := topSites_all_odd i hitop
        simp [hi, hitop, hpar]
      · by_cases hodd : i % 2 = 1 <;> simp [hi, hitop, hodd]
    · simp [hi]
  have heven : S.filter (fun i => i % 2 = 0) =
      (S \ topSites).filter (fun i => i % 2 = 0) := by
    ext i
    by_cases hi : i ∈ S
    · by_cases hitop : i ∈ topSites
      · have hpar := topSites_all_odd i hitop
        simp [hi, hitop, hpar]
      · simp [hi, hitop]
    · simp [hi]
  rw [degree, hodd, heven, Finset.card_union_of_disjoint]
  · norm_num
  · rw [Finset.disjoint_left]
    intro i hi hj
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).1).2
      (Finset.mem_inter.mp hj).2

theorem degree_chi (S : Finset ℕ) : degree S + degree (chi S) = 3 := by
  have hodd := chi_odd_filter S
  have heven := chi_even_filter S
  have hdisj : Disjoint (((S \ topSites).filter (fun i => i % 2 = 0)).image rho)
      (topSites \ (S ∩ topSites).image rho) := by
    rw [Finset.disjoint_left]
    intro i hi htop
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hjoutside := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hj).1).2
    exact hjoutside ((rho_top_mem_iff j).mp (Finset.mem_sdiff.mp htop).1)
  rw [degree_parts S, degree]
  rw [hodd, heven, Finset.card_union_of_disjoint hdisj]
  · rw [Finset.card_image_of_injOn (rho_image_injective ((S \ topSites).filter
      (fun i => i % 2 = 0))),
      Finset.card_image_of_injOn (rho_image_injective ((S \ topSites).filter
      (fun i => i % 2 = 1))), chi_top_card]
    have hle : (S ∩ topSites).card ≤ 3 := by
      have hle' := Finset.card_le_card (Finset.inter_subset_right : S ∩ topSites ⊆ topSites)
      simpa [topSites] using hle'
    push_cast [Nat.cast_sub hle]
    omega

def reverseSign (S : Finset ℕ) : ℂ :=
  (-1 : ℂ) ^ (S.card * (S.card - 1) / 2)


open BcGhostSuperStateField BcGhostSuperGenerators

def bpzSite (i : ℕ) : Module.End ℂ GhostFock :=
  if i % 2 = 0 then
    ((-1 : ℂ) ^ (i / 2)) • b (((i / 2 : ℕ) : ℤ) + 2)
  else
    ((-1 : ℂ) ^ (i / 2)) • c (((i / 2 : ℕ) : ℤ) - 1)

theorem bpzSite_even (r : ℕ) :
    bpzSite (2 * r) = ((-1 : ℂ) ^ r) • b ((r : ℤ) + 2) := by
  simp [bpzSite]

theorem bpzSite_odd (r : ℕ) :
    bpzSite (2 * r + 1) = ((-1 : ℂ) ^ r) • c ((r : ℤ) - 1) := by
  have hdiv : (2 * r + 1) / 2 = r := by omega
  simp [bpzSite, hdiv]


private theorem sign_erase (site : ℕ) (sites : Finset ℕ) :
    sign (K := ℂ) site (sites.erase site) = sign site sites := by
  have filters : (sites.erase site).filter (fun other => other < site) =
      sites.filter (fun other => other < site) := by
    ext other
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨different, member⟩, smaller⟩
      exact ⟨member, smaller⟩
    · rintro ⟨member, smaller⟩
      exact ⟨⟨ne_of_lt smaller, member⟩, smaller⟩
  simp only [sign, filters]

private theorem sign_insert (site : ℕ) (sites : Finset ℕ) :
    sign (K := ℂ) site (insert site sites) = sign site sites := by
  simp [sign, Finset.filter_insert]

theorem create_coeff (site : ℕ) (state : GhostFock) (sites : Finset ℕ) :
    create site state sites =
      if site ∈ sites then sign site sites * state (sites.erase site) else 0 := by
  classical
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstLaw secondLaw =>
    simp only [map_add, Finsupp.add_apply, firstLaw, secondLaw]
    split <;> ring
  | single support scalar =>
    simp only [create, Finsupp.linearCombination_single, Finsupp.smul_apply,
      smul_eq_mul]
    by_cases occupied : site ∈ support
    · have different : support ≠ sites.erase site := by
        intro same
        simpa [same] using occupied
      simp [createBasis, occupied, Finsupp.single_apply, different, Ne.symm different]
    · by_cases present : site ∈ sites
      · by_cases same : support = sites.erase site
        · subst support
          simp [createBasis, present, sign_erase, Finset.insert_erase, mul_comm]
        · have different : insert site support ≠ sites := by
            intro equality
            apply same
            simpa [occupied] using congrArg (Finset.erase · site) equality
          simp [createBasis, occupied, present, Finsupp.single_apply, same,
            Ne.symm same, different, Ne.symm different]
      · have different : insert site support ≠ sites := by
          intro equality
          have : site ∈ sites := by rw [← equality]; simp
          exact present this
        simp [createBasis, occupied, present, Finsupp.single_apply, different,
          Ne.symm different]

theorem annihilate_coeff (site : ℕ) (state : GhostFock) (sites : Finset ℕ) :
    annihilate site state sites =
      if site ∈ sites then 0 else sign site sites * state (insert site sites) := by
  classical
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstLaw secondLaw =>
    simp only [map_add, Finsupp.add_apply, firstLaw, secondLaw]
    split <;> ring
  | single support scalar =>
    simp only [annihilate, Finsupp.linearCombination_single, Finsupp.smul_apply,
      smul_eq_mul]
    by_cases occupied : site ∈ support
    · by_cases present : site ∈ sites
      · have different : support.erase site ≠ sites := by
          intro same
          have : site ∉ sites := by rw [← same]; simp
          exact this present
        simp [annihilateBasis, occupied, present, Finsupp.single_apply,
          different, Ne.symm different]
      · by_cases same : support = insert site sites
        · subst support
          simp [annihilateBasis, present, sign_insert, mul_comm]
        · have different : support.erase site ≠ sites := by
            intro equality
            apply same
            rw [← equality, Finset.insert_erase occupied]
          simp [annihilateBasis, occupied, present, Finsupp.single_apply,
            same, Ne.symm same, different, Ne.symm different]
    · have different : support ≠ insert site sites := by
        intro equality
        apply occupied
        rw [equality]
        simp
      simp [annihilateBasis, occupied, Finsupp.single_apply, different,
        Ne.symm different]

def sitePhase (site : ℕ) : ℂ := (-1 : ℂ) ^ (site / 2)

theorem bpzSite_native (site : ℕ) :
    bpzSite site = sitePhase site •
      (if site ∈ topSites then create (rho site) else annihilate (rho site)) := by
  by_cases top : site ∈ topSites
  · have alternatives : site = 1 ∨ site = 3 ∨ site = 5 := by
      simpa [topSites] using top
    rcases alternatives with rfl | rfl | rfl <;>
      norm_num [bpzSite, sitePhase, topSites, rho, c,
        show (0 : ℤ).toNat = 0 from rfl,
        show (1 : ℤ).toNat = 1 from rfl,
        show (2 : ℤ).toNat = 2 from rfl]
  · by_cases even : site % 2 = 0
    · have mode : ¬ ((site / 2 : ℕ) : ℤ) + 2 ≤ -2 := by omega
      have index : ((((site / 2 : ℕ) : ℤ) + 2) + 1).toNat = site / 2 + 3 := by
        omega
      have identity : 2 * (site / 2 + 3) + 1 = site + 7 := by omega
      simp only [bpzSite, if_pos even, sitePhase, if_neg top, rho,
        b, if_neg mode, index, identity]
    · have lower : 7 ≤ site := by
        simp only [topSites, Finset.mem_insert, Finset.mem_singleton] at top
        omega
      have mode : ¬ ((site / 2 : ℕ) : ℤ) - 1 ≤ 1 := by omega
      have index : ((((site / 2 : ℕ) : ℤ) - 1) - 2).toNat = site / 2 - 3 := by
        omega
      have identity : 2 * (site / 2 - 3) = site - 7 := by omega
      simp only [bpzSite, if_neg even, sitePhase, if_neg top, rho,
        c, if_neg mode, index, identity]

def toggle (site : ℕ) (sites : Finset ℕ) : Finset ℕ :=
  if site ∈ sites then sites.erase site else insert site sites

def pulledSites : List ℕ → Finset ℕ
  | [] => topSites
  | site :: tail => toggle (rho site) (pulledSites tail)

def pulledPhase : List ℕ → ℂ
  | [] => -1
  | site :: tail =>
      if (rho site ∈ pulledSites tail ↔ site ∈ topSites) then
        pulledPhase tail * sitePhase site * sign (rho site) (pulledSites tail)
      else 0

def reversedWord (word : List ℕ) : Module.End ℂ GhostFock :=
  (word.reverse.map bpzSite).prod

theorem reversedWord_coeff (word : List ℕ) (state : GhostFock) :
    topCoeff (reversedWord word state) = pulledPhase word * state (pulledSites word) := by
  induction word generalizing state with
  | nil => simp [reversedWord, topCoeff, pulledPhase, pulledSites]
  | cons site tail inductionHypothesis =>
    have recursion : reversedWord (site :: tail) state =
        reversedWord tail (bpzSite site state) := by
      simp [reversedWord, List.reverse_cons, List.map_append, List.prod_append,
        Module.End.mul_apply]
    rw [recursion, inductionHypothesis, bpzSite_native]
    simp only [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases top : site ∈ topSites <;>
      by_cases occupied : rho site ∈ pulledSites tail <;>
      simp [top, occupied, create_coeff, annihilate_coeff, pulledPhase,
        pulledSites, toggle, mul_assoc]

theorem toggle_chi (site : ℕ) (sites : Finset ℕ) (absent : site ∉ sites) :
    toggle (rho site) (chi sites) = chi (insert site sites) := by
  classical
  ext other
  by_cases same : other = rho site
  · subst other
    simp only [mem_chi_iff, rho_involutive]
    by_cases top : site ∈ topSites <;>
      simp [toggle, mem_chi_iff, rho_involutive, rho_top_mem_iff, absent, top]
  · have different : rho other ≠ site := by
      intro equality
      apply same
      rw [← rho_involutive other, equality]
    by_cases occupied : rho site ∈ chi sites <;>
      simp [toggle, occupied, mem_chi_iff, same, different]

theorem pulledSites_chi (word : List ℕ) (distinct : word.Nodup) :
    pulledSites word = chi word.toFinset := by
  induction word with
  | nil => simp [pulledSites, chi]
  | cons site tail inductionHypothesis =>
    have absent := (List.nodup_cons.mp distinct).1
    have tailDistinct := (List.nodup_cons.mp distinct).2
    simp only [pulledSites, List.toFinset_cons,
      inductionHypothesis tailDistinct]
    exact toggle_chi site tail.toFinset (by simpa using absent)

theorem pulledPhase_nonzero (word : List ℕ) (distinct : word.Nodup) :
    pulledPhase word ≠ 0 := by
  induction word with
  | nil => simp [pulledPhase]
  | cons site tail inductionHypothesis =>
    have absent : site ∉ tail.toFinset := by
      simpa using (List.nodup_cons.mp distinct).1
    have tailDistinct := (List.nodup_cons.mp distinct).2
    have allowed : rho site ∈ pulledSites tail ↔ site ∈ topSites := by
      rw [pulledSites_chi tail tailDistinct, mem_chi_iff, rho_involutive,
        rho_top_mem_iff]
      simp [absent]
    simp [pulledPhase, allowed, inductionHypothesis tailDistinct, sitePhase, sign]

def rawBasisOperator (sites : Finset ℕ) : Module.End ℂ GhostFock :=
  reverseSign sites • reversedWord (basisWord sites)

def eps (sites : Finset ℕ) : ℂ :=
  topCoeff (rawBasisOperator sites (basis (chi sites)))

theorem rawBasis_coeff (sites : Finset ℕ) (state : GhostFock) :
    topCoeff (rawBasisOperator sites state) = eps sites * state (chi sites) := by
  have distinct : (basisWord sites).Nodup :=
    (basisWord_increasing sites).imp (fun inequality => ne_of_lt inequality)
  have support : (basisWord sites).toFinset = sites := by
    ext site
    simp [basisWord_mem]
  have identity : ∀ vector : GhostFock,
      topCoeff (rawBasisOperator sites vector) =
        reverseSign sites * pulledPhase (basisWord sites) * vector (chi sites) := by
    intro vector
    simp only [rawBasisOperator, LinearMap.smul_apply, topCoeff, Finsupp.smul_apply,
      smul_eq_mul, neg_mul_eq_mul_neg]
    change reverseSign sites * topCoeff (reversedWord (basisWord sites) vector) = _
    rw [reversedWord_coeff, pulledSites_chi _ distinct, support]
    ring
  rw [identity, eps, identity]
  simp [basis]

theorem eps_nonzero (sites : Finset ℕ) : eps sites ≠ 0 := by
  have distinct : (basisWord sites).Nodup :=
    (basisWord_increasing sites).imp (fun inequality => ne_of_lt inequality)
  have support : (basisWord sites).toFinset = sites := by
    ext site
    simp [basisWord_mem]
  simp only [eps, rawBasisOperator, LinearMap.smul_apply, topCoeff, Finsupp.smul_apply,
    smul_eq_mul, neg_mul_eq_mul_neg]
  change reverseSign sites * topCoeff (reversedWord (basisWord sites) (basis (chi sites))) ≠ 0
  rw [reversedWord_coeff, pulledSites_chi _ distinct, support]
  simpa [basis, reverseSign] using pulledPhase_nonzero (basisWord sites) distinct

private theorem scaled_anticomm (left right : Module.End ℂ GhostFock)
    (first second : ℂ) (law : left * right + right * left = 0) :
    (first • left) * (second • right) + (second • right) * (first • left) = 0 := by
  calc
    _ = (first * second) • (left * right + right * left) := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
      rw [mul_comm second first]
    _ = 0 := by rw [law]; simp

theorem bpzSite_anticomm (first second : ℕ) :
    bpzSite first * bpzSite second + bpzSite second * bpzSite first = 0 := by
  by_cases firstEven : first % 2 = 0 <;> by_cases secondEven : second % 2 = 0
  · simp only [bpzSite, if_pos firstEven, if_pos secondEven]
    exact scaled_anticomm _ _ _ _ (BcGhostStressCurrent.b_b _ _)
  · simp only [bpzSite, if_pos firstEven, if_neg secondEven]
    apply scaled_anticomm
    have nonzero : ((first / 2 : ℕ) : ℤ) + 2 + (((second / 2 : ℕ) : ℤ) - 1) ≠ 0 := by
      omega
    simpa only [if_neg nonzero] using
      (BcGhostStressCurrent.b_c (K := ℂ) (((first / 2 : ℕ) : ℤ) + 2)
        (((second / 2 : ℕ) : ℤ) - 1))
  · simp only [bpzSite, if_neg firstEven, if_pos secondEven]
    apply scaled_anticomm
    have nonzero : ((second / 2 : ℕ) : ℤ) + 2 + (((first / 2 : ℕ) : ℤ) - 1) ≠ 0 := by
      omega
    have law := BcGhostStressCurrent.b_c (K := ℂ) (((second / 2 : ℕ) : ℤ) + 2)
      (((first / 2 : ℕ) : ℤ) - 1)
    rw [if_neg nonzero] at law
    simpa only [add_comm] using law
  · simp only [bpzSite, if_neg firstEven, if_neg secondEven]
    exact scaled_anticomm _ _ _ _ (BcGhostStressCurrent.c_c _ _)

theorem basisWord_insert_min (site : ℕ) (sites : Finset ℕ)
    (smaller : ∀ other ∈ sites, site < other) :
    basisWord (insert site sites) = site :: basisWord sites := by
  have absent : site ∉ sites := fun member => (lt_irrefl site) (smaller site member)
  have nonempty : insert site sites ≠ ∅ := by simp
  have minimum : (insert site sites).min' (Finset.nonempty_iff_ne_empty.mpr nonempty) = site := by
    apply (Finset.min'_eq_iff _ _ _).mpr
    refine ⟨by simp, ?_⟩
    intro other member
    rcases Finset.mem_insert.mp member with rfl | member
    · exact le_rfl
    · exact (smaller other member).le
  rw [basisWord, dif_neg nonempty]
  simp only [minimum, Finset.erase_insert absent]

private theorem reversedWord_cons (site : ℕ) (word : List ℕ) :
    reversedWord (site :: word) = reversedWord word * bpzSite site := by
  simp [reversedWord, List.reverse_cons, List.map_append, List.prod_append]

theorem reversedWord_insert (site : ℕ) (sites : Finset ℕ) (absent : site ∉ sites) :
    reversedWord (basisWord (insert site sites)) =
      sign (K := ℂ) site sites • (reversedWord (basisWord sites) * bpzSite site) := by
  induction sites using Finset.induction_on_min generalizing site with
  | empty => simp [basisWord_singleton, basisWord, reversedWord, sign]
  | @insert head sites minimal inductionHypothesis =>
    have headAbsent : head ∉ sites := fun member => (lt_irrefl head) (minimal head member)
    have different : site ≠ head := by
      intro equality
      exact absent (by simp [equality])
    have siteAbsent : site ∉ sites := fun member => absent (Finset.mem_insert_of_mem member)
    by_cases before : site < head
    · have smaller : ∀ other ∈ insert head sites, site < other := by
        intro other member
        rcases Finset.mem_insert.mp member with rfl | member
        · exact before
        · exact before.trans (minimal other member)
      rw [basisWord_insert_min site (insert head sites) smaller, reversedWord_cons]
      have emptyFilter : (insert head sites).filter (fun other => other < site) = ∅ := by
        apply Finset.filter_false_of_mem
        intro other member
        exact not_lt.mpr (smaller other member).le
      simp [sign, emptyFilter]
    · have after : head < site := by omega
      have smaller : ∀ other ∈ insert site sites, head < other := by
        intro other member
        rcases Finset.mem_insert.mp member with rfl | member
        · exact after
        · exact minimal other member
      rw [Finset.insert_comm site head, basisWord_insert_min head _ smaller,
        basisWord_insert_min head sites minimal, reversedWord_cons,
        reversedWord_cons, inductionHypothesis site siteAbsent]
      have phase : sign (K := ℂ) site (insert head sites) = -sign site sites := by
        simp [sign, Finset.filter_insert, after, headAbsent, pow_succ, mul_comm]
      rw [phase, smul_mul_assoc, neg_smul]
      have swap : bpzSite site * bpzSite head = -(bpzSite head * bpzSite site) :=
        eq_neg_of_add_eq_zero_left (bpzSite_anticomm site head)
      rw [mul_assoc, swap, mul_neg, ← mul_assoc, smul_neg]

private theorem reverseSign_insert (site : ℕ) (sites : Finset ℕ) (absent : site ∉ sites) :
    reverseSign (insert site sites) = (-1 : ℂ) ^ sites.card * reverseSign sites := by
  have arithmetic : (sites.card + 1) * sites.card =
      sites.card * (sites.card - 1) + 2 * sites.card := by
    have : sites.card = 0 ∨ 1 ≤ sites.card := by omega
    rcases this with empty | positive
    · simp [empty]
    · have subtraction : sites.card - 1 + 1 = sites.card := by omega
      nlinarith
  have division : (sites.card + 1) * sites.card / 2 =
      sites.card * (sites.card - 1) / 2 + sites.card := by omega
  rw [reverseSign, Finset.card_insert_of_notMem absent, Nat.add_sub_cancel,
    division, pow_add]
  exact mul_comm _ _

theorem rawBasis_insert (site : ℕ) (sites : Finset ℕ) (absent : site ∉ sites) :
    rawBasisOperator (insert site sites) =
      ((-1 : ℂ) ^ sites.card * sign site sites) •
        (rawBasisOperator sites * bpzSite site) := by
  rw [rawBasisOperator, reversedWord_insert site sites absent,
    reverseSign_insert site sites absent]
  simp only [rawBasisOperator, smul_mul_assoc, smul_smul]
  congr 1
  ring


private def topCoeffLinear : GhostFock →ₗ[ℂ] ℂ where
  toFun := topCoeff
  map_add' := by intro first second; simp [topCoeff]; ring
  map_smul' := by intro scalar state; simp [topCoeff]

def bpz : GhostFock →ₗ[ℂ] Module.End ℂ GhostFock :=
  Finsupp.linearCombination ℂ rawBasisOperator

def bpzForm : GhostFock →ₗ[ℂ] (GhostFock →ₗ[ℂ] ℂ) where
  toFun state := topCoeffLinear.comp (bpz state)
  map_add' := by intro first second; ext other; simp
  map_smul' := by intro scalar state; ext other; simp

def BPZ (stateLeft stateRight : GhostFock) : ℂ := bpzForm stateLeft stateRight

theorem BPZ_raw (stateLeft stateRight : GhostFock) :
    BPZ stateLeft stateRight = topCoeff (bpz stateLeft stateRight) := rfl

theorem BPZ_basis (sites : Finset ℕ) (stateRight : GhostFock) :
    BPZ (basis sites) stateRight = eps sites * stateRight (chi sites) := by
  rw [BPZ_raw]
  simp only [bpz, basis, Finsupp.linearCombination_single, one_smul]
  exact rawBasis_coeff sites stateRight

theorem BPZ_kernel (sites other : Finset ℕ) :
    BPZ (basis sites) (basis other) = if other = chi sites then eps sites else 0 := by
  rw [BPZ_basis]
  by_cases same : other = chi sites <;> simp [basis, same]

theorem BPZ_linear_left (scalar : ℂ) (stateLeft stateRight : GhostFock) :
    BPZ (scalar • stateLeft) stateRight = scalar * BPZ stateLeft stateRight := by
  simp [BPZ, smul_eq_mul]

theorem BPZ_linear_right (scalar : ℂ) (stateLeft stateRight : GhostFock) :
    BPZ stateLeft (scalar • stateRight) = scalar * BPZ stateLeft stateRight := by
  simp [BPZ, smul_eq_mul]

theorem BPZ_add_left (first second stateRight : GhostFock) :
    BPZ (first + second) stateRight = BPZ first stateRight + BPZ second stateRight := by
  simp [BPZ]

theorem BPZ_add_right (stateLeft first second : GhostFock) :
    BPZ stateLeft (first + second) = BPZ stateLeft first + BPZ stateLeft second := by
  simp [BPZ]

theorem BPZ_sum (stateLeft stateRight : GhostFock) :
    BPZ stateLeft stateRight =
      ∑ sites ∈ stateLeft.support, stateLeft sites * eps sites * stateRight (chi sites) := by
  change topCoeffLinear (bpz stateLeft stateRight) = _
  rw [bpz, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    smul_eq_mul]
  change (∑ sites ∈ stateLeft.support, stateLeft sites *
    topCoeff (rawBasisOperator sites stateRight)) = _
  simp_rw [rawBasis_coeff, mul_assoc]

def HomogeneousDegree (degreeValue : ℤ) (state : GhostFock) : Prop :=
  ∀ sites ∈ state.support, degree sites = degreeValue

theorem BPZ_degree_selection (leftDegree rightDegree : ℤ)
    (stateLeft stateRight : GhostFock)
    (leftHomogeneous : HomogeneousDegree leftDegree stateLeft)
    (rightHomogeneous : HomogeneousDegree rightDegree stateRight)
    (mismatch : leftDegree + rightDegree ≠ 3) : BPZ stateLeft stateRight = 0 := by
  rw [BPZ_sum]
  apply Finset.sum_eq_zero
  intro sites member
  have rightZero : stateRight (chi sites) = 0 := by
    by_contra nonzero
    have rightMember := Finsupp.mem_support_iff.mpr nonzero
    have selection := degree_chi sites
    rw [leftHomogeneous sites member, rightHomogeneous (chi sites) rightMember] at selection
    exact mismatch selection
  simp [rightZero]

private theorem pulledPhase_real (word : List ℕ) :
    star (pulledPhase word) = pulledPhase word := by
  induction word with
  | nil => simp [pulledPhase]
  | cons site tail inductionHypothesis =>
    simp only [pulledPhase]
    split <;> simp [inductionHypothesis, sitePhase, sign]

theorem eps_real (sites : Finset ℕ) : star (eps sites) = eps sites := by
  have distinct : (basisWord sites).Nodup :=
    (basisWord_increasing sites).imp (fun inequality => ne_of_lt inequality)
  have support : (basisWord sites).toFinset = sites := by
    ext site
    simp [basisWord_mem]
  have phase : eps sites = reverseSign sites * pulledPhase (basisWord sites) := by
    simp only [eps, rawBasisOperator, LinearMap.smul_apply, topCoeff, Finsupp.smul_apply,
      smul_eq_mul, neg_mul_eq_mul_neg]
    change reverseSign sites * topCoeff (reversedWord (basisWord sites) (basis (chi sites))) = _
    rw [reversedWord_coeff, pulledSites_chi _ distinct, support]
    simp [basis]
  rw [phase]
  simp [reverseSign, pulledPhase_real]

def conjCoeffs (state : GhostFock) : GhostFock :=
  Finsupp.mapRange (starRingEnd ℂ) (by simp) state

private theorem conjCoeffs_smul (scalar : ℂ) (state : GhostFock) :
    conjCoeffs (scalar • state) = star scalar • conjCoeffs state := by
  ext sites
  simp [conjCoeffs]

def Hghost (stateLeft stateRight : GhostFock) : ℂ :=
  BPZ (conjCoeffs stateLeft) stateRight

def Pi : Module.End ℂ GhostFock := parityPart 0 - parityPart 1

private theorem Pi_coeff (state : GhostFock) (sites : Finset ℕ) :
    Pi state sites = ((-1 : ℂ) ^ sites.card) * state sites := by
  rw [neg_one_pow_eq_pow_mod_two]
  have alternatives : sites.card % 2 = 0 ∨ sites.card % 2 = 1 := by omega
  rcases alternatives with grade | grade <;>
    simp [Pi, parityPart_coeff, subsetParity, grade]

theorem Pi_homogeneous (parity : ℕ) (state : GhostFock)
    (member : state ∈ homogeneous parity) : Pi state = ((-1 : ℂ) ^ parity) • state := by
  ext sites
  rw [Pi_coeff, Finsupp.smul_apply, smul_eq_mul]
  by_cases same : subsetParity sites = parity % 2
  · have phase : (-1 : ℂ) ^ sites.card = (-1 : ℂ) ^ parity := by
      rw [neg_one_pow_eq_pow_mod_two sites.card, neg_one_pow_eq_pow_mod_two parity]
      rw [← same]
      rfl
    rw [phase]
  · simp [member sites same]

private theorem Pi_basis (sites : Finset ℕ) :
    Pi (basis sites) = ((-1 : ℂ) ^ sites.card) • basis sites := by
  exact Pi_homogeneous sites.card (basis sites) (single_mem sites.card sites 1 rfl)

private theorem scalar_sign_square (exponent : ℕ) :
    ((-1 : ℂ) ^ exponent) * ((-1 : ℂ) ^ exponent) = 1 := by
  rw [← mul_pow]
  norm_num

theorem BPZ_create (site : ℕ) (stateLeft stateRight : GhostFock) :
    BPZ (create site stateLeft) stateRight = BPZ (Pi stateLeft) (bpzSite site stateRight) := by
  classical
  induction stateLeft using Finsupp.induction_linear with
  | zero => simp [BPZ]
  | add first second firstLaw secondLaw =>
    simp only [map_add, BPZ_add_left, firstLaw, secondLaw]
  | single sites scalar =>
    have singleBasis : Finsupp.single sites scalar = scalar • basis sites := by
      simp [basis]
    rw [singleBasis, map_smul, map_smul, BPZ_linear_left, BPZ_linear_left]
    congr 1
    by_cases occupied : site ∈ sites
    · have vanishes : create site (basis sites) = 0 := by
        simp [create, basis, createBasis, occupied]
      rw [vanishes, Pi_basis, BPZ_linear_left, BPZ_basis, bpzSite_native]
      have allowed : rho site ∈ chi sites ↔ site ∉ topSites := by
        rw [mem_chi_iff, rho_involutive, rho_top_mem_iff]
        simp [occupied]
      by_cases top : site ∈ topSites <;>
        simp [BPZ, top, allowed, create_coeff, annihilate_coeff]
    · have insertion : create site (basis sites) =
          sign (K := ℂ) site sites • basis (insert site sites) := by
        simp [create, basis, createBasis, occupied]
      rw [insertion, BPZ_linear_left, Pi_basis, BPZ_linear_left, BPZ_raw, BPZ_raw]
      simp only [bpz, basis, Finsupp.linearCombination_single, one_smul]
      rw [rawBasis_insert site sites occupied]
      simp only [LinearMap.smul_apply, Module.End.mul_apply]
      change sign site sites * topCoeffLinear
        (((-1 : ℂ) ^ sites.card * sign site sites) •
          rawBasisOperator sites (bpzSite site stateRight)) = _
      rw [map_smul]
      simp only [smul_eq_mul]
      have square : sign (K := ℂ) site sites * sign site sites = 1 :=
        scalar_sign_square _
      change sign site sites * (((-1 : ℂ) ^ sites.card * sign site sites) *
        topCoeff (rawBasisOperator sites (bpzSite site stateRight))) = _
      linear_combination ((-1 : ℂ) ^ sites.card *
        topCoeff (rawBasisOperator sites (bpzSite site stateRight))) * square

private theorem eps_insert (site : ℕ) (sites : Finset ℕ) (absent : site ∉ sites) :
    eps (insert site sites) = (-1 : ℂ) ^ sites.card * sign site sites *
      eps sites * sitePhase site * sign (rho site) (chi sites) := by
  have allowed : rho site ∈ chi sites ↔ site ∈ topSites := by
    rw [mem_chi_iff, rho_involutive, rho_top_mem_iff]
    simp [absent]
  rw [eps, rawBasis_insert site sites absent]
  change topCoeffLinear (((-1 : ℂ) ^ sites.card * sign site sites) •
    rawBasisOperator sites (bpzSite site (basis (chi (insert site sites))))) = _
  rw [map_smul]
  change ((-1 : ℂ) ^ sites.card * sign site sites) *
    topCoeff (rawBasisOperator sites (bpzSite site (basis (chi (insert site sites))))) = _
  rw [rawBasis_coeff, bpzSite_native]
  have target := toggle_chi site sites absent
  by_cases top : site ∈ topSites
  · have present := allowed.mpr top
    simp only [toggle, if_pos present] at target
    rw [← target]
    simp [top, present, create_coeff, basis]
    ring
  · have missing : rho site ∉ chi sites := by simpa only [allowed] using top
    simp only [toggle, if_neg missing] at target
    rw [← target]
    simp [top, missing, annihilate_coeff, basis]
    ring

def annBpZSite (site : ℕ) : Module.End ℂ GhostFock :=
  (-sitePhase site) •
    (if site ∈ topSites then annihilate (rho site) else create (rho site))

private theorem annBpZSite_insert_coeff (site : ℕ) (sites : Finset ℕ)
    (absent : site ∉ sites) (state : GhostFock) :
    annBpZSite site state (chi (insert site sites)) =
      -sitePhase site * sign (rho site) (chi sites) * state (chi sites) := by
  have allowed : rho site ∈ chi sites ↔ site ∈ topSites := by
    rw [mem_chi_iff, rho_involutive, rho_top_mem_iff]
    simp [absent]
  have target := toggle_chi site sites absent
  by_cases top : site ∈ topSites
  · have present := allowed.mpr top
    simp only [toggle, if_pos present] at target
    rw [← target]
    simp [annBpZSite, top, annihilate_coeff, Finset.insert_erase present,
      sign_erase, mul_assoc]
  · have missing : rho site ∉ chi sites := by simpa only [allowed] using top
    simp only [toggle, if_neg missing] at target
    rw [← target]
    simp [annBpZSite, top, create_coeff, missing, sign_insert, mul_assoc]

private theorem BPZ_annihilate_insert (site : ℕ) (sites : Finset ℕ)
    (absent : site ∉ sites) (stateRight : GhostFock) :
    BPZ (annihilate site (basis (insert site sites))) stateRight =
      BPZ (Pi (basis (insert site sites))) (annBpZSite site stateRight) := by
  have deletion : annihilate site (basis (insert site sites)) =
      sign (K := ℂ) site sites • basis sites := by
    simp [annihilate, basis, annihilateBasis, absent, sign_insert]
  rw [deletion, BPZ_linear_left, BPZ_basis, Pi_basis, BPZ_linear_left,
    BPZ_basis, annBpZSite_insert_coeff site sites absent,
    eps_insert site sites absent, Finset.card_insert_of_notMem absent, pow_succ]
  have paritySquare := scalar_sign_square sites.card
  have phaseSquare : sitePhase site * sitePhase site = 1 := scalar_sign_square _
  have insertionSquare : sign (K := ℂ) (rho site) (chi sites) *
      sign (rho site) (chi sites) = 1 := scalar_sign_square _
  calc
    _ = (((-1 : ℂ) ^ sites.card) * ((-1 : ℂ) ^ sites.card)) *
        (sitePhase site * sitePhase site) *
        (sign (rho site) (chi sites) * sign (rho site) (chi sites)) *
        (sign site sites * (eps sites * stateRight (chi sites))) := by
      rw [paritySquare, phaseSquare, insertionSquare]
      ring
    _ = _ := by ring

theorem BPZ_annihilate (site : ℕ) (stateLeft stateRight : GhostFock) :
    BPZ (annihilate site stateLeft) stateRight =
      BPZ (Pi stateLeft) (annBpZSite site stateRight) := by
  classical
  induction stateLeft using Finsupp.induction_linear with
  | zero => simp [BPZ]
  | add first second firstLaw secondLaw =>
    simp only [map_add, BPZ_add_left, firstLaw, secondLaw]
  | single sites scalar =>
    have singleBasis : Finsupp.single sites scalar = scalar • basis sites := by simp [basis]
    rw [singleBasis, map_smul, map_smul, BPZ_linear_left, BPZ_linear_left]
    congr 1
    by_cases occupied : site ∈ sites
    · simpa only [Finset.insert_erase occupied] using
        BPZ_annihilate_insert site (sites.erase site) (by simp) stateRight
    · have vanishes : annihilate site (basis sites) = 0 := by
        simp [annihilate, basis, annihilateBasis, occupied]
      rw [vanishes, Pi_basis, BPZ_linear_left, BPZ_basis]
      have allowed : rho site ∈ chi sites ↔ site ∈ topSites := by
        rw [mem_chi_iff, rho_involutive, rho_top_mem_iff]
        simp [occupied]
      by_cases top : site ∈ topSites <;>
        simp [BPZ, annBpZSite, top, allowed, create_coeff, annihilate_coeff]

private theorem annBpZSite_even (index : ℕ) :
    annBpZSite (2 * index) = -((-1 : ℂ) ^ index) • c (-(index : ℤ) - 2) := by
  have outside : 2 * index ∉ topSites := by simp [topSites]; omega
  have branch : -(index : ℤ) - 2 ≤ 1 := by omega
  have encoded : (1 - (-(index : ℤ) - 2)).toNat = index + 3 := by omega
  have siteIdentity : 2 * (index + 3) + 1 = 2 * index + 7 := by omega
  have division : 2 * index / 2 = index := by omega
  simp only [annBpZSite, sitePhase, division, if_neg outside,
    rho, Nat.mul_mod_right, if_true, c, if_pos branch, encoded, siteIdentity]

private theorem annBpZSite_odd (index : ℕ) :
    annBpZSite (2 * index + 1) = -((-1 : ℂ) ^ index) • b (1 - (index : ℤ)) := by
  by_cases small : index ≤ 2
  · have alternatives : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases alternatives with rfl | rfl | rfl <;>
      norm_num [annBpZSite, sitePhase, rho, topSites, b,
        show (0 : ℤ).toNat = 0 from rfl,
        show (1 : ℤ).toNat = 1 from rfl,
        show (2 : ℤ).toNat = 2 from rfl]
  · have outside : 2 * index + 1 ∉ topSites := by simp [topSites]; omega
    have odd : (2 * index + 1) % 2 ≠ 0 := by omega
    have division : (2 * index + 1) / 2 = index := by omega
    have branch : 1 - (index : ℤ) ≤ -2 := by omega
    have encoded : (-(1 - (index : ℤ)) - 2).toNat = index - 3 := by omega
    have siteIdentity : 2 * (index - 3) = 2 * index + 1 - 7 := by omega
    simp only [annBpZSite, sitePhase, division, if_neg outside, rho,
      if_neg odd, b, if_pos branch, encoded, siteIdentity]

private theorem integer_phase_negative (index : ℕ) :
    (-1 : ℂ) ^ (-(index : ℤ)) = (-1 : ℂ) ^ index := by
  simp [zpow_neg, ← inv_pow]

private theorem integer_phase_minus_two (index : ℕ) :
    (-1 : ℂ) ^ (-(index : ℤ) - 2) = (-1 : ℂ) ^ index := by
  rw [zpow_sub₀ (by norm_num), integer_phase_negative]
  norm_num

private theorem integer_phase_minus_one (index : ℕ) :
    (-1 : ℂ) ^ ((index : ℤ) - 1) = -((-1 : ℂ) ^ index) := by
  rw [zpow_sub₀ (by norm_num)]
  simp [div_neg_eq_neg_div]

private theorem integer_phase_plus_one (index : ℕ) :
    (-1 : ℂ) ^ ((index : ℤ) + 1) = -((-1 : ℂ) ^ index) := by
  rw [zpow_add₀ (by norm_num)]
  simp

theorem BPZ_b (mode : ℤ) (stateLeft stateRight : GhostFock) :
    BPZ (b mode stateLeft) stateRight =
      (-1 : ℂ) ^ mode * BPZ (Pi stateLeft) (b (-mode) stateRight) := by
  by_cases creator : mode ≤ -2
  · let index := (-mode - 2).toNat
    have modeIdentity : mode = -(index : ℤ) - 2 := by
      have cast := Int.toNat_of_nonneg (show 0 ≤ -mode - 2 by omega)
      dsimp [index]
      omega
    rw [b, if_pos creator, BPZ_create, bpzSite_even]
    rw [LinearMap.smul_apply, BPZ_linear_right]
    change (-1 : ℂ) ^ index * BPZ (Pi stateLeft) (b ((index : ℤ) + 2) stateRight) = _
    have opposite : -mode = (index : ℤ) + 2 := by omega
    have phase : (-1 : ℂ) ^ mode = (-1 : ℂ) ^ index := by
      rw [modeIdentity, integer_phase_minus_two]
    rw [opposite, phase]
  · let index := (mode + 1).toNat
    have modeIdentity : mode = (index : ℤ) - 1 := by
      have cast := Int.toNat_of_nonneg (show 0 ≤ mode + 1 by omega)
      dsimp [index]
      omega
    rw [b, if_neg creator, BPZ_annihilate, annBpZSite_odd]
    rw [LinearMap.smul_apply, BPZ_linear_right]
    change -((-1 : ℂ) ^ index) * BPZ (Pi stateLeft) (b (1 - (index : ℤ)) stateRight) = _
    have opposite : -mode = 1 - (index : ℤ) := by omega
    have phase : (-1 : ℂ) ^ mode = -((-1 : ℂ) ^ index) := by
      rw [modeIdentity, integer_phase_minus_one]
    rw [opposite, phase]

theorem BPZ_c (mode : ℤ) (stateLeft stateRight : GhostFock) :
    BPZ (c mode stateLeft) stateRight =
      (-1 : ℂ) ^ (mode - 1) * BPZ (Pi stateLeft) (c (-mode) stateRight) := by
  by_cases creator : mode ≤ 1
  · let index := (1 - mode).toNat
    have modeIdentity : mode = 1 - (index : ℤ) := by
      have cast := Int.toNat_of_nonneg (show 0 ≤ 1 - mode by omega)
      dsimp [index]
      omega
    rw [c, if_pos creator, BPZ_create, bpzSite_odd]
    rw [LinearMap.smul_apply, BPZ_linear_right]
    change (-1 : ℂ) ^ index * BPZ (Pi stateLeft) (c ((index : ℤ) - 1) stateRight) = _
    have opposite : -mode = (index : ℤ) - 1 := by omega
    have phase : (-1 : ℂ) ^ (mode - 1) = (-1 : ℂ) ^ index := by
      rw [modeIdentity, show 1 - (index : ℤ) - 1 = -(index : ℤ) by omega,
        integer_phase_negative]
    rw [opposite, phase]
  · let index := (mode - 2).toNat
    have modeIdentity : mode = (index : ℤ) + 2 := by
      have cast := Int.toNat_of_nonneg (show 0 ≤ mode - 2 by omega)
      dsimp [index]
      omega
    rw [c, if_neg creator, BPZ_annihilate, annBpZSite_even]
    rw [LinearMap.smul_apply, BPZ_linear_right]
    change -((-1 : ℂ) ^ index) * BPZ (Pi stateLeft) (c (-(index : ℤ) - 2) stateRight) = _
    have opposite : -mode = -(index : ℤ) - 2 := by omega
    have phase : (-1 : ℂ) ^ (mode - 1) = -((-1 : ℂ) ^ index) := by
      rw [modeIdentity, show (index : ℤ) + 2 - 1 = (index : ℤ) + 1 by omega,
        integer_phase_plus_one]
    rw [opposite, phase]

private theorem Pi_square (state : GhostFock) : Pi (Pi state) = state := by
  ext sites
  rw [Pi_coeff, Pi_coeff, ← mul_assoc, scalar_sign_square]
  simp

private theorem Pi_create (site : ℕ) (state : GhostFock) :
    Pi (create site state) = -create site (Pi state) := by
  ext sites
  rw [Pi_coeff, Finsupp.neg_apply, create_coeff, create_coeff]
  by_cases present : site ∈ sites
  · simp only [if_pos present, Pi_coeff]
    have cardinality : sites.card = (sites.erase site).card + 1 := by
      rw [Finset.card_erase_of_mem present]
      have positive := Finset.card_pos.mpr ⟨site, present⟩
      omega
    rw [cardinality, pow_succ]
    ring
  · simp [present]

private theorem Pi_annihilate (site : ℕ) (state : GhostFock) :
    Pi (annihilate site state) = -annihilate site (Pi state) := by
  ext sites
  rw [Pi_coeff, Finsupp.neg_apply, annihilate_coeff, annihilate_coeff]
  by_cases present : site ∈ sites
  · simp [present]
  · simp only [if_neg present, Pi_coeff, Finset.card_insert_of_notMem present, pow_succ]
    ring

private theorem Pi_b (mode : ℤ) (state : GhostFock) :
    Pi (b mode state) = -b mode (Pi state) := by
  unfold b
  split
  · exact Pi_create _ state
  · exact Pi_annihilate _ state

private theorem Pi_c (mode : ℤ) (state : GhostFock) :
    Pi (c mode state) = -c mode (Pi state) := by
  unfold c
  split
  · exact Pi_create _ state
  · exact Pi_annihilate _ state

private theorem BPZ_neg_left (stateLeft stateRight : GhostFock) :
    BPZ (-stateLeft) stateRight = -BPZ stateLeft stateRight := by simp [BPZ]

private theorem BPZ_neg_right (stateLeft stateRight : GhostFock) :
    BPZ stateLeft (-stateRight) = -BPZ stateLeft stateRight := by simp [BPZ]

private theorem integer_pair_phase (first second : ℤ) :
    -(((-1 : ℂ) ^ first) * ((-1 : ℂ) ^ (second - 1))) = (-1 : ℂ) ^ (first + second) := by
  rw [← zpow_add₀ (by norm_num)]
  rw [show first + (second - 1) = (first + second) - 1 by omega,
    zpow_sub₀ (by norm_num)]
  simp [div_neg_eq_neg_div]

private theorem BPZ_bc (first second : ℤ) (stateLeft stateRight : GhostFock) :
    BPZ (b first (c second stateLeft)) stateRight =
      (-1 : ℂ) ^ (first + second) * BPZ stateLeft (c (-second) (b (-first) stateRight)) := by
  rw [BPZ_b, Pi_c, BPZ_neg_left, BPZ_c, Pi_square]
  have phase := integer_pair_phase first second
  linear_combination BPZ stateLeft (c (-second) (b (-first) stateRight)) * phase

private theorem BPZ_cb (first second : ℤ) (stateLeft stateRight : GhostFock) :
    BPZ (c second (b first stateLeft)) stateRight =
      (-1 : ℂ) ^ (first + second) * BPZ stateLeft (b (-first) (c (-second) stateRight)) := by
  rw [BPZ_c, Pi_b, BPZ_neg_left, BPZ_b, Pi_square]
  have phase := integer_pair_phase first second
  linear_combination BPZ stateLeft (b (-first) (c (-second) stateRight)) * phase

theorem BPZ_normalPair (first second : ℤ) (stateLeft stateRight : GhostFock) :
    BPZ (normalPair first second stateLeft) stateRight =
      -((-1 : ℂ) ^ (first + second)) *
        BPZ stateLeft (normalPair (-first) (-second) stateRight) -
      (if -1 ≤ first ∧ first ≤ 1 ∧ first + second = 0 then BPZ stateLeft stateRight else 0) := by
  have car := congrArg (fun operator : Module.End ℂ GhostFock => operator stateRight)
    (BcGhostStressCurrent.b_c (K := ℂ) (-first) (-second))
  have sumZero : -first + -second = 0 ↔ first + second = 0 := by omega
  simp only [LinearMap.add_apply, Module.End.mul_apply, sumZero] at car
  have paired : BPZ stateLeft (b (-first) (c (-second) stateRight)) +
      BPZ stateLeft (c (-second) (b (-first) stateRight)) =
      if first + second = 0 then BPZ stateLeft stateRight else 0 := by
    rw [← BPZ_add_right, car]
    split <;> simp [BPZ]
  by_cases creator : first ≤ -2
  · have reversed : ¬ -first ≤ -2 := by omega
    have middle : ¬ -1 ≤ first := by omega
    simp only [normalPair, if_pos creator, if_neg reversed, LinearMap.comp_apply,
      LinearMap.neg_apply, BPZ_bc, BPZ_neg_right, middle, false_and, if_false]
    ring
  · by_cases reversed : -first ≤ -2
    · have middle : ¬ first ≤ 1 := by omega
      simp only [normalPair, if_neg creator, if_pos reversed, LinearMap.comp_apply,
        LinearMap.neg_apply, BPZ_neg_left, BPZ_cb, middle, and_false, false_and, if_false]
      ring
    · have lower : -1 ≤ first := by omega
      have upper : first ≤ 1 := by omega
      simp only [normalPair, if_neg creator, if_neg reversed, LinearMap.comp_apply,
        LinearMap.neg_apply, BPZ_neg_left, BPZ_cb, BPZ_neg_right, lower, upper,
        true_and]
      by_cases onDiagonal : first + second = 0
      · rw [onDiagonal, zpow_zero, if_pos rfl] at ⊢
        rw [if_pos onDiagonal] at paired
        linear_combination -paired
      · rw [if_neg onDiagonal] at paired ⊢
        linear_combination -((-1 : ℂ) ^ (first + second)) * paired

def physicalB0 : Module.End ℂ GhostFock := currentMode .b 1

def physicalC0 : Module.End ℂ GhostFock := currentMode .c (-2)

def v : GhostFock := basis ∅
def u : GhostFock := basis {3}
def j : GhostFock := basis {1}
def k : GhostFock := -basis {1, 3}
def z : GhostFock := -basis {1, 5}
def w : GhostFock := -basis topSites

private theorem BPZ_sum_left {Index : Type*} (indices : Finset Index)
    (states : Index → GhostFock) (stateRight : GhostFock) :
    BPZ (∑ index ∈ indices, states index) stateRight =
      ∑ index ∈ indices, BPZ (states index) stateRight := by
  simp [BPZ, map_sum, LinearMap.sum_apply]

private theorem BPZ_sum_right {Index : Type*} (indices : Finset Index)
    (states : Index → GhostFock) (stateLeft : GhostFock) :
    BPZ stateLeft (∑ index ∈ indices, states index) =
      ∑ index ∈ indices, BPZ stateLeft (states index) := by
  simp [BPZ, map_sum]

private theorem stress_correction_sum (mode radius : ℤ) (radiusBound : 1 ≤ radius)
    (scalar : ℂ) :
    (∑ index ∈ Finset.Icc (-radius) radius,
      (mode - index : ℂ) *
        (if -1 ≤ mode + index ∧ mode + index ≤ 1 ∧ mode = 0 then scalar else 0)) = 0 := by
  by_cases zeroMode : mode = 0
  · subst mode
    have subset : Finset.Icc (-1 : ℤ) 1 ⊆ Finset.Icc (-radius) radius := by
      intro index member
      simp only [Finset.mem_Icc] at member ⊢
      omega
    have shrink : (∑ index ∈ Finset.Icc (-radius) radius,
        (-index : ℂ) * (if -1 ≤ index ∧ index ≤ 1 then scalar else 0)) =
        ∑ index ∈ Finset.Icc (-1 : ℤ) 1,
          (-index : ℂ) * (if -1 ≤ index ∧ index ≤ 1 then scalar else 0) := by
      symm
      apply Finset.sum_subset subset
      intro index member outside
      have notMiddle : ¬ (-1 ≤ index ∧ index ≤ 1) := by
        simpa only [Finset.mem_Icc] using outside
      simp [notMiddle]
    simp only [Int.cast_zero, zero_sub, zero_add, and_true]
    rw [shrink]
    have interval : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by decide
    rw [interval]
    norm_num
  · simp [zeroMode]

theorem BPZ_stress (mode : ℤ) (stateLeft stateRight : GhostFock) :
    BPZ (L mode stateLeft) stateRight =
      (-1 : ℂ) ^ mode * BPZ stateLeft (L (-mode) stateRight) := by
  let radius : ℤ := max (cutoff mode stateLeft) (cutoff (-mode) stateRight) + 2
  have leftBound : cutoff mode stateLeft ≤ radius := by
    have maximal := le_max_left (cutoff mode stateLeft) (cutoff (-mode) stateRight)
    dsimp [radius]
    omega
  have rightBound : cutoff (-mode) stateRight ≤ radius := by
    have maximal := le_max_right (cutoff mode stateLeft) (cutoff (-mode) stateRight)
    dsimp [radius]
    omega
  have radiusBound : 1 ≤ radius := by
    have occupiedNonnegative : (0 : ℤ) ≤ ((occupied stateLeft).sup id : ℕ) := by positivity
    have absoluteNonnegative : (0 : ℤ) ≤ mode.natAbs := by positivity
    dsimp [cutoff] at leftBound
    omega
  have leftSum : BPZ (L mode stateLeft) stateRight =
      ∑ index ∈ Finset.Icc (-radius) radius,
        (mode - index : ℂ) * BPZ (normalPair (mode + index) (-index) stateLeft) stateRight := by
    rw [L_interval_sum mode stateLeft (-radius) radius (by omega) leftBound, BPZ_sum_left]
    simp_rw [BPZ_linear_left]
  have rightSum : BPZ stateLeft (L (-mode) stateRight) =
      ∑ index ∈ Finset.Icc (-radius) radius,
        (-mode - index : ℂ) * BPZ stateLeft (normalPair (-mode + index) (-index) stateRight) := by
    rw [L_interval_sum (-mode) stateRight (-radius) radius (by omega) rightBound, BPZ_sum_right]
    simp_rw [BPZ_linear_right, Int.cast_neg]
  have reindex :
      (∑ index ∈ Finset.Icc (-radius) radius,
        (-mode + index : ℂ) * BPZ stateLeft (normalPair (-mode - index) index stateRight)) =
      ∑ index ∈ Finset.Icc (-radius) radius,
        (-mode - index : ℂ) * BPZ stateLeft (normalPair (-mode + index) (-index) stateRight) := by
    apply Finset.sum_bij (fun index _ => -index)
    · intro index member
      simp only [Finset.mem_Icc] at member ⊢
      omega
    · intro first firstMember second secondMember same
      omega
    · intro index member
      refine ⟨-index, ?_, by omega⟩
      simp only [Finset.mem_Icc] at member ⊢
      omega
    · intro index member
      simp [sub_eq_add_neg]
  have summand (index : ℤ) :
      (mode - index : ℂ) * BPZ (normalPair (mode + index) (-index) stateLeft) stateRight =
        (-1 : ℂ) ^ mode *
          ((-mode + index : ℂ) * BPZ stateLeft (normalPair (-mode - index) index stateRight)) -
        (mode - index : ℂ) *
          (if -1 ≤ mode + index ∧ mode + index ≤ 1 ∧ mode = 0 then BPZ stateLeft stateRight else 0) := by
    rw [BPZ_normalPair]
    rw [show mode + index + -index = mode by omega,
      show -(mode + index) = -mode - index by omega, neg_neg]
    ring
  rw [leftSum]
  simp_rw [summand]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    stress_correction_sum mode radius radiusBound, sub_zero, reindex, ← rightSum]

private theorem chi_card_add (sites : Finset ℕ) :
    sites.card + (chi sites).card = 2 * (sites \ topSites).card + 3 := by
  rw [chi, Finset.card_union_of_disjoint (chi_parts_disjoint sites),
    Finset.card_image_of_injOn (rho_image_injective (sites \ topSites)), chi_top_card]
  have split := Finset.card_sdiff_add_card_inter sites topSites
  have bounded : (sites ∩ topSites).card ≤ 3 := by
    have comparison := Finset.card_le_card (Finset.inter_subset_right : sites ∩ topSites ⊆ topSites)
    norm_num [topSites] at comparison
    exact comparison
  omega

private theorem BPZ_Pi_both (stateLeft stateRight : GhostFock) :
    BPZ (Pi stateLeft) (Pi stateRight) = -BPZ stateLeft stateRight := by
  classical
  induction stateLeft using Finsupp.induction_linear with
  | zero => simp [BPZ]
  | add first second firstLaw secondLaw =>
    simp only [map_add, BPZ_add_left, firstLaw, secondLaw]
    ring
  | single sites scalar =>
    have singleBasis : Finsupp.single sites scalar = scalar • basis sites := by simp [basis]
    rw [singleBasis, map_smul, Pi_basis, BPZ_linear_left, BPZ_linear_left,
      BPZ_linear_left, BPZ_basis, BPZ_basis, Pi_coeff]
    have opposite : ((-1 : ℂ) ^ sites.card) * ((-1 : ℂ) ^ (chi sites).card) = -1 := by
      rw [← pow_add, chi_card_add, pow_add, pow_mul]
      norm_num
    linear_combination scalar * eps sites * stateRight (chi sites) * opposite

private theorem eps_empty : eps ∅ = -1 := by
  simp [eps, rawBasisOperator, reverseSign, basisWord, reversedWord, topCoeff, basis, chi]

private theorem eps_top : eps topSites = -1 := by
  have target : chi topSites = ∅ := by decide
  have word : basisWord topSites = [1, 3, 5] := by
    change basisWord (insert 1 (insert 3 {5})) = _
    rw [basisWord_insert_min 1 (insert 3 {5}) (by
      intro other member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl <;> omega),
      basisWord_insert_min 3 {5} (by
        intro other member
        have equality : other = 5 := by simpa using member
        omega), basisWord_singleton]
  rw [eps, target, rawBasisOperator, word]
  norm_num [topCoeff, reverseSign, reversedWord, topSites, basis,
    bpzSite, b, c, create, annihilate, Finsupp.linearCombination_single,
    createBasis, annihilateBasis, sign, Finset.filter_insert, Finset.filter_singleton,
    Module.End.mul_apply, show (0 : ℤ).toNat = 0 from rfl,
    show (1 : ℤ).toNat = 1 from rfl, show (2 : ℤ).toNat = 2 from rfl]

private theorem BPZ_vacuum_symmetric (state : GhostFock) :
    BPZ (basis ∅) state = BPZ state (basis ∅) := by
  have emptyTarget : chi ∅ = topSites := by decide
  have topTarget : chi topSites = ∅ := by decide
  rw [BPZ_basis, eps_empty, emptyTarget, BPZ_sum]
  have collapse : (∑ sites ∈ state.support,
      state sites * eps sites * basis ∅ (chi sites)) = -state topSites := by
    rw [Finset.sum_eq_single topSites]
    · simp [topTarget, eps_top, basis]
    · intro sites member different
      have targetDifferent : chi sites ≠ ∅ := by
        intro equality
        have recover := congrArg chi equality
        rw [chi_involutive, emptyTarget] at recover
        exact different recover
      simp [basis, Finsupp.single_apply, targetDifferent, Ne.symm targetDifferent]
    · intro outside
      have zeroCoefficient : state topSites = 0 := by
        simpa only [Finsupp.mem_support_iff, not_not] using outside
      simp [zeroCoefficient]
  rw [collapse]
  ring

private theorem BPZ_bpzSite (site : ℕ) (stateLeft stateRight : GhostFock) :
    BPZ (bpzSite site stateLeft) stateRight = BPZ (Pi stateLeft) (create site stateRight) := by
  let index := site / 2
  by_cases even : site % 2 = 0
  · have encoding : site = 2 * index := by dsimp [index]; omega
    rw [encoding, bpzSite_even, LinearMap.smul_apply, BPZ_linear_left, BPZ_b]
    have phase : (-1 : ℂ) ^ ((index : ℤ) + 2) = (-1 : ℂ) ^ index := by
      rw [zpow_add₀ (by norm_num)]
      norm_num
    rw [phase, ← mul_assoc, scalar_sign_square]
    have mode : -((index : ℤ) + 2) ≤ -2 := by omega
    have nativeIndex : (-(-((index : ℤ) + 2)) - 2).toNat = index := by omega
    simp only [one_mul, b, if_pos mode, nativeIndex]
  · have encoding : site = 2 * index + 1 := by dsimp [index]; omega
    rw [encoding, bpzSite_odd, LinearMap.smul_apply, BPZ_linear_left, BPZ_c]
    have phase : (-1 : ℂ) ^ ((index : ℤ) - 1 - 1) = (-1 : ℂ) ^ index := by
      rw [show (index : ℤ) - 1 - 1 = (index : ℤ) - 2 by omega,
        zpow_sub₀ (by norm_num)]
      norm_num
    rw [phase, ← mul_assoc, scalar_sign_square]
    have mode : -((index : ℤ) - 1) ≤ 1 := by omega
    have nativeIndex : (1 - (-((index : ℤ) - 1))).toNat = index := by omega
    simp only [one_mul, c, if_pos mode, nativeIndex]

theorem BPZ_symmetric (stateLeft stateRight : GhostFock) :
    BPZ stateLeft stateRight = BPZ stateRight stateLeft := by
  have basisSymmetric (sites : Finset ℕ) (state : GhostFock) :
      BPZ (basis sites) state = BPZ state (basis sites) := by
    induction sites using Finset.induction_on_min generalizing state with
    | empty => exact BPZ_vacuum_symmetric state
    | @insert head sites minimal inductionHypothesis =>
      have absent : head ∉ sites := fun member => (lt_irrefl head) (minimal head member)
      have emptyFilter : sites.filter (fun other => other < head) = ∅ := by
        apply Finset.filter_false_of_mem
        intro other member
        exact not_lt.mpr (minimal other member).le
      have insertion : create head (basis sites) = basis (insert head sites) := by
        simp [create, createBasis, basis, absent, sign, emptyFilter]
      rw [← insertion, BPZ_create, Pi_basis, BPZ_linear_left,
        inductionHypothesis, BPZ_bpzSite]
      have parityLaw := BPZ_Pi_both state (create head (basis sites))
      rw [Pi_create, Pi_basis, map_smul, BPZ_neg_right, BPZ_linear_right] at parityLaw
      linear_combination -parityLaw
  classical
  induction stateLeft using Finsupp.induction_linear with
  | zero => simp [BPZ]
  | add first second firstLaw secondLaw =>
    simp only [BPZ_add_left, BPZ_add_right, firstLaw, secondLaw]
  | single sites scalar =>
    have singleBasis : Finsupp.single sites scalar = scalar • basis sites := by simp [basis]
    rw [singleBasis, BPZ_linear_left, BPZ_linear_right, basisSymmetric]

private theorem conjCoeffs_add (first second : GhostFock) :
    conjCoeffs (first + second) = conjCoeffs first + conjCoeffs second := by
  ext sites
  simp [conjCoeffs]

private theorem conjCoeffs_basis (sites : Finset ℕ) : conjCoeffs (basis sites) = basis sites := by
  simp [conjCoeffs, basis]

private theorem conjCoeffs_involutive (state : GhostFock) :
    conjCoeffs (conjCoeffs state) = state := by
  ext sites
  simp [conjCoeffs]

private theorem BPZ_conjugate (stateLeft stateRight : GhostFock) :
    star (BPZ stateLeft stateRight) = BPZ (conjCoeffs stateLeft) (conjCoeffs stateRight) := by
  classical
  induction stateLeft using Finsupp.induction_linear with
  | zero => simp [conjCoeffs, BPZ]
  | add first second firstLaw secondLaw =>
    simp only [BPZ_add_left, star_add, conjCoeffs_add, firstLaw, secondLaw]
  | single sites scalar =>
    have singleBasis : Finsupp.single sites scalar = scalar • basis sites := by simp [basis]
    rw [singleBasis, BPZ_linear_left, conjCoeffs_smul, conjCoeffs_basis,
      BPZ_linear_left, BPZ_basis, BPZ_basis]
    simp [conjCoeffs, eps_real, mul_assoc]

theorem Hghost_hermitian (stateLeft stateRight : GhostFock) :
    Hghost stateLeft stateRight = star (Hghost stateRight stateLeft) := by
  rw [Hghost, Hghost, BPZ_conjugate, conjCoeffs_involutive, BPZ_symmetric]

end
end D5.S3.VertexAlgebra.BcGhostBpZForm
