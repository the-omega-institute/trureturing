/- GID: D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Exact
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourVacuumC2Exact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact dimension three of the literal norm-four vacuum C2 quotient. -/

import D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2
import Mathlib.LinearAlgebra.Dimension.Finite
import Batteries.Tactic.OpenPrivate

/-! The literal actual C2 quotient is separated by low-weight mode calculations.
The classical context is the simple Virasoro vacuum algebra at central charge
one half and Li's C2 construction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Exact

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeActualStateFieldCalculus
open NormFourVirasoroVector NormFourVacuumIrreducible NormFourVacuumC2
open scoped BigOperators VertexOperator

open private word wordGrade word_mem word_eigen gradeSpace grade_eigen
  commute_action assemble components_mem
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible
open private coefficient_weight_eigen translation_axis
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra

noncomputable section

private def pair (D : LatticeData) (a : Charge D) (s : ℂ)
    (p : List ℕ × List ℕ) : Carrier D :=
  mu D (word D a s p.1) (-2) (word D a s p.2)

private def pairGrade (p : List ℕ × List ℕ) : ℕ :=
  wordGrade p.1 + wordGrade p.2 + 1

-- Genuine double span induction: neither state of C2 is enlarged to the ambient carrier.
private theorem pair_span (D : LatticeData) (a : Charge D) (s : ℂ) :
    C2 D a s = Submodule.span ℂ (Set.range (pair D a s)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨u, v, hu, hv, rfl⟩
    induction hu using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨w, rfl⟩ := hu
        induction hv using Submodule.span_induction with
        | mem v hv =>
            obtain ⟨t, rfl⟩ := hv
            exact Submodule.subset_span ⟨(w,t), rfl⟩
        | zero => simp [mu]
        | add v z _ _ h₁ h₂ =>
            change mu D (word D a s w) (-2) (v + z) ∈
              Submodule.span ℂ (Set.range (pair D a s))
            simpa only [mu, map_add] using (Submodule.span ℂ
              (Set.range (pair D a s))).add_mem h₁ h₂
        | smul c v _ h =>
            change mu D (word D a s w) (-2) (c • v) ∈
              Submodule.span ℂ (Set.range (pair D a s))
            simpa only [mu, map_smul] using (Submodule.span ℂ
              (Set.range (pair D a s))).smul_mem c h
    | zero => simp [mu]
    | add u z _ _ h₁ h₂ =>
        change mu D (u + z) (-2) v ∈ Submodule.span ℂ (Set.range (pair D a s))
        simpa only [mu, map_add, LinearMap.add_apply, Pi.add_apply] using
          (Submodule.span ℂ (Set.range (pair D a s))).add_mem h₁ h₂
    | smul c u _ h =>
        change mu D (c • u) (-2) v ∈ Submodule.span ℂ (Set.range (pair D a s))
        simpa only [mu, map_smul, LinearMap.smul_apply, Pi.smul_apply] using
          (Submodule.span ℂ (Set.range (pair D a s))).smul_mem c h
  · apply Submodule.span_le.mpr
    rintro z ⟨p, rfl⟩
    exact Submodule.subset_span ⟨word D a s p.1, word D a s p.2,
      word_mem D a s p.1, word_mem D a s p.2, rfl⟩

private def pairSpace (D : LatticeData) (a : Charge D) (s : ℂ) (n : ℕ) :
    Submodule ℂ (Carrier D) :=
  Submodule.span ℂ {z | ∃ p, pairGrade p = n ∧ pair D a s p = z}

private theorem pair_eigen (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (p : List ℕ × List ℕ) :
    mode D a s 0 (pair D a s p) = (pairGrade p : ℂ) • pair D a s p := by
  let u : vacuumDescendants D a s := ⟨word D a s p.1, word_mem D a s p.1⟩
  let v : vacuumDescendants D a s := ⟨word D a s p.2, word_mem D a s p.2⟩
  have hu : u ∈ NormFourVacuumVertexAlgebra.grade D a s (wordGrade p.1) :=
    Submodule.subset_span ⟨p.1, rfl, rfl⟩
  have hv : v ∈ NormFourVacuumVertexAlgebra.grade D a s (wordGrade p.2) :=
    Submodule.subset_span ⟨p.2, rfl, rfl⟩
  have h := coefficient_weight_eigen D a ha s hs (wordGrade p.1)
    (wordGrade p.2) (-2) u v hu hv
  convert h using 1 <;> simp [pair, pairGrade, u, v, mu] <;> push_cast <;> ring

private theorem pair_space_eigen (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (n : ℕ) (z : Carrier D) (hz : z ∈ pairSpace D a s n) :
    mode D a s 0 z = (n : ℂ) • z := by
  have le : pairSpace D a s n ≤ (mode D a s 0).eigenspace (n : ℂ) := by
    apply Submodule.span_le.mpr
    rintro z ⟨p, hp, rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr (by
      simpa only [hp] using pair_eigen D a ha s hs p)
  exact Module.End.mem_eigenspace_iff.mp (le hz)

private theorem c2_stable (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (z : Carrier D) (hz : z ∈ C2 D a s) : mode D a s 0 z ∈ C2 D a s := by
  rw [pair_span] at hz ⊢
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨p, rfl⟩ := hz
      rw [pair_eigen D a ha s hs]
      exact (Submodule.span ℂ (Set.range (pair D a s))).smul_mem _
        (Submodule.subset_span ⟨p,rfl⟩)
  | zero => simp
  | add z t _ _ hz ht => simpa only [map_add] using
      (Submodule.span ℂ (Set.range (pair D a s))).add_mem hz ht
  | smul c z _ hz => simpa only [map_smul] using
      (Submodule.span ℂ (Set.range (pair D a s))).smul_mem c hz

private theorem c2_decompose (D : LatticeData) (a : Charge D) (s : ℂ)
    (z : Carrier D) (hz : z ∈ C2 D a s) :
    ∃ f : ℕ →₀ Carrier D, assemble D f = z ∧ ∀ n, f n ∈ pairSpace D a s n := by
  rw [pair_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨p, rfl⟩ := hz
      refine ⟨Finsupp.single (pairGrade p) (pair D a s p), ?_, ?_⟩
      · simp [assemble, Finsupp.lsum_single]
      · intro n
        by_cases hn : pairGrade p = n
        · subst n
          simp only [Finsupp.single_eq_same]
          exact Submodule.subset_span ⟨p, rfl, rfl⟩
        · simp [hn]
  | zero => exact ⟨0, map_zero _, fun n => by simp⟩
  | add z t _ _ hz ht =>
      obtain ⟨f,hf,hfg⟩ := hz
      obtain ⟨g,hg,hgg⟩ := ht
      exact ⟨f+g, by rw [map_add,hf,hg], fun n =>
        (pairSpace D a s n).add_mem (hfg n) (hgg n)⟩
  | smul c z _ hz =>
      obtain ⟨f,hf,hfg⟩ := hz
      exact ⟨c • f, by rw [map_smul,hf], fun n =>
        (pairSpace D a s n).smul_mem c (hfg n)⟩

-- Uniqueness is reused from the accepted finite polynomial projector, not assumed.
private theorem homogeneous_in_pair_space (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (n : ℕ) (z : Carrier D) (hz : z ∈ C2 D a s)
    (he : mode D a s 0 z = (n : ℂ) • z) : z ∈ pairSpace D a s n := by
  obtain ⟨f,hf,hfg⟩ := c2_decompose D a s z hz
  let g : ℕ →₀ Carrier D := f - Finsupp.single n z
  have eg (m : ℕ) : mode D a s 0 (g m) = (m : ℂ) • g m := by
    by_cases hm : m = n
    · subst m
      simpa only [g, Finsupp.sub_apply, Finsupp.single_eq_same, map_sub,
        pair_space_eigen D a ha s hs n _ (hfg n), he, smul_sub]
    · simpa only [g, Finsupp.sub_apply, Finsupp.single_eq_of_ne hm,
        sub_zero] using pair_space_eigen D a ha s hs m _ (hfg m)
  have hg : assemble D g ∈ (⊥ : Submodule ℂ (Carrier D)) := by
    change assemble D g = 0
    dsimp only [g]
    rw [map_sub, hf]
    simp [assemble, Finsupp.lsum_single]
  have vanish := components_mem D a s g eg ⊥
    (by intro v hv; have hz : v = 0 := hv; subst v; simp) hg n
  have hn : f n = z := sub_eq_zero.mp (by simpa [g] using vanish)
  rw [← hn]
  exact hfg n

private theorem word_grade_zero (w : List ℕ) (h : wordGrade w = 0) : w = [] := by
  cases w with
  | nil => rfl
  | cons k w => simp only [wordGrade] at h; omega

private theorem minus_one_vacuum (D : LatticeData) (a : Charge D) (s : ℂ) :
    mode D a s (-1) (vacuum D) = 0 := by
  simpa only [mode, show (-1:ℤ)+1=0 by omega] using
    stateField_creativity D (vector D a s) 0 (by omega)

private theorem word_grade_one (D : LatticeData) (a : Charge D) (s : ℂ)
    (w : List ℕ) (h : wordGrade w = 1) : word D a s w = 0 := by
  cases w with
  | nil => simp [wordGrade] at h
  | cons k w =>
      have hk : k = 0 := by simp only [wordGrade] at h; omega
      have hw : wordGrade w = 0 := by simp only [wordGrade] at h; omega
      subst k
      rw [word_grade_zero w hw]
      exact minus_one_vacuum D a s

private theorem left_vacuum (D : LatticeData) (v : Carrier D) :
    mu D (vacuum D) (-2) v = 0 := by
  simp [mu, stateField_vacuum, identity_modes]

private theorem pair_space_zero (D : LatticeData) (a : Charge D) (s : ℂ) :
    pairSpace D a s 0 = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro z ⟨p,hp,rfl⟩
  simp only [pairGrade] at hp
  omega

private theorem pair_space_two (D : LatticeData) (a : Charge D) (s : ℂ) :
    pairSpace D a s 2 = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro z ⟨⟨w,t⟩,hp,rfl⟩
  have sum : wordGrade w + wordGrade t = 1 := by simp [pairGrade] at hp; omega
  by_cases hw : wordGrade w = 0
  · rw [word_grade_zero w hw]
    simp [pair, word, left_vacuum]
  · have hw : wordGrade w = 1 := by omega
    simp [pair, word_grade_one D a s w hw, mu]

private theorem word_grade_three (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (w : List ℕ) (hw : wordGrade w = 3) :
    word D a s w ∈ Submodule.span ℂ {mode D a s (-3) (vacuum D)} := by
  have enum : w = [0,0,0] ∨ w = [0,1] ∨ w = [1,0] ∨ w = [2] := by
    cases w with
    | nil => simp [wordGrade] at hw
    | cons k w =>
        cases w with
        | nil =>
            have hk : k = 2 := by simp only [wordGrade] at hw; omega
            subst k
            exact Or.inr (Or.inr (Or.inr rfl))
        | cons l w =>
            cases w with
            | nil =>
                have hkl : k = 0 ∧ l = 1 ∨ k = 1 ∧ l = 0 := by
                  simp only [wordGrade] at hw
                  omega
                rcases hkl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact Or.inr (Or.inl rfl)
                · exact Or.inr (Or.inr (Or.inl rfl))
            | cons m w =>
                cases w with
                | nil =>
                    have hklm : k = 0 ∧ l = 0 ∧ m = 0 := by
                      simp only [wordGrade] at hw
                      omega
                    rcases hklm with ⟨rfl, rfl, rfl⟩
                    exact Or.inl rfl
                | cons q w => simp only [wordGrade] at hw; omega
  have move : mode D a s (-1) (mode D a s (-2) (vacuum D)) =
      mode D a s (-3) (vacuum D) := by
    have h := commute_action D a ha s hs (-1) (-2) (vacuum D)
    norm_num [minus_one_vacuum] at h
    exact h
  rcases enum with rfl | rfl | rfl | rfl
  · simp [word, minus_one_vacuum]
  · change mode D a s (-1) (mode D a s (-2) (vacuum D)) ∈
      Submodule.span ℂ {mode D a s (-3) (vacuum D)}
    rw [move]
    exact Submodule.subset_span (by simp)
  · simp [word, minus_one_vacuum]
  · exact Submodule.subset_span (by simp [word])

private theorem derivative_three (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    translation D (mode D a s (-3) (vacuum D)) =
      (2:ℂ) • mode D a s (-4) (vacuum D) := by
  have mem : mode D a s (-3) (vacuum D) ∈ vacuumDescendants D a s :=
    word_mem D a s [2]
  rw [translation_axis D a ha s hs _ mem]
  have h := commute_action D a ha s hs (-1) (-3) (vacuum D)
  norm_num [minus_one_vacuum] at h
  exact h

private theorem pair_space_four (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    pairSpace D a s 4 ≤ Submodule.span ℂ {mode D a s (-4) (vacuum D)} := by
  apply Submodule.span_le.mpr
  rintro z ⟨⟨w,t⟩,hp,rfl⟩
  have sum : wordGrade w + wordGrade t = 3 := by simp [pairGrade] at hp; omega
  by_cases hw0 : wordGrade w = 0
  · rw [word_grade_zero w hw0]
    simp [pair,word,left_vacuum]
  by_cases hw1 : wordGrade w = 1
  · simp [pair,word_grade_one D a s w hw1,mu]
  by_cases ht1 : wordGrade t = 1
  · simp [pair,word_grade_one D a s t ht1,mu]
  have hw3 : wordGrade w = 3 := by omega
  have ht0 : wordGrade t = 0 := by omega
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp
    (word_grade_three D a ha s hs w hw3)
  rw [show pair D a s (w,t) = translation D (word D a s w) by
    simp only [pair,word_grade_zero t ht0,word]
    exact (LatticeActualVertexAlgebra.translation_as_mode D (word D a s w)).symm]
  rw [← hc, map_smul, derivative_three D a ha s hs]
  exact (Submodule.span ℂ {mode D a s (-4) (vacuum D)}).smul_mem c
    ((Submodule.span ℂ {mode D a s (-4) (vacuum D)}).smul_mem 2
      (Submodule.subset_span (by simp)))

private theorem vacuum_mode (D : LatticeData) (a : Charge D) (s : ℂ)
    (m : ℤ) (hm : -1 ≤ m) : mode D a s m (vacuum D) = 0 :=
  stateField_creativity D (vector D a s) (m+1) (by omega)

private def e (D : LatticeData) (a : Charge D) (s : ℂ) : Carrier D :=
  mode D a s (-2) (vacuum D)

private def b (D : LatticeData) (a : Charge D) (s : ℂ) : Carrier D :=
  mode D a s (-2) (e D a s)

private def d (D : LatticeData) (a : Charge D) (s : ℂ) : Carrier D :=
  mode D a s (-4) (vacuum D)

-- These are calculations in the actual carrier from the accepted commutator.
-- They do not interpret formal words as linearly independent PBW monomials.
private theorem low_actions (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    mode D a s 0 (e D a s) = (2:ℂ) • e D a s ∧
    mode D a s 2 (e D a s) = (1/4:ℂ) • vacuum D ∧
    mode D a s 4 (e D a s) = 0 ∧
    mode D a s 0 (b D a s) = (4:ℂ) • b D a s ∧
    mode D a s 4 (d D a s) = (5/2:ℂ) • vacuum D ∧
    mode D a s 4 (b D a s) = (3/2:ℂ) • vacuum D ∧
    mode D a s 2 (mode D a s 2 (d D a s)) = (3/2:ℂ) • vacuum D ∧
    mode D a s 2 (mode D a s 2 (b D a s)) = (17/8:ℂ) • vacuum D := by
  have e0 : mode D a s 0 (e D a s) = (2:ℂ) • e D a s := by
    have h := commute_action D a ha s hs 0 (-2) (vacuum D)
    norm_num [e, vacuum_mode D a s 0 (by omega)] at h ⊢
    exact h
  have e2 : mode D a s 2 (e D a s) = (1/4:ℂ) • vacuum D := by
    have h := commute_action D a ha s hs 2 (-2) (vacuum D)
    norm_num [e, vacuum_mode D a s 0 (by omega),
      vacuum_mode D a s 2 (by omega)] at h ⊢
    exact h
  have e4 : mode D a s 4 (e D a s) = 0 := by
    have h := commute_action D a ha s hs 4 (-2) (vacuum D)
    norm_num [e, vacuum_mode D a s 2 (by omega),
      vacuum_mode D a s 4 (by omega)] at h ⊢
    exact h
  have b0 : mode D a s 0 (b D a s) = (4:ℂ) • b D a s := by
    have h := commute_action D a ha s hs 0 (-2) (e D a s)
    norm_num [b, e0, map_smul] at h ⊢
    rw [h]
    module
  have d4 : mode D a s 4 (d D a s) = (5/2:ℂ) • vacuum D := by
    have h := commute_action D a ha s hs 4 (-4) (vacuum D)
    norm_num [d, vacuum_mode D a s 0 (by omega),
      vacuum_mode D a s 4 (by omega)] at h ⊢
    exact h
  have b4 : mode D a s 4 (b D a s) = (3/2:ℂ) • vacuum D := by
    have h := commute_action D a ha s hs 4 (-2) (e D a s)
    norm_num [b, e2, e4, smul_smul] at h ⊢
    exact h
  have d2 : mode D a s 2 (d D a s) = (6:ℂ) • e D a s := by
    have h := commute_action D a ha s hs 2 (-4) (vacuum D)
    norm_num [d, e, vacuum_mode D a s 2 (by omega)] at h ⊢
    exact h
  have b2 : mode D a s 2 (b D a s) = (17/2:ℂ) • e D a s := by
    have h := commute_action D a ha s hs 2 (-2) (e D a s)
    norm_num [b, e2, e0, map_smul, smul_smul] at h ⊢
    rw [h]
    change (1/4:ℂ) • e D a s + 8 • e D a s + (1/4:ℂ) • e D a s =
      (17/2:ℂ) • e D a s
    module
  refine ⟨e0,e2,e4,b0,d4,b4,?_,?_⟩
  · rw [d2,map_smul,e2,smul_smul]
    norm_num
  · rw [b2,map_smul,e2,smul_smul]
    norm_num

private def separator (D : LatticeData) (a : Charge D) (s : ℂ) :
    Module.End ℂ (Carrier D) :=
  (5/2:ℂ) • (mode D a s 2 * mode D a s 2) - (3/2:ℂ) • mode D a s 4

private theorem separator_values (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    separator D a s (d D a s) = 0 ∧
      separator D a s (b D a s) = (49/16:ℂ) • vacuum D := by
  obtain ⟨_,_,_,_,d4,b4,d22,b22⟩ := low_actions D a ha s hs
  constructor <;> simp only [separator, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, d4,b4,d22,b22,smul_smul] <;> module

private theorem scalar_vacuum_zero (D : LatticeData) (c : ℂ)
    (h : c • vacuum D = 0) : c = 0 :=
  (smul_eq_zero.mp h).resolve_right (LatticePositiveEnergy.vacuum_nonzero D)

-- Isolate the three actual homogeneous components inside literal C2.
private theorem coefficients_zero (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (α β γ : ℂ)
    (h : α • vacuum D + β • e D a s + γ • b D a s ∈ C2 D a s) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  obtain ⟨e0,e2,_,b0,_,_,_,_⟩ := low_actions D a ha s hs
  let f : ℕ →₀ Carrier D := Finsupp.single 0 (α • vacuum D) +
    Finsupp.single 2 (β • e D a s) + Finsupp.single 4 (γ • b D a s)
  have fe (n : ℕ) : mode D a s 0 (f n) = (n:ℂ) • f n := by
    by_cases h0 : n = 0
    · subst n
      simp [f,map_smul,vacuum_mode D a s 0 (by omega)]
    by_cases h2 : n = 2
    · subst n
      simp [f,map_smul,e0,smul_smul,mul_comm]
    by_cases h4 : n = 4
    · subst n
      simp [f,map_smul,b0,smul_smul,mul_comm]
    · simp [f,h0,h2,h4,Ne.symm h0,Ne.symm h2,Ne.symm h4]
  have fm (n : ℕ) : f n ∈ C2 D a s := components_mem D a s f fe
    (C2 D a s) (c2_stable D a ha s hs) (by
      dsimp only [f]
      simp only [map_add]
      simpa [assemble, Finsupp.lsum_single] using h) n
  have z0 : α • vacuum D = 0 := by
    have h := homogeneous_in_pair_space D a ha s hs 0 (f 0) (fm 0) (fe 0)
    simpa [pair_space_zero,f] using h
  have z2 : β • e D a s = 0 := by
    have h := homogeneous_in_pair_space D a ha s hs 2 (f 2) (fm 2) (fe 2)
    simpa [pair_space_two,f] using h
  have z4 : γ • b D a s ∈ Submodule.span ℂ {d D a s} := by
    have h := pair_space_four D a ha s hs
      (homogeneous_in_pair_space D a ha s hs 4 (f 4) (fm 4) (fe 4))
    simpa [f,d] using h
  have α0 := scalar_vacuum_zero D α z0
  have β0 : β = 0 := by
    have h := congrArg (mode D a s 2) z2
    have h' : (β * (1/4:ℂ)) • vacuum D = 0 := by
      simpa only [map_smul,e2,smul_smul,map_zero] using h
    have scalar := scalar_vacuum_zero D _ h'
    exact (mul_eq_zero.mp scalar).resolve_right (by norm_num)
  have γ0 : γ = 0 := by
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp z4
    have equal := congrArg (separator D a s) hc
    obtain ⟨sd,sb⟩ := separator_values D a ha s hs
    have h' : (γ * (49/16:ℂ)) • vacuum D = 0 := by
      simpa only [map_smul,sd,sb,smul_zero,smul_smul] using equal.symm
    have scalar := scalar_vacuum_zero D _ h'
    exact (mul_eq_zero.mp scalar).resolve_right (by norm_num)
  exact ⟨α0,β0,γ0⟩

private def representative (D : LatticeData) (a : Charge D) (s : ℂ) (i : Fin 3) :
    Carrier D := ![vacuum D,e D a s,b D a s] i

private theorem representative_mem (D : LatticeData) (a : Charge D) (s : ℂ)
    (i : Fin 3) : representative D a s i ∈ vacuumDescendants D a s := by
  fin_cases i
  · exact word_mem D a s []
  · exact word_mem D a s [1]
  · exact word_mem D a s [1,1]

private def quotientRepresentative (D : LatticeData) (a : Charge D) (s : ℂ) :
    Fin 3 → vacuumDescendants D a s ⧸
      (C2 D a s).comap (vacuumDescendants D a s).subtype :=
  fun i => Submodule.Quotient.mk ⟨representative D a s i,representative_mem D a s i⟩

private theorem quotient_independent (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    LinearIndependent ℂ (quotientRepresentative D a s) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let S := vacuumDescendants D a s
  let C := (C2 D a s).comap S.subtype
  let r : Fin 3 → S := fun i => ⟨representative D a s i,representative_mem D a s i⟩
  have hq : C.mkQ (∑ i, g i • r i) = 0 := by
    simp only [map_sum, map_smul]
    change (∑ i, g i • quotientRepresentative D a s i) = 0
    exact hg
  have hm : (∑ i, g i • r i : S).val ∈ C2 D a s :=
    (Submodule.Quotient.mk_eq_zero C).mp hq
  have hz := coefficients_zero D a ha s hs (g 0) (g 1) (g 2) (by
    simpa [Fin.sum_univ_succ,r,representative,add_assoc] using hm)
  fin_cases i
  · exact hz.1
  · exact hz.2.1
  · exact hz.2.2

/-- Exact dimension of the literal actual C2 quotient. The lower
bound comes from low-weight two-state generator analysis and an actual-mode
separator, with no PBW, positivity, rootlessness or independence premise. -/
theorem actual_vacuum_c2_dimension (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    let S := vacuumDescendants D a s
    let C := (C2 D a s).comap S.subtype
    FiniteDimensional ℂ (S ⧸ C) ∧ Module.finrank ℂ (S ⧸ C) = 3 := by
  obtain ⟨_,finite,upper⟩ := actual_vacuum_c2_cofinite D a ha s hs
  letI := finite
  refine ⟨finite,le_antisymm upper ?_⟩
  simpa using (quotient_independent D a ha s hs).fintype_card_le_finrank

end
end D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Exact
