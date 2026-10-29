/- GID: D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The largest strongly complementary permutation family has size two to the valuation. -/

import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.GroupTheory.PGroup
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! The matrix convention is `σ.permMatrix ℕ i j = 1 ↔ σ i = j`.
The definitions are Definitions 4.1 and 4.3 of Rajchel–Gąsiorowski–Życzkowski,
arXiv:1804.10715v2. Only the maximum-cardinality question is addressed.
Admission basis: external open-problem resolution, preregistration #23851. -/

namespace StronglyComplementaryPermutationMaximum

open scoped BigOperators

/-- Complementarity, with all four indices quantified as in Definition 4.1. -/
def IsComplementary {α : Type*} (p q : Matrix α α ℕ) : Prop :=
  ∀ i j h k, p i j = 1 → p h k = 1 → q i k = 1 → q h j = 1

/-- Complementarity together with disjoint support, as in Definition 4.3. -/
def IsStronglyComplementary {α : Type*} (p q : Matrix α α ℕ) : Prop :=
  IsComplementary p q ∧ ∀ i j, p i j = 1 → q i j = 0

/-- A matrix arising from a permutation of its indices. -/
def IsPermutationMatrix {α : Type*} [DecidableEq α] (p : Matrix α α ℕ) : Prop :=
  ∃ σ : Equiv.Perm α, p = σ.permMatrix ℕ

/-- The supremum of the attained cardinalities of finite, pairwise strongly
complementary sets of permutation matrices. -/
noncomputable def maxStronglyComplementary (n : ℕ) : ℕ :=
  sSup {k | ∃ s : Finset (Matrix (Fin n) (Fin n) ℕ),
    (∀ p ∈ s, IsPermutationMatrix p) ∧
      (s : Set (Matrix (Fin n) (Fin n) ℕ)).Pairwise IsStronglyComplementary ∧ s.card = k}

/-- The cardinality clause of the question in arXiv:1804.10715v2. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → maxStronglyComplementary n = 2 ^ padicValNat 2 n

private lemma entry_one {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (i j : α) :
    σ.permMatrix ℕ i j = 1 ↔ σ i = j := by
  change σ.toPEquiv.toMatrix i j = 1 ↔ σ i = j
  rw [PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
  by_cases h : j = σ i
  · simp only [h, ite_eq_left]
  · simp only [h, ite_false, Nat.zero_ne_one, false_iff]
    exact Ne.symm h

private lemma entry_zero {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (i j : α) :
    σ.permMatrix ℕ i j = 0 ↔ σ i ≠ j := by
  change σ.toPEquiv.toMatrix i j = 0 ↔ σ i ≠ j
  rw [PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
  by_cases h : j = σ i
  · simp only [h, ite_eq_left, Nat.one_ne_zero, ne_eq, not_true_eq_false]
  · simp only [h, ite_false, true_iff]
    exact Ne.symm h

private lemma matrix_injective {α : Type*} [DecidableEq α] :
    Function.Injective (fun σ : Equiv.Perm α => σ.permMatrix ℕ) := by
  intro σ τ h
  have he : σ.toPEquiv = τ.toPEquiv := PEquiv.toMatrix_injective h
  apply Equiv.ext
  intro x
  exact Option.some.inj (congrArg (fun f : PEquiv α α => f x) he)

private lemma complementary_iff {α : Type*} [DecidableEq α] (σ τ : Equiv.Perm α) :
    IsComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ) ↔
      Function.Involutive (σ⁻¹ * τ) := by
  constructor
  · intro hp x
    change σ.symm (τ (σ.symm (τ x))) = x
    apply σ.injective
    rw [σ.apply_symm_apply]
    apply (entry_one τ _ _).mp
    exact hp x (σ x) (σ.symm (τ x)) (τ x)
      ((entry_one σ _ _).mpr rfl)
      ((entry_one σ _ _).mpr (σ.apply_symm_apply (τ x)))
      ((entry_one τ _ _).mpr rfl)
  · intro hi i j h k hpij hphk hqik
    have hx : σ.symm (τ i) = h := by
      apply σ.injective
      rw [σ.apply_symm_apply, (entry_one τ _ _).mp hqik,
        (entry_one σ _ _).mp hphk]
    have hh := hi i
    change σ.symm (τ (σ.symm (τ i))) = i at hh
    rw [hx] at hh
    apply (entry_one τ _ _).mpr
    calc
      τ h = σ i := by simpa only [σ.apply_symm_apply] using congrArg σ hh
      _ = j := (entry_one σ _ _).mp hpij

private lemma strong_iff {α : Type*} [DecidableEq α] (σ τ : Equiv.Perm α) :
    IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ) ↔
      Function.Involutive (σ⁻¹ * τ) ∧ ∀ x, (σ⁻¹ * τ) x ≠ x := by
  change (IsComplementary _ _ ∧ _) ↔ _
  rw [complementary_iff]
  constructor
  · rintro ⟨hi, hd⟩
    refine ⟨hi, fun x hx => ?_⟩
    have hx : τ x = σ x := by
      have h := congrArg σ hx
      change σ (σ.symm (τ x)) = σ x at h
      rwa [σ.apply_symm_apply] at h
    have hz := (entry_zero τ x (σ x)).mp (hd x (σ x) ((entry_one σ _ _).mpr rfl))
    exact hz hx
  · rintro ⟨hi, hf⟩
    refine ⟨hi, fun i j hp => (entry_zero τ i j).mpr ?_⟩
    intro hq
    apply hf i
    change σ.symm (τ i) = i
    rw [hq, ← (entry_one σ _ _).mp hp, σ.symm_apply_apply]

private lemma row_relabelling {α : Type*} [DecidableEq α] (ρ σ τ : Equiv.Perm α) :
    IsStronglyComplementary ((σ * ρ⁻¹).permMatrix ℕ) ((τ * ρ⁻¹).permMatrix ℕ) ↔
      IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ) := by
  rw [strong_iff, strong_iff]
  have he (x : α) : ((σ * ρ⁻¹)⁻¹ * (τ * ρ⁻¹)) x =
      ρ ((σ⁻¹ * τ) (ρ.symm x)) := rfl
  constructor
  · rintro ⟨hi, hf⟩
    constructor
    · intro x
      apply ρ.injective
      simpa only [he, ρ.symm_apply_apply] using hi (ρ x)
    · intro x hx
      apply hf (ρ x)
      rw [he, ρ.symm_apply_apply, hx]
  · rintro ⟨hi, hf⟩
    constructor
    · intro x
      rw [he, he, ρ.symm_apply_apply, hi, ρ.apply_symm_apply]
    · intro x hx
      apply hf (ρ.symm x)
      simpa only [he, ρ.symm_apply_apply] using congrArg ρ.symm hx

private lemma lift_family {n : ℕ} (s : Finset (Matrix (Fin n) (Fin n) ℕ))
    (hs : ∀ p ∈ s, IsPermutationMatrix p) :
    ∃ t : Finset (Equiv.Perm (Fin n)),
      t.image (fun σ => σ.permMatrix ℕ) = s ∧ t.card = s.card := by
  classical
  let t := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.permMatrix ℕ ∈ s)
  have ht : t.image (fun σ => σ.permMatrix ℕ) = s := by
    ext p
    constructor
    · intro h
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hσ).2
    · intro hp
      obtain ⟨σ, rfl⟩ := hs p hp
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩
  refine ⟨t, ht, ?_⟩
  rw [← ht, Finset.card_image_of_injective _ matrix_injective]

private lemma normalize_family {n : ℕ} (s : Finset (Equiv.Perm (Fin n)))
    (hs : (s : Set (Equiv.Perm (Fin n))).Pairwise (fun σ τ =>
      IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ))) (hne : s.Nonempty) :
    ∃ t : Finset (Equiv.Perm (Fin n)), t.card = s.card ∧ 1 ∈ t ∧
      (t : Set (Equiv.Perm (Fin n))).Pairwise (fun σ τ =>
        IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ)) := by
  classical
  obtain ⟨ρ, hρ⟩ := hne
  refine ⟨s.image (fun σ => σ * ρ⁻¹), ?_, ?_, ?_⟩
  · exact Finset.card_image_of_injective _ (mul_left_injective _)
  · exact Finset.mem_image.mpr ⟨ρ, hρ, mul_inv_cancel ρ⟩
  · intro p hp q hq hne
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hq
    exact (row_relabelling ρ σ τ).mpr
      (hs hσ hτ (fun h => hne (congrArg (fun σ => σ * ρ⁻¹) h)))

private lemma normalized_involutions {n : ℕ} (s : Finset (Equiv.Perm (Fin n)))
    (h1 : 1 ∈ s) (hs : (s : Set (Equiv.Perm (Fin n))).Pairwise (fun σ τ =>
      IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ))) :
    (∀ σ ∈ s, σ ^ 2 = 1) ∧ (s : Set (Equiv.Perm (Fin n))).Pairwise Commute := by
  have hi : ∀ σ ∈ s, σ ^ 2 = 1 := by
    intro σ hσ
    by_cases he : σ = 1
    · rw [he, one_pow]
    · have h := (strong_iff 1 σ).mp (hs h1 hσ (Ne.symm he))
      apply Equiv.ext
      intro x
      have hx := h.1 x
      simpa only [inv_one, one_mul, pow_two, Equiv.Perm.mul_apply,
        Equiv.Perm.one_apply] using hx
  refine ⟨hi, ?_⟩
  intro σ hσ τ hτ hne
  have hστ := (strong_iff σ τ).mp (hs hσ hτ hne)
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hi σ hσ)
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hi τ hτ)
  have hprod : (σ * τ) ^ 2 = 1 := by
    apply Equiv.ext
    intro x
    have hx := hστ.1 x
    simpa only [hσi, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using hx
  have hinv : (σ * τ)⁻¹ = σ * τ :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hprod)
  change σ * τ = τ * σ
  rw [← hinv, mul_inv_rev, hτi, hσi]

private lemma closure_exponent_two {n : ℕ} (s : Finset (Equiv.Perm (Fin n)))
    (hs : ∀ σ ∈ s, σ ^ 2 = 1)
    (hc : (s : Set (Equiv.Perm (Fin n))).Pairwise Commute) :
    ∀ g ∈ Subgroup.closure (s : Set (Equiv.Perm (Fin n))), g ^ 2 = 1 := by
  let g := Subgroup.closure (s : Set (Equiv.Perm (Fin n)))
  let : IsMulCommutative g := Subgroup.isMulCommutative_closure hc
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => exact one_pow 2
  | mul x y hx hy hxi hyi =>
    have hcomm : Commute x y := by
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : g) (⟨y, hy⟩ : g))
    rw [hcomm.mul_pow, hxi, hyi, one_mul]
  | inv x hx hxi => rw [inv_pow, hxi, inv_one]

private lemma orbit_evaluation_bound {n : ℕ} (s : Finset (Equiv.Perm (Fin n)))
    (hs : (s : Set (Equiv.Perm (Fin n))).Pairwise (fun σ τ =>
      IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ))) (x : Fin n) :
    s.card ≤ Nat.card (MulAction.orbit (Subgroup.closure (s : Set (Equiv.Perm (Fin n)))) x) := by
  classical
  let f : {σ : Equiv.Perm (Fin n) // σ ∈ s} →
      MulAction.orbit (Subgroup.closure (s : Set (Equiv.Perm (Fin n)))) x := fun σ =>
    ⟨σ.val x, MulAction.mem_orbit_iff.mpr
      ⟨⟨σ.val, Subgroup.subset_closure σ.property⟩, rfl⟩⟩
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    by_contra hne
    have hc := (strong_iff σ.val τ.val).mp (hs σ.property τ.property hne)
    apply hc.2 x
    change σ.val.symm (τ.val x) = x
    have he : σ.val x = τ.val x := congrArg Subtype.val h
    rw [← he, σ.val.symm_apply_apply]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    Nat.card_le_card_of_injective f hf

private lemma least_orbit_divisor {n : ℕ} (hn : 1 ≤ n)
    (g : Subgroup (Equiv.Perm (Fin n))) (hg : IsPGroup 2 g) :
    ∃ x : Fin n, ∃ a : ℕ, Nat.card (MulAction.orbit g x) = 2 ^ a ∧ 2 ^ a ∣ n := by
  classical
  let : Fintype (MulAction.orbitRel.Quotient g (Fin n)) := Fintype.ofFinite _
  let (x : Fin n) : Fintype (MulAction.orbit g x) := Fintype.ofFinite _
  have hex : ∃ a : ℕ, ∃ x : Fin n, Nat.card (MulAction.orbit g x) = 2 ^ a := by
    obtain ⟨a, ha⟩ := hg.card_orbit (⟨0, hn⟩ : Fin n)
    exact ⟨a, ⟨0, hn⟩, ha⟩
  obtain ⟨x, hx⟩ := Nat.find_spec hex
  refine ⟨x, Nat.find hex, hx, ?_⟩
  have hd (y : Fin n) : 2 ^ Nat.find hex ∣ Nat.card (MulAction.orbit g y) := by
    obtain ⟨b, hb⟩ := hg.card_orbit y
    rw [hb]
    exact pow_dvd_pow 2 (Nat.find_min' hex ⟨y, hb⟩)
  have hc := Fintype.card_congr (MulAction.selfEquivSigmaOrbits g (Fin n))
  rw [Fintype.card_sigma] at hc
  have hc : n = ∑ ω : MulAction.orbitRel.Quotient g (Fin n),
      Nat.card (MulAction.orbit g ω.out) := by
    simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using hc
  apply (congrArg (fun k : ℕ => 2 ^ Nat.find hex ∣ k) hc).mpr
  exact Finset.dvd_sum (fun ω _ => hd ω.out)

private lemma permutation_family_upper {n : ℕ} (hn : 1 ≤ n)
    (s : Finset (Equiv.Perm (Fin n))) (hs : (s : Set (Equiv.Perm (Fin n))).Pairwise (fun σ τ =>
      IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ))) :
    s.card ≤ 2 ^ padicValNat 2 n := by
  classical
  by_cases hne : s.Nonempty
  · obtain ⟨t, hcard, h1, ht⟩ := normalize_family s hs hne
    obtain ⟨hi, hc⟩ := normalized_involutions t h1 ht
    have he := closure_exponent_two t hi hc
    have hg : IsPGroup 2 (Subgroup.closure (t : Set (Equiv.Perm (Fin n)))) := by
      intro g
      refine ⟨1, ?_⟩
      apply Subtype.ext
      exact he g g.property
    obtain ⟨x, a, ha, hd⟩ :=
      least_orbit_divisor hn (Subgroup.closure (t : Set (Equiv.Perm (Fin n)))) hg
    have hb := orbit_evaluation_bound t ht x
    rw [ha, hcard] at hb
    exact hb.trans (Nat.pow_le_pow_right (by omega)
      ((padicValNat_dvd_iff_le (by omega)).mp hd))
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [this, Finset.card_empty, Nat.zero_le]

private lemma matrix_family_upper {n : ℕ} (hn : 1 ≤ n)
    (s : Finset (Matrix (Fin n) (Fin n) ℕ)) (hp : ∀ p ∈ s, IsPermutationMatrix p)
    (hs : (s : Set (Matrix (Fin n) (Fin n) ℕ)).Pairwise IsStronglyComplementary) :
    s.card ≤ 2 ^ padicValNat 2 n := by
  classical
  obtain ⟨t, ht, hc⟩ := lift_family s hp
  rw [← hc]
  apply permutation_family_upper hn t
  intro σ hσ τ hτ hne
  apply hs
  · rw [← ht]; exact Finset.mem_image_of_mem _ hσ
  · rw [← ht]; exact Finset.mem_image_of_mem _ hτ
  · exact fun h => hne (matrix_injective h)

private lemma two_adic_decomposition {n : ℕ} (hn : 1 ≤ n) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ n = 2 ^ padicValNat 2 n * m := by
  refine ⟨n.divMaxPow 2, ?_, ?_, (Nat.pow_padicValNat_mul_divMaxPow 2 n).symm⟩
  · have h := Nat.pow_padicValNat_mul_divMaxPow 2 n
    by_contra hm
    have hz : n.divMaxPow 2 = 0 := by omega
    rw [hz, mul_zero] at h
    omega
  · apply Nat.not_even_iff_odd.mp
    intro hm
    exact Nat.not_dvd_divMaxPow (by omega) (by omega) hm.two_dvd

private lemma elementary_translation_family {n a m : ℕ} (hm : 0 < m)
    (e : Fin n ≃ ((Fin a → ZMod 2) × Fin m)) :
    ∃ s : Finset (Equiv.Perm (Fin n)), s.card = 2 ^ a ∧
      (s : Set (Equiv.Perm (Fin n))).Pairwise (fun σ τ =>
        IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ)) := by
  classical
  let t : (Fin a → ZMod 2) → Equiv.Perm (Fin n) := fun v =>
    e.symm.permCongr ((Equiv.addLeft v).prodCongr (Equiv.refl (Fin m)))
  have ht (v : Fin a → ZMod 2) (x : Fin n) :
      e (t v x) = (v + (e x).1, (e x).2) := by
    change e (e.symm (v + (e x).1, (e x).2)) = _
    exact e.apply_symm_apply _
  have htinv (v : Fin a → ZMod 2) (x : Fin n) :
      e ((t v)⁻¹ x) = (-v + (e x).1, (e x).2) := by
    change e (e.symm (-v + (e x).1, (e x).2)) = _
    exact e.apply_symm_apply _
  have hrel (u v : Fin a → ZMod 2) (x : Fin n) :
      e (((t u)⁻¹ * t v) x) = ((v - u) + (e x).1, (e x).2) := by
    change e ((t u)⁻¹ (t v x)) = _
    rw [htinv, ht]
    simp only [sub_eq_add_neg, add_assoc, add_left_comm]
  have hinj : Function.Injective t := by
    intro u v huv
    have h := congrArg (fun σ : Equiv.Perm (Fin n) =>
      (e (σ (e.symm (0, ⟨0, hm⟩)))).1) huv
    change (e (t u (e.symm (0, ⟨0, hm⟩)))).1 =
      (e (t v (e.symm (0, ⟨0, hm⟩)))).1 at h
    rw [ht, ht, e.apply_symm_apply] at h
    simpa only [add_zero] using h
  refine ⟨Finset.univ.image t, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · intro σ hσ τ hτ hne
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hσ
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hτ
    apply (strong_iff (t u) (t v)).mpr
    constructor
    · intro x
      apply e.injective
      rw [hrel, hrel]
      apply Prod.ext
      · change (v - u) + ((v - u) + (e x).1) = (e x).1
        have hz : (v - u) + (v - u) = 0 := by
          funext i
          exact CharTwo.add_self_eq_zero ((v - u) i)
        rw [← add_assoc, hz, zero_add]
      · rfl
    · intro x hx
      have h := congrArg e hx
      rw [hrel] at h
      have hz : v - u = 0 := by
        apply add_right_cancel (b := (e x).1)
        simpa only [zero_add] using congrArg Prod.fst h
      exact hne (congrArg t (sub_eq_zero.mp hz).symm)

private lemma matrix_family_lower {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset (Matrix (Fin n) (Fin n) ℕ),
      (∀ p ∈ s, IsPermutationMatrix p) ∧
      (s : Set (Matrix (Fin n) (Fin n) ℕ)).Pairwise IsStronglyComplementary ∧
        s.card = 2 ^ padicValNat 2 n := by
  classical
  obtain ⟨m, hm, _, hnfac⟩ := two_adic_decomposition hn
  have hcard : Fintype.card (Fin n) =
      Fintype.card ((Fin (padicValNat 2 n) → ZMod 2) × Fin m) := by
    simpa only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
      using hnfac
  obtain ⟨t, ht, htcomp⟩ := elementary_translation_family hm (Fintype.equivOfCardEq hcard)
  refine ⟨t.image (fun σ => σ.permMatrix ℕ), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨σ, rfl⟩
  · intro p hp q hq hne
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hq
    exact htcomp hσ hτ (fun h => hne (congrArg (fun σ => σ.permMatrix ℕ) h))
  · rw [Finset.card_image_of_injective _ matrix_injective, ht]

/-- The maximal size is the largest power of two dividing the dimension. -/
theorem result : claim := by
  intro n hn
  change sSup {k | ∃ s : Finset (Matrix (Fin n) (Fin n) ℕ),
    (∀ p ∈ s, IsPermutationMatrix p) ∧
      (s : Set (Matrix (Fin n) (Fin n) ℕ)).Pairwise IsStronglyComplementary ∧ s.card = k} = _
  obtain ⟨s, hp, hs, hc⟩ := matrix_family_lower hn
  have hb : ∀ k ∈ {k | ∃ t : Finset (Matrix (Fin n) (Fin n) ℕ),
      (∀ p ∈ t, IsPermutationMatrix p) ∧
      (t : Set (Matrix (Fin n) (Fin n) ℕ)).Pairwise IsStronglyComplementary ∧
        t.card = k}, k ≤ 2 ^ padicValNat 2 n := by
    rintro k ⟨t, ht, htcomp, rfl⟩
    exact matrix_family_upper hn t ht htcomp
  apply le_antisymm
  · exact csSup_le ⟨_, s, hp, hs, hc⟩ hb
  · exact le_csSup ⟨_, hb⟩ ⟨s, hp, hs, hc⟩

end StronglyComplementaryPermutationMaximum
