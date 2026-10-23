/- GID: D5/S3/FiniteGroups/ToralCharacterSupport
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/ToralCharacterSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Faithful projective character triples on products of finite cyclic groups. -/

import D5.S3.FiniteGroups.CyclicPrimePowerAction
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-! # Projective matching of complex character triples -/

namespace D5.S3.FiniteGroups.ToralCharacterSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open D5.S3.FiniteGroups.CyclicPrimePowerAction (Cyclic cyclic_card)

abbrev Triple (G : Type*) [Group G] := Fin 3 → (G →* ℂˣ)

def ProjectivelyFaithful {G : Type*} [Group G] (X : Triple G) : Prop :=
  ∀ g, (∀ i, X i g = X 0 g) → g = 1

def PointwiseMatched {G : Type*} [Group G] (X Y : Triple G) : Prop :=
  ∀ g, ∃ l : ℂˣ, ∃ p : Equiv.Perm (Fin 3), ∀ i, Y i g = l * X (p i) g

def GloballyMatched {G : Type*} [Group G] (X Y : Triple G) : Prop :=
  ∃ e : G →* ℂˣ, ∃ p : Equiv.Perm (Fin 3), ∀ i, Y i = e * X (p i)

def Supports (G : Type*) [Group G] : Prop :=
  ∃ X Y : Triple G, ProjectivelyFaithful X ∧ ProjectivelyFaithful Y ∧
    PointwiseMatched X Y ∧ ¬ GloballyMatched X Y

abbrev Source (a b m : ℕ) := Cyclic (2 ^ a) × Cyclic (2 ^ b * m)

private def twist {G : Type*} [Group G] (e : G →* ℂˣ) (X : Triple G) : Triple G :=
  fun i => e * X i

@[simp] private theorem twist_one {G : Type*} [Group G] (X : Triple G) : twist 1 X = X := by
  funext i
  exact one_mul (X i)

private def reindex {G : Type*} [Group G] (p : Equiv.Perm (Fin 3))
    (X : Triple G) : Triple G := fun i => X (p i)

private theorem faithful_twist {G : Type*} [Group G] (e : G →* ℂˣ) (X : Triple G) :
    ProjectivelyFaithful (twist e X) ↔ ProjectivelyFaithful X := by
  simp only [ProjectivelyFaithful, twist, MonoidHom.mul_apply, mul_left_cancel_iff]

private theorem global_twist {G : Type*} [Group G] (e f : G →* ℂˣ)
    (X Y : Triple G) :
    GloballyMatched (twist e X) (twist f Y) ↔ GloballyMatched X Y := by
  constructor
  · rintro ⟨d, p, hd⟩
    refine ⟨f⁻¹ * d * e, p, fun i => ?_⟩
    have hi := hd i
    dsimp [twist] at hi
    calc
      Y i = f⁻¹ * (f * Y i) := by group
      _ = f⁻¹ * (d * (e * X (p i))) := congrArg (f⁻¹ * ·) hi
      _ = f⁻¹ * d * e * X (p i) := by group
  · rintro ⟨d, p, hd⟩
    refine ⟨f * d * e⁻¹, p, fun i => ?_⟩
    dsimp [twist]
    rw [hd i]
    group

private theorem pointwise_twist {G : Type*} [Group G] (e f : G →* ℂˣ)
    {X Y : Triple G} (h : PointwiseMatched X Y) :
    PointwiseMatched (twist e X) (twist f Y) := by
  intro g
  obtain ⟨l, p, hp⟩ := h g
  refine ⟨f g * l / e g, p, fun i => ?_⟩
  simp only [twist, MonoidHom.mul_apply]
  rw [hp i]
  simp [div_eq_mul_inv, mul_assoc]

private theorem global_reindex {G : Type*} [Group G] (p : Equiv.Perm (Fin 3))
    {X Y : Triple G} (h : GloballyMatched X (reindex p Y)) : GloballyMatched X Y := by
  obtain ⟨e, q, hq⟩ := h
  exact ⟨e, p.symm.trans q, fun i => by simpa [reindex] using hq (p.symm i)⟩

private theorem cyclic_global {G : Type*} [Group G] [IsCyclic G]
    {X Y : Triple G} (h : PointwiseMatched X Y) : GloballyMatched X Y := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨l, p, hp⟩ := h g
  refine ⟨Y 0 / X (p 0), p, fun i => ?_⟩
  apply (MonoidHom.eq_iff_eq_on_generator hg _ _).2
  simp only [MonoidHom.mul_apply, MonoidHom.div_apply]
  rw [hp i, hp 0]
  simp

private theorem coprime_roots {n m : ℕ} (h : n.Coprime m) {z : ℂˣ}
    (hn : z ^ n = 1) (hm : z ^ m = 1) : z = 1 := by
  have hz : z ^ n.gcd m = 1 := (pow_gcd_eq_one).2 ⟨hn, hm⟩
  simpa [h.gcd_eq_one] using hz

private def determinant {G : Type*} [Group G] (X : Triple G) : G →* ℂˣ :=
  ∏ i, X i

private theorem determinant_apply {G : Type*} [Group G] (X : Triple G) (g : G) :
    determinant X g = ∏ i, X i g := by simp [determinant]

private theorem match_determinant {G : Type*} [Group G] {X Y : Triple G}
    {g : G} {l : ℂˣ} {p : Equiv.Perm (Fin 3)}
    (h : ∀ i, Y i g = l * X (p i) g) :
    determinant Y g / determinant X g = l ^ 3 := by
  rw [determinant_apply, determinant_apply]
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  rw [Equiv.prod_comp p (fun i => X i g)]
  simp

private theorem power_of_exponent {G : Type*} [Group G] {n : ℕ}
    (h : ∀ g : G, g ^ n = 1) (f : G →* ℂˣ) (g : G) : f g ^ n = 1 := by
  rw [← map_pow, h, map_one]

private def complexCharacter {G : Type*} [Group G] (f : G →* ℂˣ) : G →* ℂ :=
  (Units.coeHom ℂ).comp f

private theorem complexCharacter_injective {G : Type*} [Group G] :
    Function.Injective (complexCharacter (G := G)) := by
  intro f g h
  apply DFunLike.ext
  intro x
  exact Units.ext (DFunLike.congr_fun h x)

private theorem characters_permutation {G : Type*} [Group G]
    (X Y : Triple G) (hY : Function.Injective Y)
    (h : ∀ g, (∑ i, (X i g : ℂ)) = ∑ i, (Y i g : ℂ)) :
    ∃ p : Equiv.Perm (Fin 3), ∀ i, Y i = X (p i) := by
  classical
  let A : (G →* ℂ) →₀ ℂ := ∑ i, Finsupp.single (complexCharacter (X i)) 1
  let B : (G →* ℂ) →₀ ℂ := ∑ i, Finsupp.single (complexCharacter (Y i)) 1
  have hAB : A = B := (linearIndependent_monoidHom G ℂ) (by
    ext g
    simpa [A, B, map_sum, Finsupp.linearCombination_single, complexCharacter] using h g)
  have hi (i : Fin 3) : ∃ j, Y i = X j := by
    by_contra hn
    push Not at hn
    have hzero : A (complexCharacter (Y i)) = 0 := by
      simp [A,
        fun j => (complexCharacter_injective.ne (hn j)).symm]
    have hone : B (complexCharacter (Y i)) = 1 := by
      have hinj := complexCharacter_injective.comp hY
      have heq (j : Fin 3) : complexCharacter (Y j) = complexCharacter (Y i) ↔ j = i :=
        hinj.eq_iff
      simp only [B, Finsupp.finsetSum_apply, Finsupp.single_apply, heq]
      simp
    rw [hAB, hone] at hzero
    exact one_ne_zero hzero
  choose p hp using hi
  have hp_inj : Function.Injective p := by
    intro i j hij
    apply hY
    rw [hp i, hp j, hij]
  exact ⟨Equiv.ofBijective p ((Finite.injective_iff_bijective).1 hp_inj), hp⟩

private theorem ordinary_permutation {G : Type*} [Group G]
    (X Y : Triple G) (hY : Function.Injective Y)
    (h : ∀ g, ∃ p : Equiv.Perm (Fin 3), ∀ i, Y i g = X (p i) g) :
    ∃ p : Equiv.Perm (Fin 3), ∀ i, Y i = X (p i) := by
  apply characters_permutation X Y hY
  intro g
  obtain ⟨p, hp⟩ := h g
  simp_rw [hp]
  exact (Equiv.sum_comp p (fun i => (X i g : ℂ))).symm

private theorem cyclic_of_faithful_character {G : Type*} [Group G] [Finite G]
    (f : G →* ℂˣ) (hf : ∀ x, f x = 1 → x = 1) : IsCyclic G := by
  let f' : G →* rootsOfUnity (Nat.card G) ℂ := {
    toFun := fun x => ⟨f x, by
      rw [mem_rootsOfUnity]
      rw [← map_pow, pow_card_eq_one', map_one]⟩
    map_one' := Subtype.ext f.map_one
    map_mul' := fun x y => Subtype.ext (f.map_mul x y) }
  apply isCyclic_of_injective f'
  apply (injective_iff_map_eq_one f').2
  intro x hx
  exact hf x (congrArg Subtype.val hx)

private theorem faithful_characters_injective {G : Type*} [Group G] [Finite G]
    (hn : ¬ IsCyclic G) {X : Triple G} (hf : ProjectivelyFaithful X) :
    Function.Injective X := by
  have h01 : X 0 ≠ X 1 := by
    intro he
    apply hn
    apply cyclic_of_faithful_character (X 2 / X 0)
    intro g hg
    apply hf g
    intro i
    have hg' : X 2 g = X 0 g := div_eq_one.mp hg
    fin_cases i
    · rfl
    · exact DFunLike.congr_fun he.symm g
    · exact hg'
  have h02 : X 0 ≠ X 2 := by
    intro he
    apply hn
    apply cyclic_of_faithful_character (X 1 / X 0)
    intro g hg
    apply hf g
    intro i
    have hg' : X 1 g = X 0 g := div_eq_one.mp hg
    fin_cases i
    · rfl
    · exact hg'
    · exact DFunLike.congr_fun he.symm g
  have h12 : X 1 ≠ X 2 := by
    intro he
    apply hn
    apply cyclic_of_faithful_character (X 1 / X 0)
    intro g hg
    apply hf g
    intro i
    have hg' : X 1 g = X 0 g := div_eq_one.mp hg
    fin_cases i
    · rfl
    · exact hg'
    · exact (DFunLike.congr_fun he.symm g).trans hg'
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private def leftTriple {P O : Type*} [Group P] [Group O]
    (X : Triple (P × O)) : Triple P := fun i => (X i).comp (MonoidHom.inl P O)

private theorem faithful_left {P O : Type*} [Group P] [Group O]
    {X : Triple (P × O)} (h : ProjectivelyFaithful X) :
    ProjectivelyFaithful (leftTriple X) := by
  intro p hp
  exact congrArg Prod.fst (h (p, 1) hp)

private theorem split_apply {P O : Type*} [Group P] [Group O]
    (f : P × O →* ℂˣ) (p : P) (o : O) :
    f (p, o) = f (p, 1) * f (1, o) := by
  rw [← map_mul]
  simp

private theorem normalize_left {P O : Type*} [Group P] [Group O] [Finite P]
    {n : ℕ} (hn : 1 < n) (hn3 : Nat.Coprime 3 n)
    (hexp : ∀ p : P, p ^ n = 1) (hnc : ¬ IsCyclic P)
    {X Y : Triple (P × O)} (hY : ProjectivelyFaithful Y)
    (h : PointwiseMatched X Y) :
    ∃ e : P × O →* ℂˣ, ∃ p : Equiv.Perm (Fin 3),
      ∀ i, (twist e (reindex p Y) i).comp (MonoidHom.inl P O) =
        (X i).comp (MonoidHom.inl P O) := by
  obtain ⟨q, _, hq⟩ := Nat.exists_mul_mod_eq_one_of_coprime hn3 hn
  let D : P →* ℂˣ := (determinant Y / determinant X).comp (MonoidHom.inl P O)
  let e : P × O →* ℂˣ := (D ^ q).comp (MonoidHom.fst P O)
  let Y' := twist e⁻¹ Y
  have hpoint (p : P) : ∃ t : Equiv.Perm (Fin 3),
      ∀ i, Y' i (p, 1) = X (t i) (p, 1) := by
    obtain ⟨l, t, ht⟩ := h (p, 1)
    have hp : (p, (1 : O)) ^ n = 1 := by simp [hexp]
    have hl : l ^ n = 1 := by
      have hi := ht 0
      have hi' := congrArg (fun z : ℂˣ => z ^ n) hi
      simp only [mul_pow, ← map_pow, hp, map_one, mul_one] at hi'
      exact hi'.symm
    have hd : D p = l ^ 3 := match_determinant ht
    have he : e (p, 1) = l := by
      change D p ^ q = l
      rw [hd, ← pow_mul]
      have hqe : 3 * q ≡ 1 [MOD n] := by simpa [Nat.ModEq, Nat.mod_eq_of_lt hn] using hq
      simpa using pow_eq_pow_of_modEq hqe hl
    refine ⟨t, fun i => ?_⟩
    simp [Y', twist, ht i, he]
  have hY' : Function.Injective (leftTriple Y') := by
    apply faithful_characters_injective hnc
    apply faithful_left
    exact (faithful_twist e⁻¹ Y).2 hY
  obtain ⟨t, ht⟩ := ordinary_permutation (leftTriple X) (leftTriple Y') hY' hpoint
  refine ⟨e⁻¹, t.symm, fun i => ?_⟩
  simpa [leftTriple, Y', twist, reindex] using ht (t.symm i)

private theorem mixed_match_primary {P O : Type*} [Group P] [Group O]
    {n m : ℕ} (hn3 : n.Coprime 3) (hnm : n.Coprime m)
    (hP : ∀ p : P, p ^ n = 1) (hO : ∀ o : O, o ^ m = 1)
    {X Y : Triple (P × O)} (heq : ∀ i p, Y i (p, 1) = X i (p, 1))
    {p : P} {o : O} {l : ℂˣ} {t : Equiv.Perm (Fin 3)}
    (ht : ∀ i, Y i (p, o) = l * X (t i) (p, o)) :
    l ^ m = 1 ∧ ∀ i, X i (p, 1) = X (t i) (p, 1) := by
  have hpair : (p, o) ^ (n * m) = 1 := by
    apply Prod.ext
    · change p ^ (n * m) = 1
      rw [pow_mul, hP, one_pow]
    · change o ^ (n * m) = 1
      rw [Nat.mul_comm n m, pow_mul, hO, one_pow]
  have hl : l ^ (n * m) = 1 := by
    have hi := congrArg (fun z : ℂˣ => z ^ (n * m)) (ht 0)
    simpa only [mul_pow, ← map_pow, hpair, map_one, mul_one] using hi.symm
  let D : P × O →* ℂˣ := determinant Y / determinant X
  have hDP : D (p, 1) = 1 := by
    change determinant Y (p, 1) / determinant X (p, 1) = 1
    rw [div_eq_one, determinant_apply, determinant_apply]
    exact Finset.prod_congr rfl (fun i _ => heq i p)
  have hDO : D (1, o) ^ m = 1 := by
    rw [← map_pow]
    have ho : ((1 : P), o) ^ m = 1 := by ext <;> simp [hO]
    rw [ho, map_one]
  have hDm : D (p, o) ^ m = 1 := by
    rw [split_apply D p o, hDP, one_mul]
    exact hDO
  have hlm : l ^ m = 1 := by
    apply coprime_roots hn3
    · rw [← pow_mul, Nat.mul_comm m n]
      exact hl
    · rw [← pow_mul, Nat.mul_comm m 3, pow_mul]
      rw [← match_determinant ht]
      exact hDm
  refine ⟨hlm, fun i => ?_⟩
  have hOm (f : P × O →* ℂˣ) : f (1, o) ^ m = 1 := by
    rw [← map_pow]
    have ho : ((1 : P), o) ^ m = 1 := by ext <;> simp [hO]
    rw [ho, map_one]
  have hPm (f : P × O →* ℂˣ) : f (p, 1) ^ n = 1 := by
    rw [← map_pow]
    have hp : (p, (1 : O)) ^ n = 1 := by ext <;> simp [hP]
    rw [hp, map_one]
  have hi := congrArg (fun z : ℂˣ => z ^ m) (ht i)
  rw [split_apply (Y i) p o, split_apply (X (t i)) p o] at hi
  simp only [mul_pow, hOm, hlm, mul_one, one_mul, heq] at hi
  apply div_eq_one.mp
  apply coprime_roots hnm
  · simp only [div_pow, hPm, div_self']
  · rw [div_pow, hi, div_self']

private theorem aligned_regular_global {P O : Type*} [Group P] [Group O]
    {n m : ℕ} (hn3 : n.Coprime 3) (hnm : n.Coprime m)
    (hP : ∀ p : P, p ^ n = 1) (hO : ∀ o : O, o ^ m = 1)
    {X Y : Triple (P × O)} (heq : ∀ i p, Y i (p, 1) = X i (p, 1))
    (h : PointwiseMatched X Y) (p₀ : P)
    (hr : Function.Injective (fun i => X i (p₀, 1))) : GloballyMatched X Y := by
  have hright (o : O) : ∀ i,
      Y i (1, o) = (Y 0 (1, o) / X 0 (1, o)) * X i (1, o) := by
    obtain ⟨l, t, ht⟩ := h (p₀, o)
    have hc := (mixed_match_primary hn3 hnm hP hO heq ht).2
    have hfix (i : Fin 3) : t i = i := (hr (hc i)).symm
    have ho (i : Fin 3) : Y i (1, o) = l * X i (1, o) := by
      have hi := ht i
      rw [hfix i, split_apply (Y i) p₀ o, split_apply (X i) p₀ o, heq] at hi
      apply mul_left_cancel (a := X i (p₀, 1))
      simpa only [mul_assoc, mul_left_comm] using hi
    intro i
    rw [ho i, ho 0]
    simp
  refine ⟨((Y 0 / X 0).comp (MonoidHom.inr P O)).comp (MonoidHom.snd P O),
    Equiv.refl _, fun i => ?_⟩
  apply DFunLike.ext
  rintro ⟨p, o⟩
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.coe_snd,
    MonoidHom.inr_apply, MonoidHom.div_apply, Equiv.refl_apply]
  rw [split_apply (Y i) p o, split_apply (X i) p o, heq, hright o i]
  ac_rfl

private theorem three_powers_avoid {H : Type*} [Group H] (x a b c : H)
    (hx : x ^ 2 ≠ 1) : ∃ j : Fin 3, x ^ j.val * a ≠ b ∧ x ^ j.val * a ≠ c := by
  have hx1 : x ≠ 1 := by rintro rfl; simp at hx
  have hx2 : x ≠ x ^ 2 := by
    intro h
    apply hx1
    apply mul_left_cancel (a := x)
    simpa [pow_two] using h.symm
  have h01 : a ≠ x * a := by
    intro h
    apply hx1
    simpa using h
  have h02 : a ≠ x ^ 2 * a := by
    intro h
    apply hx
    simpa using h
  have h12 : x * a ≠ x ^ 2 * a := fun h => hx2 (mul_right_cancel h)
  by_contra! h
  have h0 : a = b ∨ a = c := by
    have hh : a ≠ b → a = c := by simpa using h 0
    tauto
  have h1 : x * a = b ∨ x * a = c := by
    have hh : x * a ≠ b → x * a = c := by simpa using h 1
    tauto
  have h2 : x ^ 2 * a = b ∨ x ^ 2 * a = c := by
    have hh : x ^ 2 * a ≠ b → x ^ 2 * a = c := h 2
    tauto
  aesop

private theorem regular_of_nonsquare {G : Type*} [Group G]
    (a b : G →* ℂˣ) (hb : b ≠ 1) (hab : a ≠ b)
    (g : G) (hg : a g ^ 2 ≠ 1) :
    ∃ p, a p ≠ 1 ∧ b p ≠ 1 ∧ a p ≠ b p := by
  have hag : a g ≠ 1 := by intro h; simp [h] at hg
  by_cases hbg : b g = 1
  · obtain ⟨k, hk⟩ : ∃ k, b k ≠ 1 := by
      by_contra! h
      apply hb
      apply DFunLike.ext
      intro x
      exact h x
    obtain ⟨j, hj1, hj2⟩ := three_powers_avoid (a g) (a k) 1 (b k) hg
    refine ⟨g ^ j.val * k, ?_, ?_, ?_⟩
    · simpa only [map_mul, map_pow] using hj1
    · simpa [hbg] using hk
    · simpa [hbg] using hj2
  by_cases he : a g = b g
  · obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra! h
      exact hab (DFunLike.ext _ _ h)
    obtain ⟨j, hj1, hj2⟩ := three_powers_avoid (a g) (b k) 1 (b k / a k) hg
    refine ⟨g ^ j.val * k, ?_, ?_, ?_⟩
    · intro hh
      apply hj2
      simp only [map_mul, map_pow] at hh
      calc
        a g ^ j.val * b k = (a g ^ j.val * a k) * (b k / a k) := by
          simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
        _ = b k / a k := by rw [hh, one_mul]
    · simpa [← he] using hj1
    · intro hh
      apply hk
      simpa only [map_mul, map_pow, ← he, mul_left_cancel_iff] using hh
  exact ⟨g, hag, hbg, he⟩

private theorem faithful_regular {G : Type*} [Group G] [Finite G]
    (hn : ¬ IsCyclic G) {X : Triple G} (hX : ProjectivelyFaithful X)
    (g : G) (hg : g ^ 2 ≠ 1) : ∃ p, Function.Injective (fun i => X i p) := by
  have hi := faithful_characters_injective hn hX
  let a : G →* ℂˣ := X 1 / X 0
  let b : G →* ℂˣ := X 2 / X 0
  have ha : a ≠ 1 := by
    intro h
    have : X 1 = X 0 := div_eq_one.mp h
    have := hi this
    norm_num at this
  have hb : b ≠ 1 := by
    intro h
    have : X 2 = X 0 := div_eq_one.mp h
    have := hi this
    norm_num at this
  have hab : a ≠ b := by
    intro h
    have : X 1 = X 2 := div_left_inj.mp h
    have := hi this
    norm_num at this
  have hsq : a g ^ 2 ≠ 1 ∨ b g ^ 2 ≠ 1 := by
    by_contra! h
    apply hg
    apply hX (g ^ 2)
    intro i
    have h1 : X 1 (g ^ 2) = X 0 (g ^ 2) := by
      apply div_eq_one.mp
      simpa [a, div_pow, map_pow] using h.1
    have h2 : X 2 (g ^ 2) = X 0 (g ^ 2) := by
      apply div_eq_one.mp
      simpa [b, div_pow, map_pow] using h.2
    fin_cases i
    · rfl
    · exact h1
    · exact h2
  have hr : ∃ p, a p ≠ 1 ∧ b p ≠ 1 ∧ a p ≠ b p := by
    rcases hsq with h | h
    · exact regular_of_nonsquare a b hb hab g h
    · obtain ⟨p, hp, hq, hr⟩ := regular_of_nonsquare b a ha hab.symm g h
      exact ⟨p, hq, hp, hr.symm⟩
  obtain ⟨p, hp, hq, hr⟩ := hr
  refine ⟨p, fun i j hij => ?_⟩
  have hp' : X 1 p ≠ X 0 p := by simpa [a, div_eq_one] using hp
  have hq' : X 2 p ≠ X 0 p := by simpa [b, div_eq_one] using hq
  have hr' : X 1 p ≠ X 2 p := by simpa [a, b, div_left_inj] using hr
  fin_cases i <;> fin_cases j <;> simp_all

private theorem pointwise_reindex {G : Type*} [Group G] (p : Equiv.Perm (Fin 3))
    {X Y : Triple G} (h : PointwiseMatched X Y) :
    PointwiseMatched X (reindex p Y) := by
  intro g
  obtain ⟨l, t, ht⟩ := h g
  exact ⟨l, p.trans t, fun i => ht (p i)⟩

private theorem supports_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Supports H) : Supports G := by
  obtain ⟨X, Y, hX, hY, hXY, hnot⟩ := h
  let X' : Triple G := fun i => (X i).comp e.toMonoidHom
  let Y' : Triple G := fun i => (Y i).comp e.toMonoidHom
  refine ⟨X', Y', ?_, ?_, ?_, ?_⟩
  · intro g hg
    apply e.injective
    rw [e.map_one]
    exact hX (e g) hg
  · intro g hg
    apply e.injective
    rw [e.map_one]
    exact hY (e g) hg
  · intro g
    exact hXY (e g)
  · rintro ⟨d, p, hp⟩
    apply hnot
    refine ⟨d.comp e.symm.toMonoidHom, p, fun i => ?_⟩
    apply DFunLike.ext
    intro g
    simpa [X', Y', MonoidHom.comp_apply] using DFunLike.congr_fun (hp i) (e.symm g)

private theorem cyclic_exponent (n : ℕ) (x : Cyclic n) : x ^ n = 1 := by
  change n • x.toAdd = 0
  simp [nsmul_eq_mul]

private theorem primary_noncyclic {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬ IsCyclic (Cyclic (2 ^ a) × Cyclic (2 ^ b)) := by
  intro hc
  let := hc
  have h := coprime_card_of_isCyclic_prod (Cyclic (2 ^ a)) (Cyclic (2 ^ b))
  rw [cyclic_card, cyclic_card] at h
  have htwo : 2 ∣ (2 ^ a).gcd (2 ^ b) := Nat.dvd_gcd
    (dvd_pow_self 2 (by omega)) (dvd_pow_self 2 (by omega))
  rw [h.gcd_eq_one] at htwo
  norm_num at htwo

private theorem primary_exponent {a b : ℕ} (hab : a ≤ b)
    (x : Cyclic (2 ^ a) × Cyclic (2 ^ b)) : x ^ (2 ^ b) = 1 := by
  apply Prod.ext
  · change x.1 ^ (2 ^ b) = 1
    obtain ⟨k, hk⟩ := pow_dvd_pow 2 hab
    calc
      x.1 ^ (2 ^ b) = x.1 ^ (2 ^ a * k) := congrArg (fun n => x.1 ^ n) hk
      _ = 1 := by rw [pow_mul, cyclic_exponent, one_pow]
  · exact cyclic_exponent _ x.2

private theorem primary_nonsquare {a b : ℕ} (hb : 2 ≤ b) :
    ∃ x : Cyclic (2 ^ a) × Cyclic (2 ^ b), x ^ 2 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Cyclic (2 ^ b))
  refine ⟨(1, g), fun h => ?_⟩
  have hg' : g ^ 2 = 1 := congrArg Prod.snd h
  have hd : 2 ^ b ∣ 2 := by
    have hd := orderOf_dvd_of_pow_eq_one hg'
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, cyclic_card] at hd
  have hpow : 4 ≤ 2 ^ b := by simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hb
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

private theorem no_support_higher {a b m : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : 2 ≤ b) (hm : Odd m) :
    ¬ Supports ((Cyclic (2 ^ a) × Cyclic (2 ^ b)) × Cyclic m) := by
  rintro ⟨X, Y, hX, hY, h, hnot⟩
  have hn3 : (2 ^ b).Coprime 3 := (by decide : Nat.Coprime 2 3).pow_left b
  have hnm : (2 ^ b).Coprime m := (Nat.coprime_two_left.mpr hm).pow_left b
  have hnc := primary_noncyclic ha (by omega : 1 ≤ b)
  have hn : 1 < 2 ^ b := one_lt_pow₀ (by norm_num) (by omega)
  obtain ⟨e, t, ht⟩ := normalize_left hn hn3.symm (primary_exponent hab) hnc hY h
  let Y' := twist e (reindex t Y)
  have heq (i : Fin 3) (p : Cyclic (2 ^ a) × Cyclic (2 ^ b)) :
      Y' i (p, 1) = X i (p, 1) := DFunLike.congr_fun (ht i) p
  have hpoint : PointwiseMatched X Y' := by
    simpa [Y'] using pointwise_twist 1 e (pointwise_reindex t h)
  obtain ⟨g, hg⟩ := primary_nonsquare (a := a) hb
  obtain ⟨p, hp⟩ := faithful_regular hnc (faithful_left hX) g hg
  have hmexp := cyclic_exponent m
  have hglobal := aligned_regular_global hn3 hnm (primary_exponent hab) hmexp heq hpoint p hp
  have hg' : GloballyMatched X (reindex t Y) := by
    apply (global_twist 1 e X (reindex t Y)).1
    simpa [Y'] using hglobal
  exact hnot (global_reindex t hg')

private theorem faithful_square_surjective {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P = 4) (hexp : ∀ p : P, p ^ 2 = 1)
    {X : Triple P} (hf : ProjectivelyFaithful X) (s t : ℂˣ)
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) :
    ∃ p, X 1 p / X 0 p = s ∧ X 2 p / X 0 p = t := by
  let a : P →* rootsOfUnity 2 ℂ := (X 1 / X 0).codRestrict _ (fun p =>
    power_of_exponent hexp (X 1 / X 0) p)
  let b : P →* rootsOfUnity 2 ℂ := (X 2 / X 0).codRestrict _ (fun p =>
    power_of_exponent hexp (X 2 / X 0) p)
  let R := a.prod b
  have hinj : Function.Injective R := by
    apply (injective_iff_map_eq_one R).2
    intro p hp
    apply hf p
    have h1 : X 1 p / X 0 p = 1 := congrArg (fun z => (z.1 : ℂˣ)) hp
    have h2 : X 2 p / X 0 p = 1 := congrArg (fun z => (z.2 : ℂˣ)) hp
    intro i
    fin_cases i
    · rfl
    · exact div_eq_one.mp h1
    · exact div_eq_one.mp h2
  have hcard' : Nat.card (rootsOfUnity 2 ℂ × rootsOfUnity 2 ℂ) = 4 := by
    rw [Nat.card_prod, Complex.card_rootsOfUnity]
  have hsurj := ((Nat.bijective_iff_injective_and_card R).2
    ⟨hinj, hcard.trans hcard'.symm⟩).2
  obtain ⟨p, hp⟩ := hsurj (⟨s, hs⟩, ⟨t, ht⟩)
  exact ⟨p, congrArg (fun z => (z.1 : ℂˣ)) hp, congrArg (fun z => (z.2 : ℂˣ)) hp⟩

private theorem singleton_point {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P = 4) (hexp : ∀ p : P, p ^ 2 = 1)
    {X : Triple P} (hf : ProjectivelyFaithful X) (j : Fin 3) :
    ∃ p, (∀ i, i ≠ j → X i p ≠ X j p) ∧
      ∀ i k, i ≠ j → k ≠ j → X i p = X k p := by
  have hneg : (-1 : ℂˣ) ^ 2 = 1 := by ext; norm_num
  have hne : (-1 : ℂˣ) ≠ 1 := by intro h; have hh := congrArg Units.val h; norm_num at hh
  have hdiff (u v : ℂˣ) (h : u / v = -1) : u ≠ v := by
    intro he
    rw [he, div_self'] at h
    exact hne h.symm
  fin_cases j
  · obtain ⟨p, h1, h2⟩ := faithful_square_surjective hcard hexp hf (-1) (-1) hneg hneg
    have he : X 1 p = X 2 p := div_left_inj.mp (h1.trans h2.symm)
    have hn1 := hdiff _ _ h1
    have hn2 := hdiff _ _ h2
    refine ⟨p, ?_, ?_⟩
    · intro i hi
      fin_cases i <;> simp_all
    · intro i k hi hk
      fin_cases i <;> fin_cases k <;> simp_all
  · obtain ⟨p, h1, h2⟩ := faithful_square_surjective hcard hexp hf (-1) 1 hneg (by simp)
    have he : X 2 p = X 0 p := div_eq_one.mp h2
    have hn1 := hdiff _ _ h1
    refine ⟨p, ?_, ?_⟩
    · intro i hi
      fin_cases i
      · exact hn1.symm
      · exact False.elim (hi rfl)
      · simpa [he] using hn1.symm
    · intro i k hi hk
      fin_cases i <;> fin_cases k <;> simp_all
  · obtain ⟨p, h1, h2⟩ := faithful_square_surjective hcard hexp hf 1 (-1) (by simp) hneg
    have he : X 1 p = X 0 p := div_eq_one.mp h1
    have hn2 := hdiff _ _ h2
    refine ⟨p, ?_, ?_⟩
    · intro i hi
      fin_cases i
      · exact hn2.symm
      · simpa [he] using hn2.symm
      · exact False.elim (hi rfl)
    · intro i k hi hk
      fin_cases i <;> fin_cases k <;> simp_all

private theorem global_of_generator_values {P O : Type*} [Group P] [Group O]
    {X Y : Triple (P × O)} (heq : ∀ i p, Y i (p, 1) = X i (p, 1))
    (g : O) (hg : ∀ o, o ∈ Subgroup.zpowers g)
    (h : ∃ l : ℂˣ, ∀ i, Y i (1, g) = l * X i (1, g)) : GloballyMatched X Y := by
  obtain ⟨l, hl⟩ := h
  let d : O →* ℂˣ := (Y 0 / X 0).comp (MonoidHom.inr P O)
  have hd : d g = l := by simp [d, hl 0]
  have hright (i : Fin 3) : (Y i).comp (MonoidHom.inr P O) =
      d * (X i).comp (MonoidHom.inr P O) := by
    apply (MonoidHom.eq_iff_eq_on_generator hg _ _).2
    simpa [hd] using hl i
  refine ⟨d.comp (MonoidHom.snd P O), Equiv.refl _, fun i => ?_⟩
  apply DFunLike.ext
  rintro ⟨p, o⟩
  have ho := DFunLike.congr_fun (hright i) o
  change Y i (1, o) = d o * X i (1, o) at ho
  change Y i (p, o) = d o * X i (p, o)
  rw [split_apply (Y i) p o, split_apply (X i) p o, heq, ho]
  ac_rfl

private def complementarySwap (j : Fin 3) : Equiv.Perm (Fin 3) :=
  if j = 0 then Equiv.swap 1 2 else if j = 1 then Equiv.swap 0 2 else Equiv.swap 0 1

private theorem fixed_permutation_three (j : Fin 3) (p : Equiv.Perm (Fin 3))
    (h : p j = j) : p = Equiv.refl _ ∨ p = complementarySwap j := by
  have key : ∀ (j : Fin 3) (p : Equiv.Perm (Fin 3)), p j = j →
      p = Equiv.refl _ ∨ p = complementarySwap j := by decide
  exact key j p h

private theorem singleton_generator_match {P O : Type*} [Group P] [Group O] [Finite P]
    {m : ℕ} (hm : Odd m) (hcard : Nat.card P = 4) (hP : ∀ p : P, p ^ 2 = 1)
    (hO : ∀ o : O, o ^ m = 1) {X Y : Triple (P × O)}
    (hX : ProjectivelyFaithful X) (heq : ∀ i p, Y i (p, 1) = X i (p, 1))
    (h : PointwiseMatched X Y) (hnot : ¬ GloballyMatched X Y)
    (g : O) (hg : ∀ o, o ∈ Subgroup.zpowers g) (j : Fin 3) :
    ∃ l : ℂˣ, ∀ i, Y i (1, g) = l * X (complementarySwap j i) (1, g) := by
  obtain ⟨p, hs, _⟩ := singleton_point hcard hP (faithful_left hX) j
  obtain ⟨l, t, ht⟩ := h (p, g)
  have hc := (mixed_match_primary (by decide : Nat.Coprime 2 3)
    (Nat.coprime_two_left.mpr hm) hP hO heq ht).2
  have hfix : t j = j := by
    by_contra hn
    exact hs (t j) hn (hc j).symm
  have ho (i : Fin 3) : Y i (1, g) = l * X (t i) (1, g) := by
    have hi := ht i
    rw [split_apply (Y i) p g, split_apply (X (t i)) p g, heq, hc i] at hi
    apply mul_left_cancel (a := X (t i) (p, 1))
    simpa only [mul_assoc, mul_left_comm] using hi
  rcases fixed_permutation_three j t hfix with hti | hts
  · apply False.elim
    apply hnot
    apply global_of_generator_values heq g hg
    exact ⟨l, fun i => by simpa [hti] using ho i⟩
  · exact ⟨l, fun i => by simpa [hts] using ho i⟩

private theorem two_swaps_cube (d e : Fin 3 → ℂˣ) (hd : d 0 = 1) (he : e 0 = 1)
    (h₀ : ∃ l : ℂˣ, ∀ i, e i = l * d (complementarySwap 0 i))
    (h₁ : ∃ l : ℂˣ, ∀ i, e i = l * d (complementarySwap 1 i)) :
    d 1 ^ 3 = 1 ∧ d 2 ^ 3 = 1 := by
  obtain ⟨l, hl⟩ := h₀
  obtain ⟨k, hk⟩ := h₁
  have hl0 : l = 1 := by simpa [complementarySwap, Equiv.swap_apply_def, hd, he] using (hl 0).symm
  have hl1 : e 1 = d 2 := by simpa [complementarySwap, Equiv.swap_apply_def, hl0] using hl 1
  have hl2 : e 2 = d 1 := by simpa [complementarySwap, Equiv.swap_apply_def, hl0] using hl 2
  have hk0 : k * d 2 = 1 := by simpa [complementarySwap, Equiv.swap_apply_def, he] using (hk 0).symm
  have hk1 : d 2 = k * d 1 := by simpa [complementarySwap, Equiv.swap_apply_def, hl1] using hk 1
  have hk2 : d 1 = k := by simpa [complementarySwap, Equiv.swap_apply_def, hd, hl2] using hk 2
  have hprod : d 1 * d 2 = 1 := by simpa [hk2] using hk0
  have hsq : d 2 = d 1 ^ 2 := by simpa [← hk2, pow_two] using hk1
  have hc : d 1 ^ 3 = 1 := by
    rw [hsq, ← pow_succ'] at hprod
    exact hprod
  refine ⟨hc, ?_⟩
  rw [hsq, ← pow_mul, Nat.mul_comm 2 3, pow_mul, hc, one_pow]

private theorem aligned_odd_order {P : Type*} [Group P] [Finite P]
    {m : ℕ} [NeZero m] (hm : Odd m) (hcard : Nat.card P = 4)
    (hP : ∀ p : P, p ^ 2 = 1) {X Y : Triple (P × Cyclic m)}
    (hX : ProjectivelyFaithful X) (heq : ∀ i p, Y i (p, 1) = X i (p, 1))
    (hX0 : ∀ o, X 0 (1, o) = 1) (hY0 : ∀ o, Y 0 (1, o) = 1)
    (h : PointwiseMatched X Y) (hnot : ¬ GloballyMatched X Y) : m = 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Cyclic m)
  have horder : orderOf g = m := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, cyclic_card]
  have hs := singleton_generator_match hm hcard hP (cyclic_exponent m) hX heq h hnot g hg
  have hc := two_swaps_cube (fun i => X i (1, g)) (fun i => Y i (1, g))
    (hX0 g) (hY0 g) (hs 0) (hs 1)
  have hg3 : g ^ 3 = 1 := by
    have he : ((1 : P), g ^ 3) = 1 := by
      apply hX
      intro i
      have h0 : X 0 (1, g ^ 3) = 1 := hX0 _
      rw [h0]
      have hpow (f : P × Cyclic m →* ℂˣ) : f (1, g ^ 3) = f (1, g) ^ 3 := by
        rw [← map_pow]
        congr 1
        ext <;> simp
      rw [hpow]
      fin_cases i
      · simp [hX0]
      · exact hc.1
      · exact hc.2
    exact congrArg Prod.snd he
  have hd : m ∣ 3 := by rw [← horder]; exact orderOf_dvd_of_pow_eq_one hg3
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with hm1 | hm3
  · have hg1 : g = 1 := orderOf_eq_one_iff.mp (horder.trans hm1)
    apply False.elim
    apply hnot
    apply global_of_generator_values heq g hg
    refine ⟨1, fun i => ?_⟩
    subst g
    change Y i 1 = 1 * X i 1
    simp
  · exact hm3

private def oddFirstTwist {P O : Type*} [Group P] [Group O]
    (X : Triple (P × O)) : P × O →* ℂˣ :=
  (((X 0).comp (MonoidHom.inr P O))⁻¹).comp (MonoidHom.snd P O)

private theorem oddFirstTwist_left {P O : Type*} [Group P] [Group O]
    (X : Triple (P × O)) (p : P) : oddFirstTwist X (p, 1) = 1 := by
  change (((X 0).comp (MonoidHom.inr P O))⁻¹) 1 = 1
  exact map_one _

private theorem oddFirstTwist_zero {P O : Type*} [Group P] [Group O]
    (X : Triple (P × O)) (o : O) : twist (oddFirstTwist X) X 0 (1, o) = 1 := by
  change (X 0 (1, o))⁻¹ * X 0 (1, o) = 1
  exact inv_mul_cancel _

private theorem support_small_odd {m : ℕ} [NeZero m] (hm : Odd m)
    (hs : Supports ((Cyclic 2 × Cyclic 2) × Cyclic m)) : m = 3 := by
  obtain ⟨X, Y, hX, hY, h, hnot⟩ := hs
  have hnc := primary_noncyclic (a := 1) (b := 1) (by omega) (by omega)
  have hP : ∀ p : Cyclic 2 × Cyclic 2, p ^ 2 = 1 := by
    intro p
    exact Prod.ext (cyclic_exponent 2 p.1) (cyclic_exponent 2 p.2)
  obtain ⟨e, t, ht⟩ := normalize_left (by decide : 1 < 2) (by decide : Nat.Coprime 3 2)
    hP hnc hY h
  let Y' := twist e (reindex t Y)
  have heq (i : Fin 3) (p : Cyclic 2 × Cyclic 2) : Y' i (p, 1) = X i (p, 1) :=
    DFunLike.congr_fun (ht i) p
  have hpoint : PointwiseMatched X Y' := by
    simpa [Y'] using pointwise_twist 1 e (pointwise_reindex t h)
  have hnot' : ¬ GloballyMatched X Y' := by
    intro hg
    have hg' : GloballyMatched X (reindex t Y) := by
      apply (global_twist 1 e X (reindex t Y)).1
      simpa [Y'] using hg
    exact hnot (global_reindex t hg')
  let f := oddFirstTwist X
  let k := oddFirstTwist Y'
  let U := twist f X
  let V := twist k Y'
  have hUV : PointwiseMatched U V := pointwise_twist f k hpoint
  have hnUV : ¬ GloballyMatched U V := fun hg => hnot' ((global_twist f k X Y').1 hg)
  have heqUV (i : Fin 3) (p : Cyclic 2 × Cyclic 2) : V i (p, 1) = U i (p, 1) := by
    simp only [V, U, twist, MonoidHom.mul_apply, f, k, oddFirstTwist_left, one_mul, heq]
  apply aligned_odd_order hm (by norm_num only [Nat.card_prod, cyclic_card]) hP
    ((faithful_twist f X).2 hX) heqUV
    (oddFirstTwist_zero X) (oddFirstTwist_zero Y') hUV hnUV

private noncomputable def primaryDecomposition (a b m : ℕ) (hm : Odd m) :
    Source a b m ≃* (Cyclic (2 ^ a) × Cyclic (2 ^ b)) × Cyclic m := by
  have hc : (2 ^ b).Coprime m := (Nat.coprime_two_left.mpr hm).pow_left b
  let c := (AddEquiv.toMultiplicative (ZMod.chineseRemainder hc).toAddEquiv).trans
    (MulEquiv.prodMultiplicative _ _)
  exact (MulEquiv.prodCongr (MulEquiv.refl (Cyclic (2 ^ a))) c).trans
    MulEquiv.prodAssoc.symm

private theorem faithful_of_pointwise {G : Type*} [Group G] {X Y : Triple G}
    (hX : ProjectivelyFaithful X) (h : PointwiseMatched X Y) : ProjectivelyFaithful Y := by
  intro g hg
  obtain ⟨l, p, hp⟩ := h g
  apply hX g
  intro i
  apply mul_left_cancel (a := l)
  have hi := (hg (p.symm i)).trans (hg (p.symm 0)).symm
  simpa [hp] using hi

private abbrev WitnessGroup := (rootsOfUnity 2 ℂ × rootsOfUnity 2 ℂ) × rootsOfUnity 3 ℂ

private def firstSign : WitnessGroup →* ℂˣ where
  toFun x := x.1.1.val
  map_one' := rfl
  map_mul' _ _ := rfl

private def secondSign : WitnessGroup →* ℂˣ where
  toFun x := x.1.2.val
  map_one' := rfl
  map_mul' _ _ := rfl

private def thirdRoot : WitnessGroup →* ℂˣ where
  toFun x := x.2.val
  map_one' := rfl
  map_mul' _ _ := rfl

private def witnessX : Triple WitnessGroup :=
  ![1, firstSign * thirdRoot, secondSign * thirdRoot⁻¹]

private def witnessY : Triple WitnessGroup :=
  ![1, firstSign * thirdRoot⁻¹, secondSign * thirdRoot]

private theorem witness_faithful : ProjectivelyFaithful witnessX := by
  intro x hx
  have h1 : firstSign x * thirdRoot x = 1 := by simpa [witnessX] using hx 1
  have h2 : secondSign x * (thirdRoot x)⁻¹ = 1 := by simpa [witnessX] using hx 2
  have hs : firstSign x ^ 2 = 1 := x.1.1.property
  have hz3 : thirdRoot x ^ 3 = 1 := x.2.property
  have hz2 : thirdRoot x ^ 2 = 1 := by
    have hh := congrArg (fun z : ℂˣ => z ^ 2) h1
    simpa only [mul_pow, hs, one_mul, one_pow] using hh
  have hz := coprime_roots (by decide : Nat.Coprime 2 3) hz2 hz3
  have hs1 : firstSign x = 1 := by simpa [hz] using h1
  have ht1 : secondSign x = 1 := by simpa [hz] using h2
  exact Prod.ext (Prod.ext (Subtype.ext hs1) (Subtype.ext ht1)) (Subtype.ext hz)

private theorem unit_square_cases (s : ℂˣ) (hs : s ^ 2 = 1) : s = 1 ∨ s = -1 := by
  have hh : (s : ℂ) ^ 2 = 1 := congrArg Units.val hs
  rcases sq_eq_one_iff.mp hh with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

private theorem witness_pointwise : PointwiseMatched witnessX witnessY := by
  intro x
  have hs : firstSign x ^ 2 = 1 := x.1.1.property
  have ht : secondSign x ^ 2 = 1 := x.1.2.property
  have hz : thirdRoot x ^ 3 = 1 := x.2.property
  have hz2 : thirdRoot x ^ 2 = (thirdRoot x)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    simpa [pow_succ] using hz
  have hzi2 : ((thirdRoot x)⁻¹) ^ 2 = thirdRoot x := by
    apply inv_injective
    simpa only [inv_pow, inv_inv] using hz2
  by_cases he : firstSign x = secondSign x
  · refine ⟨1, Equiv.swap 1 2, fun i => ?_⟩
    fin_cases i <;> simp [witnessX, witnessY, Equiv.swap_apply_def, he]
  rcases unit_square_cases (firstSign x) hs with hs1 | hs1 <;>
    rcases unit_square_cases (secondSign x) ht with ht1 | ht1
  · exact False.elim (he (hs1.trans ht1.symm))
  · refine ⟨(thirdRoot x)⁻¹, Equiv.swap 0 1, fun i => ?_⟩
    fin_cases i <;> simp [witnessX, witnessY, Equiv.swap_apply_def, hs1, ht1,
      ← pow_two, hzi2]
  · refine ⟨thirdRoot x, Equiv.swap 0 2, fun i => ?_⟩
    fin_cases i <;> simp [witnessX, witnessY, Equiv.swap_apply_def, hs1, ht1,
      ← pow_two, hz2]
  · exact False.elim (he (hs1.trans ht1.symm))

private theorem witness_not_global : ¬ GloballyMatched witnessX witnessY := by
  rintro ⟨e, t, ht⟩
  have hP : ∀ p : rootsOfUnity 2 ℂ × rootsOfUnity 2 ℂ, p ^ 2 = 1 := by
    intro p
    exact Prod.ext (Subtype.ext p.1.property) (Subtype.ext p.2.property)
  have hleft (p : rootsOfUnity 2 ℂ × rootsOfUnity 2 ℂ) (i : Fin 3) :
      witnessY i (p, 1) = witnessX i (p, 1) := by
    fin_cases i <;> simp [witnessX, witnessY, firstSign, secondSign, thirdRoot]
  have heP (p : rootsOfUnity 2 ℂ × rootsOfUnity 2 ℂ) : e (p, 1) = 1 := by
    have hp : (p, (1 : rootsOfUnity 3 ℂ)) ^ 2 = 1 := by ext <;> simp [hP]
    have he2 : e (p, 1) ^ 2 = 1 := by rw [← map_pow, hp, map_one]
    have heq (i : Fin 3) : witnessY i (p, 1) = e (p, 1) * witnessX (t i) (p, 1) :=
      DFunLike.congr_fun (ht i) (p, 1)
    have hd : determinant witnessY (p, 1) = determinant witnessX (p, 1) := by
      simp only [determinant_apply]
      exact Finset.prod_congr rfl (fun i _ => hleft p i)
    have he3 : e (p, 1) ^ 3 = 1 := by rw [← match_determinant heq, hd, div_self']
    exact coprime_roots (by decide : Nat.Coprime 2 3) he2 he3
  have hnc : ¬ IsCyclic (rootsOfUnity 2 ℂ × rootsOfUnity 2 ℂ) := by
    intro hc
    let := hc
    have hh := coprime_card_of_isCyclic_prod (rootsOfUnity 2 ℂ) (rootsOfUnity 2 ℂ)
    rw [Complex.card_rootsOfUnity] at hh
    norm_num at hh
  have hinj := faithful_characters_injective hnc (faithful_left witness_faithful)
  have hfix (i : Fin 3) : t i = i := by
    apply Eq.symm
    apply hinj
    apply DFunLike.ext
    intro p
    have hi := DFunLike.congr_fun (ht i) (p, 1)
    change witnessY i (p, 1) = e (p, 1) * witnessX (t i) (p, 1) at hi
    rw [hleft, heP, one_mul] at hi
    exact hi
  have he : e = 1 := by simpa [witnessX, witnessY, hfix 0] using (ht 0).symm
  have hz (z : rootsOfUnity 3 ℂ) : z = 1 := by
    have hi := DFunLike.congr_fun (ht 1) ((1, 1), z)
    have hzi : (z.val)⁻¹ = z.val := by
      simpa [witnessX, witnessY, hfix 1, he, firstSign, thirdRoot] using hi
    have hz2 : z.val ^ 2 = 1 := by
      rw [pow_two]
      exact eq_inv_iff_mul_eq_one.mp hzi.symm
    exact Subtype.ext (coprime_roots (by decide : Nat.Coprime 2 3) hz2 z.property)
  have hsub : Subsingleton (rootsOfUnity 3 ℂ) := ⟨fun x y => (hz x).trans (hz y).symm⟩
  let := hsub
  have hc : Nat.card (rootsOfUnity 3 ℂ) = 1 := Nat.card_unique
  rw [Complex.card_rootsOfUnity] at hc
  omega

private theorem witness_support : Supports WitnessGroup :=
  ⟨witnessX, witnessY, witness_faithful,
    faithful_of_pointwise witness_faithful witness_pointwise, witness_pointwise, witness_not_global⟩

private noncomputable def cyclicRoots (n : ℕ) [NeZero n] :
    Cyclic n ≃* rootsOfUnity n ℂ :=
  mulEquivOfCyclicCardEq (by rw [cyclic_card, Complex.card_rootsOfUnity])

private theorem source_witness : Supports (Source 1 1 3) := by
  let e := (primaryDecomposition 1 1 3 (by decide)).trans
    (MulEquiv.prodCongr (MulEquiv.prodCongr (cyclicRoots 2) (cyclicRoots 2)) (cyclicRoots 3))
  exact supports_of_equiv e witness_support

/-- Exactly one parameter triple supports two faithful projectively pointwise matched
character triples with no single character twist and permutation. -/
theorem support_iff (a b m : ℕ) (hab : a ≤ b) (hm : 1 ≤ m) (hodd : Odd m) :
    Supports (Source a b m) ↔ a = 1 ∧ b = 1 ∧ m = 3 := by
  let : NeZero m := ⟨by omega⟩
  constructor
  · intro hs
    by_cases ha0 : a = 0
    · subst a
      let : IsCyclic (Source 0 b m) := by
        apply Group.isCyclic_prod_iff.mpr
        exact ⟨inferInstance, inferInstance, by simp⟩
      obtain ⟨X, Y, _, _, hp, hn⟩ := hs
      exact False.elim (hn (cyclic_global hp))
    have ha : 1 ≤ a := by omega
    have hsplit := supports_of_equiv (primaryDecomposition a b m hodd).symm hs
    by_cases hb : b ≤ 1
    · have ha1 : a = 1 := by omega
      have hb1 : b = 1 := by omega
      subst a b
      have hm3 : m = 3 := support_small_odd hodd (by simpa using hsplit)
      exact ⟨rfl, rfl, hm3⟩
    · exact False.elim (no_support_higher ha hab (by omega) hodd hsplit)
  · rintro ⟨rfl, rfl, rfl⟩
    exact source_witness

end D5.S3.FiniteGroups.ToralCharacterSupport
