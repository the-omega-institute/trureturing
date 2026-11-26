/- GID: D5/S1/Eigenstructure/NilSemigroup
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/NilSemigroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lit/yahaghi2002operatorsemigroups]
   utility: none
   digest: Nil semigroups of endomorphisms vanish after dimension many factors. -/

module

public import OmegaBuild.Commands
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

compile_only_with_mathlib

/-! # Nil semigroups on finite-dimensional left vector spaces -/

@[expose] public section

namespace D5.S1.Eigenstructure.NilSemigroup

open Module

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

variable {K : Type u} [DivisionRing K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem exists_sandwich_zero (S : Set (Module.End K V))
    (hmul : ∀ A ∈ S, ∀ B ∈ S, A * B ∈ S)
    (hnil : ∀ A ∈ S, IsNilpotent A) (hne : ∃ T ∈ S, T ≠ 0) :
    ∃ T ∈ S, T ≠ 0 ∧ ∀ A ∈ S, T * A * T = 0 := by
  classical
  have hex : ∃ n : ℕ, ∃ T ∈ S, T ≠ 0 ∧ finrank K (LinearMap.range T) = n := by
    obtain ⟨T, hT, hT0⟩ := hne
    exact ⟨_, T, hT, hT0, rfl⟩
  obtain ⟨T, hT, hT0, hr⟩ := Nat.find_spec hex
  refine ⟨T, hT, hT0, ?_⟩
  intro A hA
  by_contra hbad
  have hle : LinearMap.range (T * A * T) ≤ LinearMap.range T := by
    rintro x ⟨y, rfl⟩
    exact ⟨A (T y), rfl⟩
  have hdim : finrank K (LinearMap.range T) ≤ finrank K (LinearMap.range (T * A * T)) := by
    rw [hr]
    exact Nat.find_min' hex ⟨T * A * T, hmul _ (hmul _ hT _ hA) _ hT, hbad, rfl⟩
  have heq : LinearMap.range (T * A * T) = LinearMap.range T :=
    Submodule.eq_of_le_of_finrank_le hle hdim
  have hstable : (LinearMap.range T).map (T * A) = LinearMap.range T := by
    rw [← LinearMap.range_comp]
    exact heq
  have hp : ∀ n : ℕ, (LinearMap.range T).map ((T * A) ^ n) = LinearMap.range T := by
    intro n
    induction n with
    | zero => simp only [pow_zero, Module.End.one_eq_id, Submodule.map_id]
    | succ n ih =>
      rw [pow_succ', Module.End.mul_eq_comp, Submodule.map_comp, ih, hstable]
  obtain ⟨n, hn⟩ := hnil (T * A) (hmul _ hT _ hA)
  have hz := hp n
  rw [hn, Submodule.map_zero] at hz
  exact hT0 (LinearMap.range_eq_bot.mp hz.symm)

/-- A nil semigroup on a nonzero finite-dimensional space has a common nonzero
annihilated vector. -/
theorem exists_common_annihilator {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Set (Module.End K V))
    (hmul : ∀ A ∈ S, ∀ B ∈ S, A * B ∈ S)
    (hnil : ∀ A ∈ S, IsNilpotent A) [Nontrivial V] :
    ∃ x : V, x ≠ 0 ∧ ∀ A ∈ S, A x = 0 := by
  classical
  by_cases hz : ∀ T ∈ S, T = 0
  · obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact ⟨x, hx, fun A hA => by rw [hz A hA]; rfl⟩
  push Not at hz
  obtain ⟨T, hT, hT0, hsand⟩ := exists_sandwich_zero S hmul hnil hz
  have hex : ∃ x : V, T x ≠ 0 := by
    by_contra! h
    exact hT0 (LinearMap.ext h)
  obtain ⟨x, hx⟩ := hex
  let U : Submodule K V := Submodule.span K {y | ∃ A ∈ S, y = A (T x)}
  have hker : U ≤ LinearMap.ker T := by
    apply Submodule.span_le.mpr
    rintro y ⟨A, hA, rfl⟩
    exact congrArg (fun f : Module.End K V => f x) (hsand A hA)
  have hinv : ∀ A ∈ S, ∀ y ∈ U, A y ∈ U := by
    intro A hA y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨B, hB, rfl⟩ := hy
      exact Submodule.subset_span ⟨A * B, hmul A hA B hB, rfl⟩
    | zero => simp
    | add y z hy hz hy' hz' => simpa using U.add_mem hy' hz'
    | smul a y hy hy' => simpa using U.smul_mem a hy'
  by_cases hU : U = ⊥
  · refine ⟨T x, hx, ?_⟩
    intro A hA
    have hmem : A (T x) ∈ U := Submodule.subset_span ⟨A, hA, rfl⟩
    simpa only [hU, Submodule.mem_bot] using hmem
  have hproper : U ≠ ⊤ := by
    intro h
    have ht : T x = 0 := hker (h ▸ Submodule.mem_top)
    exact hx ht
  let : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
  let R : S → Module.End K U := fun A => A.val.restrict (hinv A.val A.property)
  have hRmul : ∀ A ∈ Set.range R, ∀ B ∈ Set.range R, A * B ∈ Set.range R := by
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    refine ⟨⟨A.val * B.val, hmul _ A.property _ B.property⟩, ?_⟩
    rfl
  have hRnil : ∀ A ∈ Set.range R, IsNilpotent A := by
    rintro _ ⟨A, rfl⟩
    obtain ⟨n, hn⟩ := hnil A.val A.property
    refine ⟨n, ?_⟩
    change (A.val.restrict (hinv A.val A.property)) ^ n = 0
    rw [Module.End.pow_restrict]
    ext y
    exact congrArg (fun f : Module.End K V => f y.val) hn
  obtain ⟨y, hy, hkill⟩ := exists_common_annihilator (V := U) (Set.range R) hRmul hRnil
  refine ⟨y.val, ?_, ?_⟩
  · intro h
    exact hy (Subtype.ext h)
  · intro A hA
    exact congrArg Subtype.val (hkill (R ⟨A, hA⟩) ⟨⟨A, hA⟩, rfl⟩)
termination_by finrank K V
decreasing_by exact Submodule.finrank_lt hproper

/-- Every native ordered product of at least `finrank K V` members of a nil
semigroup is zero. -/
theorem list_prod_eq_zero {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Set (Module.End K V))
    (hmul : ∀ A ∈ S, ∀ B ∈ S, A * B ∈ S)
    (hnil : ∀ A ∈ S, IsNilpotent A)
    (l : List (Module.End K V)) (hl : ∀ A ∈ l, A ∈ S)
    (hlen : finrank K V ≤ l.length) : l.prod = 0 := by
  classical
  by_cases hV : Subsingleton V
  · let _ := hV
    exact Subsingleton.elim _ _
  let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
  obtain ⟨x, hx, hkill⟩ := exists_common_annihilator S hmul hnil
  let U : Submodule K V := K ∙ x
  have hkillU : ∀ A ∈ S, ∀ y ∈ U, A y = 0 := by
    intro A hA
    change U ≤ LinearMap.ker A
    apply Submodule.span_le.mpr
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hkill A hA
  have hinv : ∀ A ∈ S, U ≤ U.comap A := by
    intro A hA y hy
    change A y ∈ U
    rw [hkillU A hA y hy]
    exact U.zero_mem
  have hdim : finrank K (V ⧸ U) + 1 = finrank K V := by
    have h := U.finrank_quotient_add_finrank
    rwa [show finrank K U = 1 from finrank_span_singleton hx] at h
  let q : Module.End K V → Module.End K (V ⧸ U) := fun A =>
    if hA : A ∈ S then U.mapQ U A (hinv A hA) else 0
  have hq (A : Module.End K V) (hA : A ∈ S) :
      q A = U.mapQ U A (hinv A hA) := dite_eq_left hA
  have hqmul (A : Module.End K V) (hA : A ∈ S)
      (B : Module.End K V) (hB : B ∈ S) : q (A * B) = q A * q B := by
    rw [hq _ (hmul A hA B hB), hq A hA, hq B hB]
    ext y
    rfl
  have hmulQ : ∀ A ∈ q '' S, ∀ B ∈ q '' S, A * B ∈ q '' S := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    exact ⟨A * B, hmul A hA B hB, hqmul A hA B hB⟩
  have hnilQ : ∀ A ∈ q '' S, IsNilpotent A := by
    rintro _ ⟨A, hA, rfl⟩
    obtain ⟨n, hn⟩ := hnil A hA
    refine ⟨n, ?_⟩
    rw [hq A hA, ← U.mapQ_pow (hinv A hA) n]
    simp only [hn, Submodule.mapQ_zero]
  have hprod : ∀ (w : List (Module.End K V)), (∀ A ∈ w, A ∈ S) → ∀ y : V,
      (w.map q).prod (U.mkQ y) = U.mkQ (w.prod y) := by
    intro w hw y
    induction w with
    | nil => rfl
    | cons A w ih =>
      have hA := hw A (List.mem_cons_self ..)
      have hw' : ∀ B ∈ w, B ∈ S := fun B hB => hw B (List.mem_cons_of_mem A hB)
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [ih hw', hq A hA]
      rfl
  cases l with
  | nil =>
    have hp := finrank_pos (R := K) (M := V)
    simp only [List.length_nil] at hlen
    omega
  | cons A w =>
    have hA := hl A (List.mem_cons_self ..)
    have hw : ∀ B ∈ w, B ∈ S := fun B hB => hl B (List.mem_cons_of_mem A hB)
    have hwQ : ∀ B ∈ w.map q, B ∈ q '' S := by
      intro B hB
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
      exact ⟨C, hw C hC, rfl⟩
    have hlenQ : finrank K (V ⧸ U) ≤ (w.map q).length := by
      simp only [List.length_cons] at hlen
      simp only [List.length_map]
      omega
    have hz := list_prod_eq_zero (V := V ⧸ U) (q '' S) hmulQ hnilQ
      (w.map q) hwQ hlenQ
    apply LinearMap.ext
    intro y
    change A (w.prod y) = 0
    apply hkillU A hA
    apply (Submodule.Quotient.mk_eq_zero U).mp
    change U.mkQ (w.prod y) = 0
    rw [← hprod w hw y, hz]
    rfl
termination_by finrank K V
decreasing_by
  exact (Nat.lt_succ_self (finrank K (V ⧸ K ∙ x))).trans_eq
    (by simpa only [finrank_span_singleton hx] using (K ∙ x).finrank_quotient_add_finrank)

end D5.S1.Eigenstructure.NilSemigroup
