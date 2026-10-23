/- GID: D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual maximal ancestry gives primitive roots and the full ordered pair law. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates

open GenealogicalFiberTransport (Source substitution)
open Geometry.GeometryEntranceRatio (EntranceFiber)
open D5.S3.Combinatorics.Partitions.PaddedWordPartition (G)
open D5.S3.Combinatorics.Partitions.WordPartitionInverse (wd)

/-- Alpha has no actual substitution predecessor. -/
theorem no_alpha (t : Source) : substitution t ≠ .of true := by
  cases t with
  | of b =>
    cases b <;> simp only [substitution, FreeMagma.lift_of, Bool.false_eq_true,
      ↓reduceIte] <;> intro h <;> injection h <;> contradiction
  | mul s t => intro h; change FreeMagma.mul _ _ = .of true at h; cases h

/-- An actual primitive source has no one-step substitution predecessor. -/
def Primitive (p : Source) : Prop := ¬ ∃ x : Source, substitution x = p

/-- All actual ancestors of a fixed source, with their legal exponents. -/
def Ancestors (t : Source) := {a : Source × ℕ // substitution^[a.2] a.1 = t}

private instance ancestorsFinite (t : Source) : Finite (Ancestors t) := by
  let f : Ancestors t → EntranceFiber (G (wd t)) := fun a =>
    ⟨(t, a.val.1, a.val.2), rfl, a.property⟩
  exact Finite.of_injective f (fun a b h => by
    apply Subtype.ext
    exact congrArg (fun p : EntranceFiber (G (wd t)) => p.val.2) h)

/-- The set of legal exponents, without any artificial cutoff. -/
def legalIndices (t : Source) : Finset ℕ :=
  (Set.finite_range (fun a : Ancestors t => a.val.2)).toFinset

private theorem mem_legalIndices (t : Source) (k : ℕ) :
    k ∈ legalIndices t ↔ ∃ x : Source, substitution^[k] x = t := by
  classical
  simp only [legalIndices, Set.Finite.mem_toFinset, Set.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.val.1, a.property⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨(x,k), hx⟩, rfl⟩

private theorem legalIndices_nonempty (t : Source) : (legalIndices t).Nonempty :=
  ⟨0, (mem_legalIndices t 0).mpr ⟨t, rfl⟩⟩

/-- The maximum of the actual legal substitution exponents. -/
abbrev depth (t : Source) : ℕ := Geometry.AncestorAreaInstability.depth t

private theorem indices_finite (t : Source) :
    Set.Finite {k : ℕ | ∃ p : Source, substitution^[k] p = t} := by
  have he : {k : ℕ | ∃ p : Source, substitution^[k] p = t} =
      (legalIndices t : Set ℕ) := by
    ext k
    exact (mem_legalIndices t k).symm
  rw [he]
  exact Finset.finite_toSet _

private theorem depth_legal (t : Source) : ∃ p : Source, substitution^[depth t] p = t := by
  have ne : Set.Nonempty {k : ℕ | ∃ p : Source, substitution^[k] p = t} := by
    obtain ⟨k, hk⟩ := legalIndices_nonempty t
    exact ⟨k, (mem_legalIndices t k).mp hk⟩
  exact ne.csSup_mem (indices_finite t)

/-- The actual ancestor at the maximum legal exponent. -/
def root (t : Source) : Source := Classical.choose (depth_legal t)

/-- The ray flag tests the primitive endpoint, rather than the current leaf label. -/
def flag (t : Source) : Bool := decide (root t = .of true)

/-- The intrinsic substitution depth and alpha-ray flag. -/
def Q (t : Source) : ℕ × Bool := (depth t, flag t)

private theorem root_spec (t : Source) : substitution^[depth t] (root t) = t :=
  Classical.choose_spec (depth_legal t)

private theorem legal_le (t : Source) (k : ℕ)
    (hk : ∃ x : Source, substitution^[k] x = t) : k ≤ depth t :=
  le_csSup (indices_finite t).bddAbove hk

private theorem legal_iff (t : Source) (k : ℕ) :
    (∃ x : Source, substitution^[k] x = t) ↔ k ≤ depth t := by
  constructor
  · exact legal_le t k
  · intro hk
    refine ⟨substitution^[depth t - k] (root t), ?_⟩
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le hk]
    exact root_spec t

private theorem root_primitive (t : Source) : Primitive (root t) := by
  rintro ⟨x, hx⟩
  have h : depth t + 1 ≤ depth t := legal_le t (depth t + 1) ⟨x, by
    rw [Function.iterate_succ_apply, hx]
    exact root_spec t⟩
  omega

private theorem substitution_injective : Function.Injective substitution :=
  SourceTransportCentralizer.source_transport_centralizer.2.2.1 substitution
    ⟨substitution.map_mul, fun _ => rfl⟩

private theorem primitive_index (p : Source) (hp : Primitive p) (n : ℕ)
    (x : Source) (hx : substitution^[n] x = p) : n = 0 := by
  cases n with
  | zero => rfl
  | succ n => exact False.elim (hp ⟨substitution^[n] x, by
      simpa only [Function.iterate_succ_apply'] using hx⟩)

private theorem normal_depth (p : Source) (hp : Primitive p) (n : ℕ) :
    depth (substitution^[n] p) = n := by
  apply le_antisymm
  · by_contra hn
    have hle : n ≤ depth (substitution^[n] p) := by omega
    obtain ⟨x, hx⟩ := depth_legal (substitution^[n] p)
    have hcancel : substitution^[depth (substitution^[n] p) - n] x = p := by
      apply substitution_injective.iterate n
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le hle]
      exact hx
    have hz := primitive_index p hp _ x hcancel
    omega
  · exact legal_le _ n ⟨p, rfl⟩

private theorem normal_root (p : Source) (hp : Primitive p) (n : ℕ) :
    root (substitution^[n] p) = p := by
  apply substitution_injective.iterate n
  have h := root_spec (substitution^[n] p)
  rwa [normal_depth p hp n] at h

private theorem normal_Q (p : Source) (hp : Primitive p) (n : ℕ) :
    Q (substitution^[n] p) = (n, decide (p = .of true)) := by
  simp only [Q, flag, normal_depth p hp n, normal_root p hp n]

/-- Intrinsic ancestry, the primitive endpoint and its unique ray representation. -/
theorem intrinsic_coordinates (t : Source) :
    (∀ k : ℕ, (∃ x : Source, substitution^[k] x = t) ↔ k ≤ depth t) ∧
    Primitive (root t) ∧ substitution^[depth t] (root t) = t ∧
    (∀ (p : Source) (n : ℕ), Primitive p → substitution^[n] p = t →
      n = depth t ∧ p = root t) ∧
    (flag t = true ↔ substitution^[depth t] (.of true) = t) := by
  refine ⟨legal_iff t, root_primitive t, root_spec t, ?_, ?_⟩
  · intro p n hp he
    have hd : depth t = n := he ▸ normal_depth p hp n
    have hr : root t = p := he ▸ normal_root p hp n
    exact ⟨hd.symm, hr.symm⟩
  · simp only [flag, decide_eq_true_eq]
    constructor
    · intro hr
      rw [← hr]
      exact root_spec t
    · intro he
      exact substitution_injective.iterate (depth t) ((root_spec t).trans he.symm)

private theorem primitive_alpha : Primitive (.of true) := by
  rintro ⟨x, hx⟩
  exact no_alpha x hx

private theorem iterate_pair (n : ℕ) (s t : Source) :
    substitution^[n] (.mul s t) = .mul (substitution^[n] s) (substitution^[n] t) :=
  Function.Semiconj₂.iterate
    (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
      substitution.map_mul) n s t

theorem pair_image (s t : Source) :
    (∃ x : Source, substitution x = .mul s t) ↔
      (s = .of false ∧ t = .of true) ∨
      ((∃ x : Source, substitution x = s) ∧ (∃ y : Source, substitution y = t)) := by
  constructor
  · rintro ⟨x, hx⟩
    cases x with
    | of b =>
      cases b with
      | false =>
        change FreeMagma.mul (.of false) (.of true) = .mul s t at hx
        injection hx with hs ht
        exact Or.inl ⟨hs.symm, ht.symm⟩
      | true => change FreeMagma.of false = .mul s t at hx; cases hx
    | mul x y =>
      change FreeMagma.mul (substitution x) (substitution y) = .mul s t at hx
      injection hx with hs ht
      exact Or.inr ⟨⟨x,hs⟩, ⟨y,ht⟩⟩
  · rintro (⟨rfl,rfl⟩ | ⟨⟨x,rfl⟩,⟨y,rfl⟩⟩)
    · exact ⟨.of false, rfl⟩
    · exact ⟨.mul x y, substitution.map_mul x y⟩

private theorem pair_update (s t : Source) :
    Q (.mul s t) =
      if flag s = true ∧ flag t = true ∧ depth s = depth t + 1
      then (depth t + 2, true) else (min (depth s) (depth t), false) := by
  classical
  let a := depth s
  let b := depth t
  let m := min a b
  let r := substitution^[a-m] (root s)
  let z := substitution^[b-m] (root t)
  have hs : substitution^[m] r = s := by
    dsimp [r]
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le (min_le_left a b)]
    exact root_spec s
  have ht : substitution^[m] z = t := by
    dsimp [z]
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le (min_le_right a b)]
    exact root_spec t
  have hpair : substitution^[m] (.mul r z) = .mul s t := by
    rw [iterate_pair, hs, ht]
  have hprimitive : Primitive r ∨ Primitive z := by
    rcases le_total a b with hab | hba
    · left
      have he : a-m = 0 := by dsimp [m]; omega
      simpa only [r, he, Function.iterate_zero_apply] using root_primitive s
    · right
      have he : b-m = 0 := by dsimp [m]; omega
      simpa only [z, he, Function.iterate_zero_apply] using root_primitive t
  have hexception : (r = .of false ∧ z = .of true) ↔
      flag s = true ∧ flag t = true ∧ depth s = depth t + 1 := by
    constructor
    · rintro ⟨hr,hz⟩
      have hz0 : b-m = 0 := primitive_index (.of true) primitive_alpha _ (root t) hz
      have rz : root t = .of true := by
        simpa only [z, hz0, Function.iterate_zero_apply] using hz
      have hb : b = m := by have := min_le_right a b; dsimp [m] at *; omega
      have sa : s = substitution^[m+1] (.of true) := by
        rw [← hs, hr]
        rfl
      have sd : depth s = m+1 := sa ▸ normal_depth _ primitive_alpha (m+1)
      have sr : root s = .of true := sa ▸ normal_root _ primitive_alpha (m+1)
      exact ⟨by simp [flag,sr], by simp [flag,rz], by dsimp [b] at hb; omega⟩
    · rintro ⟨hf,hg,hab⟩
      have sr : root s = .of true := of_decide_eq_true hf
      have tr : root t = .of true := of_decide_eq_true hg
      have hm : m = b := by dsimp [m,a,b]; omega
      constructor
      · dsimp [r]
        rw [sr, hm, show a-b = 1 by dsimp [a,b]; omega]
        rfl
      · dsimp [z]
        rw [tr, hm, Nat.sub_self]
        rfl
  by_cases he : flag s = true ∧ flag t = true ∧ depth s = depth t + 1
  · rw [if_pos he]
    obtain ⟨hr,hz⟩ := hexception.mpr he
    have hb : m = depth t := by dsimp [m,a,b]; omega
    have hp : .mul s t = substitution^[depth t+2] (.of true) := by
      rw [← hpair, hr, hz, hb]
      rw [Function.iterate_add_apply]
      rfl
    rw [hp, normal_Q _ primitive_alpha]
    rfl
  · rw [if_neg he]
    have hp : Primitive (.mul r z) := by
      intro hi
      rcases (pair_image r z).mp hi with he' | ⟨hr,hz⟩
      · exact he (hexception.mp he')
      · rcases hprimitive with h | h
        · exact h hr
        · exact h hz
    rw [← hpair, normal_Q _ hp]
    rfl

/-- The complete intrinsic substitution and ordered-pair laws on every actual source. -/
theorem all_source_coordinate_law :
    (∀ t : Source,
      (∀ k : ℕ, (∃ x : Source, substitution^[k] x = t) ↔ k ≤ depth t) ∧
      Primitive (root t) ∧ substitution^[depth t] (root t) = t ∧
      (∀ (p : Source) (n : ℕ), Primitive p → substitution^[n] p = t →
        n = depth t ∧ p = root t) ∧
      (flag t = true ↔ substitution^[depth t] (.of true) = t)) ∧
    (∀ t : Source, Q (substitution t) = (depth t + 1, flag t)) ∧
    (∀ s t : Source, Q (.mul s t) =
      if flag s = true ∧ flag t = true ∧ depth s = depth t + 1
      then (depth t + 2, true) else (min (depth s) (depth t), false)) ∧
    Q (.of true) = (0, true) ∧ Q (.of false) = (1, true) := by
  refine ⟨intrinsic_coordinates, ?_, pair_update, ?_, ?_⟩
  · intro t
    have h := intrinsic_coordinates t
    have he : substitution t = substitution^[depth t+1] (root t) := by
      rw [Function.iterate_succ_apply', h.2.2.1]
    rw [he, normal_Q _ h.2.1]
    rfl
  · exact normal_Q _ primitive_alpha 0
  · exact normal_Q _ primitive_alpha 1

#print axioms intrinsic_coordinates
#print axioms all_source_coordinate_law

end D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates
