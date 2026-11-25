/- GID: D5/S3/Quantum/Entanglement/OccupancyWordSectors
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/OccupancyWordSectors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Occupation words have multinomial counts and orthonormal uniform vectors. -/

module

public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Ring
public import D5.S1.Ledger.BoundedTimeSlice

set_option backward.privateInPublic true
@[expose] public section

/-!
The finite-class normalization argument in `sector_gram` is adapted from
QuAIR/Lean-QIT, QIT/Symmetry/SymmetricSubspace.lean, commit
c1d59b133b56e3d79efb11ee46a728d290f761f5, declarations
`tensorPowerProfileUnitVector_trace_rankOne_eq_one` and
`tensorPowerProfileUnitVector_inner`.
Copyright (c) 2026 QuAIR. Authors: QuAIR Team. Apache-2.0;
full license: Library/Quantum/raveh2024dicke.md. No upstream NOTICE exists.
Modified here: Fin-indexed words, multiset occupations, and explicit length
hypotheses replace recursive TensorPower and realized-profile subtypes.
Retire this port when this repository's pinned Mathlib provides equivalent
finite-fiber normalized indicator declarations, replacing it by imports.

The counting recurrence and factorial cancellation below also adapt the same
immutable source, declarations `tensorPowerProfileClass_succ_card`,
`tensorPowerProfile_tail_factorial_prod_mul`,
`tensorPowerProfile_multinomial_tail_mul_length`,
`tensorPowerProfile_multinomial_succ_recurrence`, and
`tensorPowerProfileClass_card_eq_multinomial` (lines 501-744).
Modified here: Fin.cons and Multiset.erase implement head/tail removal;
Multiset count/card lemmas replace the realized-profile infrastructure.
Retire this counting port when the repository's pinned Mathlib supplies
equivalent fixed-occupation word-fiber cardinality declarations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.OccupancyWordSectors

noncomputable section
open scoped BigOperators

variable {α : Type*}

abbrev Word (α : Type*) (n : ℕ) := Fin n → α

def occupation {n : ℕ} (w : Word α n) : Multiset α := List.ofFn w

@[simp] theorem occupation_card {n : ℕ} (w : Word α n) :
    (occupation w).card = n := by simp [occupation]

@[simp] theorem occupation_append {t s : ℕ} (u : Word α t) (v : Word α s) :
    occupation (Fin.append u v) = occupation u + occupation v := by
  simp [occupation]

private theorem word_exists (a : Multiset α) {n : ℕ} (h : a.card = n) :
    ∃ w : Word α n, occupation w = a := by
  induction a using Quotient.inductionOn with
  | h l =>
    simp only [Multiset.quot_mk_to_coe, Multiset.coe_card] at h ⊢
    subst n
    exact ⟨l.get, by simp [occupation]⟩

def representative (a : Multiset α) {n : ℕ} (h : a.card = n) : Word α n :=
  Classical.choose (word_exists a h)

@[simp] theorem occupation_representative (a : Multiset α) {n : ℕ}
    (h : a.card = n) : occupation (representative a h) = a :=
  Classical.choose_spec (word_exists a h)

variable [Fintype α] [DecidableEq α]

def sectorWords (n : ℕ) (a : Multiset α) : Finset (Word α n) :=
  Finset.univ.filter (fun w => occupation w = a)

def multiplicity (n : ℕ) (a : Multiset α) : ℕ := (sectorWords n a).card

private theorem count_sum (a : Multiset α) : ∑ z : α, a.count z = a.card :=
  Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)

private theorem multiplicity_succ (a : Multiset α) (n : ℕ) :
    multiplicity (n + 1) a = ∑ z : α, if z ∈ a then multiplicity n (a.erase z) else 0 := by
  classical
  simp only [multiplicity, sectorWords, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => α)).sum_comp
    (fun w => if occupation w = a then 1 else 0), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  have hcons (w : Word α n) :
      occupation (Fin.cons z w) = a ↔ z ∈ a ∧ occupation w = a.erase z := by
    rw [show occupation (Fin.cons z w) = z ::ₘ occupation w by
      simp only [occupation, List.ofFn_cons]; rfl]
    rw [← Multiset.singleton_add, add_comm ({z} : Multiset α),
      Multiset.add_singleton_eq_iff]
  change (∑ w : Word α n, if occupation (Fin.cons z w) = a then 1 else 0) = _
  simp_rw [hcons]
  by_cases hz : z ∈ a <;> simp [hz]

private theorem erase_factorial_prod_mul (a : Multiset α) (z : α) (hz : z ∈ a) :
    (∏ y : α, Nat.factorial ((a.erase z).count y)) * a.count z =
      ∏ y : α, Nat.factorial (a.count y) := by
  classical
  rw [Finset.prod_eq_prod_sdiff_singleton_mul (s := (Finset.univ : Finset α))
      (Finset.mem_univ z) (f := fun y => Nat.factorial (a.count y))]
  rw [Finset.prod_eq_prod_sdiff_singleton_mul (s := (Finset.univ : Finset α))
      (Finset.mem_univ z) (f := fun y => Nat.factorial ((a.erase z).count y))]
  have hprod : (∏ y ∈ (Finset.univ : Finset α) \ {z},
      Nat.factorial ((a.erase z).count y)) =
      ∏ y ∈ (Finset.univ : Finset α) \ {z}, Nat.factorial (a.count y) := by
    apply Finset.prod_congr rfl
    intro y hy
    exact congrArg Nat.factorial (Multiset.count_erase_of_ne (by simpa using
      (Finset.mem_sdiff.mp hy).2) a)
  rw [hprod, Multiset.count_erase_self]
  have hp : 0 < a.count z := Multiset.count_pos.mpr hz
  have hfac : Nat.factorial (a.count z) = a.count z * Nat.factorial (a.count z - 1) := by
    conv_lhs => rw [show a.count z = (a.count z - 1) + 1 by omega]
    rw [Nat.factorial_succ]
    congr 1
    omega
  rw [hfac]
  ring

private theorem multinomial_erase_mul {a : Multiset α} {n : ℕ} (h : a.card = n + 1)
    (z : α) (hz : z ∈ a) :
    (n + 1) * Nat.multinomial Finset.univ (a.erase z).count =
      a.count z * Nat.multinomial Finset.univ a.count := by
  have ht : (a.erase z).card = n := by rw [Multiset.card_erase_of_mem hz, h]; rfl
  have htail := Nat.multinomial_spec (s := Finset.univ) (f := (a.erase z).count)
  have hfull := Nat.multinomial_spec (s := Finset.univ) (f := a.count)
  rw [count_sum, ht] at htail
  rw [count_sum, h] at hfull
  apply Nat.mul_left_cancel (show 0 < ∏ y : α, Nat.factorial ((a.erase z).count y) from
    Finset.prod_pos (fun _ _ => Nat.factorial_pos _))
  calc
    (∏ y : α, Nat.factorial ((a.erase z).count y)) *
        ((n + 1) * Nat.multinomial Finset.univ (a.erase z).count) =
        (n + 1) * ((∏ y : α, Nat.factorial ((a.erase z).count y)) *
          Nat.multinomial Finset.univ (a.erase z).count) := by ring
    _ = (n + 1) * Nat.factorial n := by rw [htail]
    _ = Nat.factorial (n + 1) := (Nat.factorial_succ n).symm
    _ = (∏ y : α, Nat.factorial (a.count y)) * Nat.multinomial Finset.univ a.count :=
      hfull.symm
    _ = (∏ y : α, Nat.factorial ((a.erase z).count y)) *
        (a.count z * Nat.multinomial Finset.univ a.count) := by
      rw [← erase_factorial_prod_mul a z hz]
      ring

private theorem multinomial_succ {a : Multiset α} {n : ℕ} (h : a.card = n + 1) :
    Nat.multinomial Finset.univ a.count =
      ∑ z : α, if z ∈ a then Nat.multinomial Finset.univ (a.erase z).count else 0 := by
  apply Nat.mul_left_cancel (Nat.succ_pos n)
  calc
    (n + 1) * Nat.multinomial Finset.univ a.count =
        (∑ z : α, a.count z) * Nat.multinomial Finset.univ a.count := by rw [count_sum, h]
    _ = ∑ z : α, a.count z * Nat.multinomial Finset.univ a.count := by rw [Finset.sum_mul]
    _ = (n + 1) * ∑ z : α,
        if z ∈ a then Nat.multinomial Finset.univ (a.erase z).count else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ a
      · simpa [hz] using (multinomial_erase_mul h z hz).symm
      · simp [hz]

/-- Cardinality of the actual word carrier, not an algebraically defined count. -/
theorem sector_words_card_multinomial (a : Multiset α) {n : ℕ} (h : a.card = n) :
    (sectorWords n a).card = Nat.multinomial Finset.univ a.count := by
  induction n generalizing a with
  | zero =>
    have ha : a = 0 := Multiset.card_eq_zero.mp h
    subst a
    simp [sectorWords, occupation, Nat.multinomial, Word]
  | succ n ih =>
    change multiplicity (n + 1) a = _
    rw [multiplicity_succ, multinomial_succ h]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ a
    · simp only [if_pos hz]
      exact ih (a.erase z) (by rw [Multiset.card_erase_of_mem hz, h]; rfl)
    · simp [hz]

theorem multiplicity_eq_factorial (a : Multiset α) {n : ℕ} (h : a.card = n) :
    multiplicity n a = Nat.factorial n / ∏ z : α, Nat.factorial (a.count z) := by
  rw [multiplicity, sector_words_card_multinomial a h, Nat.multinomial, count_sum, h]

/-- The existing head-removal recurrence on actual word cardinalities. -/
theorem multiplicity_erase_mul {a : Multiset α} {n : ℕ} (h : a.card = n + 1)
    (i : α) (hi : i ∈ a) :
    (n + 1) * multiplicity n (a.erase i) = a.count i * multiplicity (n + 1) a := by
  have he : (a.erase i).card = n := by rw [Multiset.card_erase_of_mem hi, h]; rfl
  simpa only [multiplicity, sector_words_card_multinomial _ he,
    sector_words_card_multinomial _ h] using multinomial_erase_mul h i hi

theorem multiplicity_pos (a : Multiset α) {n : ℕ} (h : a.card = n) :
    0 < multiplicity n a := by
  apply Finset.card_pos.mpr
  exact ⟨representative a h, by simp [sectorWords]⟩

def sectorVector (n : ℕ) (a : Multiset α) : Word α n → ℂ :=
  fun w => if w ∈ sectorWords n a then
    ((Real.sqrt (multiplicity n a : ℝ) : ℂ)⁻¹) else 0

theorem sector_gram {n : ℕ} (a b : Multiset α) (ha : a.card = n) :
    ∑ w : Word α n, star (sectorVector n a w) * sectorVector n b w =
      if a = b then 1 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    have hm : (multiplicity n a : ℂ) ≠ 0 := by
      exact_mod_cast (multiplicity_pos a ha).ne'
    have hs : (Real.sqrt (multiplicity n a : ℝ) : ℂ) *
        (Real.sqrt (multiplicity n a : ℝ) : ℂ) = (multiplicity n a : ℂ) := by
      norm_cast
      exact Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hterm (w : Word α n) :
        star (sectorVector n a w) * sectorVector n a w =
          if w ∈ sectorWords n a then (multiplicity n a : ℂ)⁻¹ else 0 := by
      by_cases hw : w ∈ sectorWords n a
      · simp only [sectorVector, if_pos hw, star_inv₀, Complex.star_def,
          Complex.conj_ofReal]
        rw [← mul_inv, hs]
      · simp [sectorVector, hw]
    simp only [hterm]
    rw [← Finset.sum_filter]
    simpa [sectorWords, multiplicity, nsmul_eq_mul] using mul_inv_cancel₀ hm
  · have hterm (w : Word α n) :
        star (sectorVector n a w) * sectorVector n b w = 0 := by
      by_cases hw : w ∈ sectorWords n a
      · have hwb : w ∉ sectorWords n b := by
          simp only [sectorWords, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          exact fun h => hab (hw.symm.trans h)
        simp [sectorVector, hwb]
      · simp [sectorVector, hw]
    simp only [hterm, Finset.sum_const_zero, if_neg hab]

def boundaries (a : Multiset α) (t : ℕ) : Finset (Multiset α) :=
  (a.powersetCard t).toFinset

abbrev Boundary (a : Multiset α) (t : ℕ) := {b // b ∈ boundaries a t}

omit [Fintype α] in
theorem boundary_spec (a : Multiset α) (t : ℕ) (b : Boundary a t) :
    b.val ≤ a ∧ b.val.card = t := by
  simpa [boundaries, Multiset.mem_powersetCard] using b.property

omit [Fintype α] in
theorem complement_card {a : Multiset α} {t s : ℕ} (h : a.card = t + s)
    (b : Boundary a t) : (a - b.val).card = s := by
  rw [Multiset.card_sub (boundary_spec a t b).1, h, (boundary_spec a t b).2]
  omega

omit [Fintype α] in
theorem complement_injective (a : Multiset α) (t : ℕ) :
    Function.Injective (fun b : Boundary a t => a - b.val) := by
  intro b c h
  dsimp only at h
  apply Subtype.ext
  have hb := Multiset.sub_add_cancel (boundary_spec a t b).1
  have hc := Multiset.sub_add_cancel (boundary_spec a t c).1
  rw [h] at hb
  exact add_left_cancel (hb.trans hc.symm)

private def boundaryCountEquiv (a : Multiset α) (t : ℕ) :
    Boundary a t ≃ {P : {P : α → ℕ // ∑ i, P i = t} // ∀ i, P.val i ≤ a.count i} :=
  (show Boundary a t ≃ {s : Sym α t // (s : Multiset α) ≤ a} from
    { toFun := fun b => ⟨⟨b.val, (boundary_spec a t b).2⟩, (boundary_spec a t b).1⟩
      invFun := fun s => ⟨s.val.val, by
        simpa [boundaries, Multiset.mem_powersetCard] using And.intro s.property s.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    ((Sym.equivNatSumOfFintype α t).subtypeEquiv (fun s => by
      simp only [Multiset.le_iff_count, Sym.coe_equivNatSumOfFintype_apply_apply]))

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Actual occupation with one distinguished head and arbitrary tail capacities. -/
def capacityOccupation (A : ℕ) (a : I → ℕ) : Multiset (Option I) :=
  ((Sym.equivNatSumOfFintype (Option I) (A + ∑ i, a i)).symm
    ⟨fun i => i.elim A a, by simp [Fintype.sum_option]⟩).val

@[simp] theorem capacity_occupation_card (A : ℕ) (a : I → ℕ) :
    (capacityOccupation A a).card = A + ∑ i, a i := Sym.card_coe

@[simp] theorem capacity_occupation_count (A : ℕ) (a : I → ℕ) (i : Option I) :
    (capacityOccupation A a).count i = i.elim A a := by
  exact congrArg (fun P => P.val i)
    ((Sym.equivNatSumOfFintype (Option I) (A + ∑ i, a i)).apply_symm_apply
      ⟨fun i => i.elim A a, by simp [Fintype.sum_option]⟩)

/-- Restrict Mathlib's multiset/count equivalence, then separate head and tails. -/
def boundaryTimeSliceEquiv (A : ℕ) (a : I → ℕ) (t : ℕ) :
    Boundary (capacityOccupation A a) t ≃ D5.S1.Ledger.BoundedTimeSlice.TimeSlice A a t :=
  (boundaryCountEquiv (capacityOccupation A a) t).trans
    { toFun := fun P => ⟨(⟨P.val.val none, Nat.lt_succ_of_le (by
          simpa using P.property none)⟩,
        fun i => ⟨P.val.val (some i), Nat.lt_succ_of_le (by
          simpa using P.property (some i))⟩), by
        simpa [D5.S1.Ledger.BoundedTimeSlice.tailSum, Fintype.sum_option] using P.val.property⟩
      invFun := fun x => ⟨⟨fun i => i.elim x.val.1.val (fun j => (x.val.2 j).val), by
        simpa [Fintype.sum_option, D5.S1.Ledger.BoundedTimeSlice.tailSum] using x.property⟩,
        fun i => by
          cases i with
          | none => simpa using Nat.le_of_lt_succ x.val.1.isLt
          | some i => simpa using Nat.le_of_lt_succ (x.val.2 i).isLt⟩
      left_inv := fun P => by
        apply Subtype.ext
        apply Subtype.ext
        funext i
        cases i <;> rfl
      right_inv := fun x => by
        apply Subtype.ext
        rfl }

theorem boundary_time_slice_coordinates (A : ℕ) (a : I → ℕ) (t : ℕ)
    (b : Boundary (capacityOccupation A a) t) :
    (boundaryTimeSliceEquiv A a t b).val.1.val = b.val.count none ∧
      ∀ i, ((boundaryTimeSliceEquiv A a t b).val.2 i).val = b.val.count (some i) :=
  ⟨rfl, fun _ => rfl⟩

theorem boundary_count_eq_sliceCount (A : ℕ) (a : I → ℕ) (t : ℕ) :
    (boundaries (capacityOccupation A a) t).card =
      D5.S1.Ledger.BoundedTimeSlice.sliceCount A a t := by
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (boundaryTimeSliceEquiv A a t)

example : Nonempty (Word Bool 3) := ⟨fun _ => true⟩

example : ∃ a : Multiset Bool, a.card = 3 ∧ 0 < multiplicity 3 a :=
  ⟨{true, false, true}, by decide, multiplicity_pos _ (by decide)⟩

example : multiplicity 0 (0 : Multiset (Fin 0)) = 1 := by
  simp [multiplicity, sectorWords, occupation]

example (a : Multiset α) : (boundaries a 0).card = 1 ∧
    (boundaries a a.card).card = 1 := by simp [boundaries]

example : (capacityOccupation 0 (fun i : Fin 0 => i.elim0)).card = 0 := by simp

example (t : ℕ) : (boundaries (capacityOccupation 0 (fun _ : I => 0)) t).card =
    D5.S1.Ledger.BoundedTimeSlice.sliceCount 0 (fun _ : I => 0) t :=
  boundary_count_eq_sliceCount _ _ _

example (A : ℕ) (a : I → ℕ) (h : Fin (A + 1))
    (x : D5.S1.Ledger.BoundedTimeSlice.TailBox a) :
    ∃ b : Boundary (capacityOccupation A a) (h.val + D5.S1.Ledger.BoundedTimeSlice.tailSum x),
      b.val.count none = h.val ∧ ∀ i, b.val.count (some i) = (x i).val := by
  let y : D5.S1.Ledger.BoundedTimeSlice.TimeSlice A a
      (h.val + D5.S1.Ledger.BoundedTimeSlice.tailSum x) := ⟨(h, x), rfl⟩
  refine ⟨(boundaryTimeSliceEquiv A a _).symm y, ?_⟩
  have hc := boundary_time_slice_coordinates A a _ ((boundaryTimeSliceEquiv A a _).symm y)
  rw [Equiv.apply_symm_apply] at hc
  exact ⟨hc.1.symm, fun i => (hc.2 i).symm⟩

example : Nonempty (Boundary (capacityOccupation 2 (fun _ : Bool => 2)) 3) :=
  ⟨(boundaryTimeSliceEquiv 2 (fun _ : Bool => 2) 3).symm
    ⟨(⟨1, by norm_num⟩, fun _ => ⟨1, by norm_num⟩), by decide⟩⟩

end
end D5.S3.Quantum.Entanglement.OccupancyWordSectors
