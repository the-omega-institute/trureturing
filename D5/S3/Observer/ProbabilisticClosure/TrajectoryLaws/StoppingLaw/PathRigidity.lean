/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/PathRigidity
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/PathRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed biased zero-prefix masses recover distinct consecutive edges and target separation. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- A fixed interior bias; competitors may depend on this same parameter. -/
structure Bias where
  p : ℝ
  pos : 0 < p
  lt_one : p < 1
  biased : p ≠ 1 / 2

namespace Bias

def π (β : Bias) (s : Bool) : ℝ := if s then β.p else 1 - β.p

def T (β : Bias) (n : ℕ) : ℝ := (1 - β.p)^n + β.p^n

def d (β : Bias) (n : ℕ) : ℝ := β.T n - β.T (n + 1)

private theorem π_pos (β : Bias) (s : Bool) : 0 < β.π s := by
  cases s <;> simp only [π, Bool.false_eq_true, ↓reduceIte]
  · linarith [β.lt_one]
  · exact β.pos

theorem π_sum (β : Bias) : β.π false + β.π true = 1 := by simp [π]

theorem T_one (β : Bias) : β.T 1 = 1 := by simp [T]

private theorem d_formula (β : Bias) (n : ℕ) :
    β.d n = (1 - β.p)^n * β.p + β.p^n * (1 - β.p) := by
  simp only [d, T, pow_succ]
  ring

theorem d_pos (β : Bias) (n : ℕ) : 0 < β.d n := by
  rw [d_formula]
  have := β.pos
  have : 0 < 1 - β.p := by linarith [β.lt_one]
  positivity

theorem T_succ_lt (β : Bias) (n : ℕ) : β.T (n + 1) < β.T n := by
  have := β.d_pos n
  unfold d at this
  linarith

theorem T_antitone (β : Bias) : Antitone β.T := by
  exact (strictAnti_nat_of_succ_lt β.T_succ_lt).antitone

private theorem unequal_powers (β : Bias) {n : ℕ} (hn : 0 < n) :
    (1 - β.p)^n ≠ β.p^n := by
  have hn0 : n ≠ 0 := by omega
  have h0 : 0 < 1 - β.p := by linarith [β.lt_one]
  have hne : 1 - β.p ≠ β.p := by intro h; apply β.biased; linarith
  rcases lt_or_gt_of_ne hne with h | h
  · exact ne_of_lt (pow_lt_pow_left₀ h h0.le hn0)
  · exact ne_of_gt (pow_lt_pow_left₀ h β.pos.le hn0)

/-- The strict difference for a detached edge, with a successor exponent to avoid subtraction. -/
private theorem detached_gap_factorization (β : Bias) (n : ℕ) :
    β.T (n + 3) - β.T 2 * β.T (n + 2) =
      (1 - β.p) * β.p * ((1 - β.p) - β.p) *
        ((1 - β.p)^(n + 1) - β.p^(n + 1)) := by
  simp only [T, pow_succ]
  ring

private theorem detached_gap_pos (β : Bias) (n : ℕ) :
    β.T 2 * β.T (n + 2) < β.T (n + 3) := by
  rw [← sub_pos, detached_gap_factorization]
  have h0 : 0 < 1 - β.p := by linarith [β.lt_one]
  have hne : 1 - β.p ≠ β.p := by intro h; apply β.biased; linarith
  have hprod : 0 < ((1 - β.p) - β.p) *
      ((1 - β.p)^(n + 1) - β.p^(n + 1)) := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr h)
        (sub_neg.mpr (pow_lt_pow_left₀ h h0.le (by omega)))
    · exact mul_pos (sub_pos.mpr h)
        (sub_pos.mpr (pow_lt_pow_left₀ h β.pos.le (by omega)))
  simpa only [mul_assoc] using mul_pos (mul_pos h0 β.pos) hprod

end Bias
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace FiniteSpinLaw

variable {ι : Type*} [Fintype ι]

def weight (β : Bias) (σ : ι → Bool) : ℝ := ∏ i, β.π (σ i)

def mass (β : Bias) (E : Set (ι → Bool)) : ℝ :=
  ∑ σ, if σ ∈ E then weight β σ else 0

private theorem weight_pos (β : Bias) (σ : ι → Bool) : 0 < weight β σ :=
  Finset.prod_pos fun _ _ => β.π_pos _

private theorem weight_sum (β : Bias) : ∑ σ : ι → Bool, weight β σ = 1 := by
  rw [show (∑ σ : ι → Bool, weight β σ) = ∏ _ : ι, ∑ s : Bool, β.π s from
    (Fintype.prod_sum (fun (_ : ι) (s : Bool) => β.π s)).symm]
  simp [Fintype.sum_bool, Bias.π]

private theorem mass_nonneg (β : Bias) (E : Set (ι → Bool)) : 0 ≤ mass β E := by
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · exact (weight_pos β σ).le
  · exact le_rfl

@[simp] private theorem mass_univ (β : Bias) : mass (ι := ι) β Set.univ = 1 := by
  simpa [mass] using weight_sum (ι := ι) β

@[simp] private theorem mass_empty (β : Bias) : mass (ι := ι) β ∅ = 0 := by simp [mass]

private theorem mass_union (β : Bias) {E F : Set (ι → Bool)} (h : Disjoint E F) :
    mass β (E ∪ F) = mass β E + mass β F := by
  rw [mass, mass, mass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  have hn : ¬(σ ∈ E ∧ σ ∈ F) := fun hh => Set.disjoint_left.mp h hh.1 hh.2
  by_cases he : σ ∈ E <;> by_cases hf : σ ∈ F <;> simp_all

private theorem mass_diff (β : Bias) {E F : Set (ι → Bool)} (h : F ⊆ E) :
    mass β (E \ F) = mass β E - mass β F := by
  have hu : E = (E \ F) ∪ F := by ext σ; simp only [Set.mem_union, Set.mem_diff]; tauto
  have hd : Disjoint (E \ F) F := Set.disjoint_sdiff_left
  have he := mass_union β hd
  rw [← hu] at he
  linarith

private theorem mass_mono (β : Bias) {E F : Set (ι → Bool)} (h : E ⊆ F) :
    mass β E ≤ mass β F := by
  have hn := mass_nonneg β (F \ E)
  rw [mass_diff β h] at hn
  linarith

private theorem mass_pos_iff (β : Bias) (E : Set (ι → Bool)) :
    0 < mass β E ↔ E.Nonempty := by
  constructor
  · intro hp
    by_contra hn
    have he : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he] at hp
  · rintro ⟨σ, hσ⟩
    have hs : mass β {σ} = weight β σ := by simp [mass]
    have hle : weight β σ ≤ mass β E := by
      rw [← hs]
      exact mass_mono β (Set.singleton_subset_iff.mpr hσ)
    exact (weight_pos β σ).trans_le hle

/-- A finite probability-one assertion holds at every configuration. -/
private theorem mass_one_iff (β : Bias) (E : Set (ι → Bool)) :
    mass β E = 1 ↔ E = Set.univ := by
  constructor
  · intro he
    have hdiff := mass_diff β (show E ⊆ Set.univ from Set.subset_univ E)
    rw [mass_univ, he, sub_self] at hdiff
    by_contra hn
    have hnon : (Set.univ \ E).Nonempty := by
      by_contra h
      have : Set.univ ⊆ E := by
        intro σ _
        by_contra hx
        exact h ⟨σ, trivial, hx⟩
      exact hn (Set.Subset.antisymm (Set.subset_univ E) this)
    have hp := (mass_pos_iff β _).2 hnon
    linarith
  · rintro rfl; exact mass_univ β

/-- Arbitrary coordinatewise constraints factor as a finite product. -/
private theorem mass_pi (β : Bias) (A : ι → Set Bool) :
    mass β {σ | ∀ i, σ i ∈ A i} =
      ∏ i, ∑ s : Bool, if s ∈ A i then β.π s else 0 := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simpa only [mass, weight, Set.mem_setOf_eq] using
    (Fintype.prod_ite_zero (p := fun i => σ i ∈ A i) (f := fun i => β.π (σ i))).symm

/-- Prescribing a finite set of coordinates leaves every other spin unrestricted. -/
private theorem prescribed_mass (β : Bias) (A : Finset ι) (v : ι → Bool) :
    mass β {σ | ∀ i ∈ A, σ i = v i} = ∏ i ∈ A, β.π (v i) := by
  have hs : {σ : ι → Bool | ∀ i ∈ A, σ i = v i} =
      {σ | ∀ i, σ i ∈ (if i ∈ A then {v i} else Set.univ : Set Bool)} := by
    ext σ
    constructor
    · intro h i
      by_cases hi : i ∈ A
      · simpa [hi] using h i hi
      · simp [hi]
    · intro h i hi; simpa [hi] using h i
  rw [hs, mass_pi]
  have hcoord (i : ι) :
      (∑ s : Bool, if s ∈ (if i ∈ A then {v i} else Set.univ : Set Bool)
        then β.π s else 0) = if i ∈ A then β.π (v i) else 1 := by
    by_cases hi : i ∈ A
    · simp [hi, Fintype.sum_bool]
    · simp [hi, Fintype.sum_bool, Bias.π]
  simp_rw [hcoord]
  exact Finset.prod_ite_mem_eq A (fun i => β.π (v i))

private theorem constant_mass (β : Bias) (A : Finset ι) (s : Bool) :
    mass β {σ | ∀ i ∈ A, σ i = s} = (β.π s)^A.card := by
  rw [prescribed_mass]
  simp

/-- Nonempty monochromatic blocks split into two disjoint constant-spin cylinders. -/
private theorem monochromatic_mass (β : Bias) (A : Finset ι) (ha : A.Nonempty) :
    mass β {σ | (∀ i ∈ A, σ i = false) ∨ (∀ i ∈ A, σ i = true)} = β.T A.card := by
  have hd : Disjoint {σ : ι → Bool | ∀ i ∈ A, σ i = false}
      {σ | ∀ i ∈ A, σ i = true} := by
    apply Set.disjoint_left.mpr
    intro σ h0 h1
    rcases ha with ⟨i, hi⟩
    have := (h0 i hi).symm.trans (h1 i hi)
    cases this
  change mass β ({σ | ∀ i ∈ A, σ i = false} ∪ {σ | ∀ i ∈ A, σ i = true}) = _
  rw [mass_union β hd, constant_mass, constant_mass]
  rfl

end FiniteSpinLaw
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace FiniteSpinLaw

variable {ι : Type*} [Fintype ι]

def restrict (A : Finset ι) (σ : ι → Bool) : A → Bool := fun i => σ i

private theorem restriction_fiber_mass (β : Bias) (A : Finset ι) (τ : A → Bool) :
    mass β {σ : ι → Bool | restrict A σ = τ} = weight β τ := by
  let v : ι → Bool := fun i => if h : i ∈ A then τ ⟨i, h⟩ else false
  have he : {σ : ι → Bool | restrict A σ = τ} = {σ | ∀ i ∈ A, σ i = v i} := by
    ext σ
    constructor
    · intro h i hi
      have hh := congrFun h ⟨i, hi⟩
      simpa [restrict, v, hi] using hh
    · intro h
      funext i
      simpa [restrict, v, i.property] using h i i.property
  rw [he, prescribed_mass]
  have hp : (∏ i ∈ A, β.π (v i)) = ∏ i : A, β.π (v i) :=
    (Finset.prod_coe_sort A (fun i => β.π (v i))).symm
  rw [hp]
  simp only [v, dif_pos (Subtype.property _), weight]

/-- Marginalization is proved for every event, not just constant-spin cylinders. -/
private theorem restriction_mass (β : Bias) (A : Finset ι) (E : Set (A → Bool)) :
    mass β {σ : ι → Bool | restrict A σ ∈ E} = mass β E := by
  have hsingle (σ : ι → Bool) :
      (if restrict A σ ∈ E then weight β σ else 0) =
      ∑ τ : A → Bool, if τ ∈ E then
        (if restrict A σ = τ then weight β σ else 0) else 0 := by
    rw [Finset.sum_eq_single (restrict A σ)]
    · by_cases he : restrict A σ ∈ E <;> simp [he]
    · intro τ _ hτ
      have hn : restrict A σ ≠ τ := Ne.symm hτ
      simp [hn]
    · simp
  unfold mass
  simp only [Set.mem_setOf_eq]
  simp_rw [hsingle]
  rw [Finset.sum_comm]
  refine Finset.sum_congr (by ext; simp) ?_
  intro τ _
  by_cases he : τ ∈ E
  · simp only [he, ↓reduceIte]
    have hf := restriction_fiber_mass β A τ
    unfold mass at hf
    calc
      _ = _ := Finset.sum_congr (by ext; simp) (by intro σ _; simp)
      _ = _ := hf
  · simp [he]

/-- An arbitrary coordinate partition has independent product marginals. -/
private theorem partition_mass (β : Bias) (p : ι → Prop) [DecidablePred p]
    (E : Set ({i // p i} → Bool)) (F : Set ({i // ¬p i} → Bool)) :
    mass β {σ : ι → Bool | (fun i : {i // p i} => σ i) ∈ E ∧
      (fun i : {i // ¬p i} => σ i) ∈ F} = mass β E * mass β F := by
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => Bool)
  have hw (σ : ι → Bool) : weight β σ = weight β (e σ).1 * weight β (e σ).2 := by
    exact (Fintype.prod_subtype_mul_prod_subtype p (fun i => β.π (σ i))).symm
  unfold mass
  simp only [Set.mem_setOf_eq]
  rw [show (∑ σ : ι → Bool, if
      (fun i : {i // p i} => σ i) ∈ E ∧ (fun i : {i // ¬p i} => σ i) ∈ F
      then weight β σ else 0) =
      ∑ z : ({i // p i} → Bool) × ({i // ¬p i} → Bool),
        if z.1 ∈ E ∧ z.2 ∈ F then weight β z.1 * weight β z.2 else 0 from
    Fintype.sum_equiv e _ _ (fun σ => by rw [hw]; rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr (by ext; simp) ?_
  intro σ _
  refine Finset.sum_congr (by ext; simp) ?_
  intro τ _
  by_cases he : σ ∈ E <;> by_cases hf : τ ∈ F <;> simp [he, hf]

/-- Events depending on disjoint coordinate sets are independent. -/
private theorem disjoint_event_mass (β : Bias) (A B : Finset ι) (hd : Disjoint A B)
    (E F : Set (ι → Bool))
    (hE : ∀ σ τ : ι → Bool, (∀ i ∈ A, σ i = τ i) → (σ ∈ E ↔ τ ∈ E))
    (hF : ∀ σ τ : ι → Bool, (∀ i ∈ B, σ i = τ i) → (σ ∈ F ↔ τ ∈ F)) :
    mass β (E ∩ F) = mass β E * mass β F := by
  let E' : Set ({i // i ∈ A} → Bool) :=
    {σ | (fun i => if hi : i ∈ A then σ ⟨i, hi⟩ else false) ∈ E}
  let F' : Set ({i // i ∉ A} → Bool) :=
    {σ | (fun i => if hi : i ∉ A then σ ⟨i, hi⟩ else false) ∈ F}
  have he (σ : ι → Bool) : σ ∈ E ↔ (fun i : {i // i ∈ A} => σ i) ∈ E' := by
    apply hE
    intro i hi
    simp [hi]
  have hf (σ : ι → Bool) : σ ∈ F ↔ (fun i : {i // i ∉ A} => σ i) ∈ F' := by
    apply hF
    intro i hi
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    simp [hn]
  have heq : E ∩ F = {σ | (fun i : {i // i ∈ A} => σ i) ∈ E' ∧
      (fun i : {i // i ∉ A} => σ i) ∈ F'} := by ext σ; exact and_congr (he σ) (hf σ)
  have heqE : E = {σ | (fun i : {i // i ∈ A} => σ i) ∈ E'} := by ext σ; exact he σ
  have heqF : F = {σ | (fun i : {i // i ∉ A} => σ i) ∈ F'} := by ext σ; exact hf σ
  rw [heq, partition_mass]
  have hmE : mass β {σ : ι → Bool | (fun i : {i // i ∈ A} => σ i) ∈ E'} =
      mass β E' := by
    convert restriction_mass β A E' using 1 <;> congr 1 <;> exact Subsingleton.elim _ _
  have hmF := partition_mass β (fun i : ι => i ∈ A) Set.univ F'
  simp only [Set.mem_univ, and_true, true_and, mass_univ, mul_one, one_mul] at hmE hmF
  rw [heqE, heqF, hmE, hmF]
  congr!

end FiniteSpinLaw
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- Left endpoints and vertices of a path containing n integer edges. -/
def pathEdges (L : ℤ) (n : ℕ) : Finset ℤ := Finset.Icc L (L + n - 1)

def pathVertices (L : ℤ) (n : ℕ) : Finset ℤ := Finset.Icc L (L + n)

/-- The three cases include arbitrary negative edge indices. -/
private theorem integer_edge_trichotomy (L e : ℤ) {n : ℕ} (hn : 1 ≤ n) :
    e ∈ pathEdges L n ∨ (e = L - 1 ∨ e = L + n) ∨
      Disjoint ({e, e + 1} : Finset ℤ) (pathVertices L n) := by
  by_cases hi : e ∈ pathEdges L n
  · exact Or.inl hi
  by_cases hl : e = L - 1
  · exact Or.inr (Or.inl (Or.inl hl))
  by_cases hr : e = L + n
  · exact Or.inr (Or.inl (Or.inr hr))
  right; right
  apply Finset.disjoint_left.mpr
  intro v hv hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  simp only [pathVertices, Finset.mem_Icc] at hp
  simp only [pathEdges, Finset.mem_Icc, not_and_or, not_le] at hi
  rcases hv with rfl | rfl <;> omega

private theorem extend_left (L : ℤ) (n : ℕ) :
    insert (L - 1) (pathEdges L n) = pathEdges (L - 1) (n + 1) := by
  ext e
  simp only [Finset.mem_insert, pathEdges, Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
  omega

private theorem extend_right (L : ℤ) (n : ℕ) :
    insert (L + n) (pathEdges L n) = pathEdges L (n + 1) := by
  ext e
  simp only [Finset.mem_insert, pathEdges, Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
  omega

theorem vertices_card (L : ℤ) (n : ℕ) : (pathVertices L n).card = n + 1 := by
  simp only [pathVertices, Int.card_Icc]
  omega

/-- Adjacent equalities on an integer interval force a single common spin value. -/
private theorem path_constant_iff (L : ℤ) (n : ℕ) (S : Spins) :
    (∀ e ∈ pathEdges L n, S e = S (e + 1)) ↔
      ∀ v ∈ pathVertices L n, S v = S L := by
  constructor
  · intro h v hv
    have hv' : L ≤ v ∧ v ≤ L + n := by simpa [pathVertices] using hv
    have key : ∀ m : ℕ, m ≤ n → S (L + m) = S L := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
        have hm' : m ≤ n := by omega
        have he : L + m ∈ pathEdges L n := by
          simp only [pathEdges, Finset.mem_Icc]
          constructor <;> omega
        have hh := h _ he
        have hi := ih hm'
        have hc : L + (m + 1 : ℕ) = L + m + 1 := by push_cast; ring
        rw [hc, ← hh, hi]
    have hc : L + (v - L).toNat = v := by omega
    have hm : (v - L).toNat ≤ n := by omega
    have hp := key (v - L).toNat hm
    rw [hc] at hp
    exact hp
  · intro h e he
    have he' : L ≤ e ∧ e ≤ L + n - 1 := by simpa [pathEdges] using he
    have h0 : e ∈ pathVertices L n := by simp only [pathVertices, Finset.mem_Icc]; omega
    have h1 : e + 1 ∈ pathVertices L n := by simp only [pathVertices, Finset.mem_Icc]; omega
    exact (h e h0).trans (h _ h1).symm

/-- A target contained in a zero path specifies the spin of every vertex. -/
private theorem path_target_iff (L q : ℤ) (n : ℕ) (S : Spins) (s : Bool)
    (hq : q ∈ pathVertices L n) :
    ((∀ e ∈ pathEdges L n, S e = S (e + 1)) ∧ S q = s) ↔
      ∀ v ∈ pathVertices L n, S v = s := by
  constructor
  · rintro ⟨h, hs⟩
    have hc := (path_constant_iff L n S).1 h
    intro v hv
    exact (hc v hv).trans ((hc q hq).symm.trans hs)
  · intro h
    refine ⟨(path_constant_iff L n S).2 ?_, h q hq⟩
    intro v hv
    have hl : L ∈ pathVertices L n := by simp [pathVertices]
    exact (h v hv).trans (h L hl).symm

/-- A target outside a consecutive k-edge path forces a remote original-clock address. -/
theorem detached_path_remote (j : Bool) {k : ℕ} (hk : 1 ≤ k) (L : ℤ)
    (hq : j.toInt ∉ pathVertices L k) :
    ∃ e ∈ pathEdges L k, (2 * k + 1 : ℤ) ≤ |2 * e + (!j).toInt - j.toInt| := by
  have hsep : j.toInt < L ∨ L + k < j.toInt := by
    simp only [pathVertices, Finset.mem_Icc, not_and_or, not_le] at hq
    exact hq
  rcases hsep with hr | hl
  · refine ⟨L + k - 1, ?_, ?_⟩
    · simp only [pathEdges, Finset.mem_Icc]; constructor <;> omega
    · have hle := le_abs_self (2 * (L + k - 1) + (!j).toInt - j.toInt)
      cases j <;> simp only [Bool.not_false, Bool.not_true, Bool.toInt_false,
        Bool.toInt_true] at * <;> omega
  · refine ⟨L, ?_, ?_⟩
    · simp only [pathEdges, Finset.mem_Icc]; constructor <;> omega
    · have hle := neg_le_abs (2 * L + (!j).toInt - j.toInt)
      cases j <;> simp only [Bool.not_false, Bool.not_true, Bool.toInt_false,
        Bool.toInt_true] at * <;> omega

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace SpinWindow

/-- The default outside a finite window is immaterial to events supported inside it. -/
def extend (V : Finset ℤ) (σ : V → Bool) : Spins :=
  fun i => if hi : i ∈ V then σ ⟨i, hi⟩ else false

@[simp] private theorem extend_apply (V : Finset ℤ) (σ : V → Bool) (i : ℤ) (hi : i ∈ V) :
    extend V σ i = σ ⟨i, hi⟩ := dif_pos hi

def prob (β : Bias) (V : Finset ℤ) (E : Set Spins) : ℝ :=
  FiniteSpinLaw.mass β {σ | extend V σ ∈ E}

@[simp] theorem prob_univ (β : Bias) (V : Finset ℤ) : prob β V Set.univ = 1 :=
  FiniteSpinLaw.mass_univ β

@[simp] private theorem prob_empty (β : Bias) (V : Finset ℤ) : prob β V ∅ = 0 :=
  FiniteSpinLaw.mass_empty β

theorem prob_union (β : Bias) (V : Finset ℤ) {E F : Set Spins} (h : Disjoint E F) :
    prob β V (E ∪ F) = prob β V E + prob β V F := by
  apply FiniteSpinLaw.mass_union
  exact h.preimage _

theorem prob_diff (β : Bias) (V : Finset ℤ) {E F : Set Spins} (h : F ⊆ E) :
    prob β V (E \ F) = prob β V E - prob β V F :=
  FiniteSpinLaw.mass_diff β (fun _ hh => h hh)

theorem prob_pos_iff (β : Bias) (V : Finset ℤ) (E : Set Spins) :
    0 < prob β V E ↔ ∃ σ : V → Bool, extend V σ ∈ E :=
  FiniteSpinLaw.mass_pos_iff β _

/-- Every actual finite configuration is retained by positive product weights. -/
theorem prob_one_iff (β : Bias) (V : Finset ℤ) (E : Set Spins) :
    prob β V E = 1 ↔ ∀ σ : V → Bool, extend V σ ∈ E := by
  rw [prob, FiniteSpinLaw.mass_one_iff]
  simp [Set.eq_univ_iff_forall]

def constant (A : Finset ℤ) (s : Bool) : Set Spins := {S | ∀ i ∈ A, S i = s}

def monoBlock (A : Finset ℤ) : Set Spins := constant A false ∪ constant A true

def zeroEdges (E : Finset ℤ) : Set Spins := {S | ∀ e ∈ E, S e = S (e + 1)}

theorem constant_prob (β : Bias) (V A : Finset ℤ) (hA : A ⊆ V) (s : Bool) :
    prob β V (constant A s) = (β.π s)^A.card := by
  have he : {σ : V → Bool | extend V σ ∈ constant A s} =
      {σ | ∀ i ∈ A.subtype (· ∈ V), σ i = s} := by
    ext σ
    constructor
    · intro h i hi
      have hi' : i.val ∈ A := Finset.mem_subtype.mp hi
      simpa only [extend_apply V σ i.val i.property] using h i.val hi'
    · intro h i hi
      have hiV := hA hi
      have hh := h ⟨i, hiV⟩ (Finset.mem_subtype.mpr hi)
      simpa only [extend_apply V σ i hiV] using hh
  unfold prob
  rw [he, FiniteSpinLaw.constant_mass, Finset.card_subtype,
    Finset.filter_eq_self.mpr hA]

private theorem constant_disjoint (A : Finset ℤ) (hA : A.Nonempty) :
    Disjoint (constant A false) (constant A true) := by
  apply Set.disjoint_left.mpr
  intro S h0 h1
  obtain ⟨i, hi⟩ := hA
  have := (h0 i hi).symm.trans (h1 i hi)
  cases this

private theorem monoBlock_prob (β : Bias) (V A : Finset ℤ) (hA : A ⊆ V) (hne : A.Nonempty) :
    prob β V (monoBlock A) = β.T A.card := by
  let C : Finset V := A.subtype (· ∈ V)
  have hc : C.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨⟨i, hA hi⟩, Finset.mem_subtype.mpr hi⟩
  have hconst (u : Bool) (σ : V → Bool) :
      (∀ i ∈ A, extend V σ i = u) ↔ (∀ i ∈ C, σ i = u) := by
    constructor
    · intro h i hi
      simpa only [extend_apply V σ i.val i.property] using h i.val (Finset.mem_subtype.mp hi)
    · intro h i hi
      simpa only [extend_apply V σ i (hA hi)] using h ⟨i, hA hi⟩ (Finset.mem_subtype.mpr hi)
  have he : {σ : V → Bool | extend V σ ∈ monoBlock A} =
      {σ | (∀ i ∈ C, σ i = false) ∨ (∀ i ∈ C, σ i = true)} := by
    ext σ
    exact or_congr (hconst false σ) (hconst true σ)
  change FiniteSpinLaw.mass β {σ : V → Bool | extend V σ ∈ monoBlock A} = _
  rw [he, FiniteSpinLaw.monochromatic_mass β C hc]
  simp [C, Finset.card_subtype, Finset.filter_eq_self.mpr hA]

theorem zero_path_eq_block (L : ℤ) (n : ℕ) :
    zeroEdges (pathEdges L n) = monoBlock (pathVertices L n) := by
  ext S
  change (∀ e ∈ pathEdges L n, S e = S (e + 1)) ↔
    (∀ v ∈ pathVertices L n, S v = false) ∨ (∀ v ∈ pathVertices L n, S v = true)
  rw [path_constant_iff]
  constructor
  · intro h
    cases hs : S L with
    | false => exact Or.inl (fun v hv => (h v hv).trans hs)
    | true => exact Or.inr (fun v hv => (h v hv).trans hs)
  · intro h v hv
    have hl : L ∈ pathVertices L n := by simp [pathVertices]
    rcases h with h | h <;> exact (h v hv).trans (h L hl).symm

private theorem zero_path_prob (β : Bias) (V : Finset ℤ) (L : ℤ) (n : ℕ)
    (hV : pathVertices L n ⊆ V) :
    prob β V (zeroEdges (pathEdges L n)) = β.T (n + 1) := by
  rw [zero_path_eq_block, monoBlock_prob β V _ hV, vertices_card]
  exact ⟨L, by simp [pathVertices]⟩

/-- The target section becomes a constant-spin block if the target lies on the path. -/
private theorem target_collision_prob (β : Bias) (V : Finset ℤ) (L q : ℤ) (n : ℕ)
    (hV : pathVertices L n ⊆ V) (hq : q ∈ pathVertices L n) (s : Bool) :
    prob β V (zeroEdges (pathEdges L n) ∩ {S | S q = s}) = (β.π s)^(n + 1) := by
  have he : zeroEdges (pathEdges L n) ∩ {S | S q = s} = constant (pathVertices L n) s := by
    ext S
    exact path_target_iff L q n S s hq
  rw [he, constant_prob β V _ hV, vertices_card]

private theorem target_collision_conditional (β : Bias) (V : Finset ℤ) (L q : ℤ) (n : ℕ)
    (hV : pathVertices L n ⊆ V) (hq : q ∈ pathVertices L n) (s : Bool) :
    prob β V (zeroEdges (pathEdges L n) ∩ {S | S q = s}) / β.π s = (β.π s)^n := by
  rw [target_collision_prob β V L q n hV hq s, pow_succ,
    mul_div_cancel_right₀ _ (ne_of_gt (β.π_pos s))]

end SpinWindow
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace SpinWindow

def SupportedOn (V : Finset ℤ) (E : Set Spins) : Prop :=
  ∀ S R : Spins, (∀ i ∈ V, S i = R i) → (S ∈ E ↔ R ∈ E)

/-- Two spin events on disjoint finite coordinates are independent in any containing window. -/
private theorem prob_independent (β : Bias) (V A B : Finset ℤ) (hA : A ⊆ V) (hB : B ⊆ V)
    (hd : Disjoint A B) (E F : Set Spins) (hE : SupportedOn A E) (hF : SupportedOn B F) :
    prob β V (E ∩ F) = prob β V E * prob β V F := by
  let A' : Finset V := A.subtype (· ∈ V)
  let B' : Finset V := B.subtype (· ∈ V)
  have hd' : Disjoint A' B' := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact Finset.disjoint_left.mp hd (Finset.mem_subtype.mp hiA) (Finset.mem_subtype.mp hiB)
  apply FiniteSpinLaw.disjoint_event_mass β A' B' hd'
  · intro σ τ h
    apply hE
    intro i hi
    have hh := h ⟨i, hA hi⟩ (Finset.mem_subtype.mpr hi)
    simpa only [extend_apply V σ i (hA hi), extend_apply V τ i (hA hi)] using hh
  · intro σ τ h
    apply hF
    intro i hi
    have hh := h ⟨i, hB hi⟩ (Finset.mem_subtype.mpr hi)
    simpa only [extend_apply V σ i (hB hi), extend_apply V τ i (hB hi)] using hh

end SpinWindow
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

namespace FiniteSpinLaw

variable {ι : Type*} [Fintype ι]

private theorem two_constant_mass (β : Bias) (A B : Finset ι) (hd : Disjoint A B) (s t : Bool) :
    mass β ({σ | ∀ i ∈ A, σ i = s} ∩ {σ | ∀ i ∈ B, σ i = t}) =
      (β.π s)^A.card * (β.π t)^B.card := by
  have hs (C : Finset ι) (u : Bool) (σ τ : ι → Bool)
      (h : ∀ i ∈ C, σ i = τ i) :
      (∀ i ∈ C, σ i = u) ↔ (∀ i ∈ C, τ i = u) := by
    constructor <;> intro hc i hi
    · rw [← h i hi]; exact hc i hi
    · rw [h i hi]; exact hc i hi
  calc
    _ = mass β {σ : ι → Bool | ∀ i ∈ A, σ i = s} *
        mass β {σ : ι → Bool | ∀ i ∈ B, σ i = t} :=
      disjoint_event_mass β A B hd {σ | ∀ i ∈ A, σ i = s}
        {σ | ∀ i ∈ B, σ i = t} (hs A s) (hs B t)
    _ = _ := by rw [constant_mass, constant_mass]

end FiniteSpinLaw

namespace SpinWindow

private theorem two_constant_prob (β : Bias) (V A B : Finset ℤ)
    (hA : A ⊆ V) (hB : B ⊆ V) (hd : Disjoint A B) (s t : Bool) :
    prob β V (constant A s ∩ constant B t) =
      (β.π s)^A.card * (β.π t)^B.card := by
  have he (C : Finset ℤ) (hC : C ⊆ V) (u : Bool) :
      {σ : V → Bool | extend V σ ∈ constant C u} =
        {σ | ∀ i ∈ C.subtype (· ∈ V), σ i = u} := by
    ext σ
    constructor
    · intro h i hi
      have hi' : i.val ∈ C := Finset.mem_subtype.mp hi
      simpa only [extend_apply V σ i.val i.property] using h i.val hi'
    · intro h i hi
      have hiV := hC hi
      simpa only [extend_apply V σ i hiV] using
        h ⟨i, hiV⟩ (Finset.mem_subtype.mpr hi)
  have hd' : Disjoint (A.subtype (· ∈ V)) (B.subtype (· ∈ V)) := by
    apply Finset.disjoint_left.mpr
    intro i ha hb
    exact Finset.disjoint_left.mp hd (Finset.mem_subtype.mp ha) (Finset.mem_subtype.mp hb)
  change FiniteSpinLaw.mass β
    ({σ | extend V σ ∈ constant A s} ∩ {σ | extend V σ ∈ constant B t}) = _
  rw [he A hA s, he B hB t, FiniteSpinLaw.two_constant_mass β _ _ hd',
    Finset.card_subtype, Finset.card_subtype,
    Finset.filter_eq_self.mpr hA, Finset.filter_eq_self.mpr hB]

theorem block_constant_prob (β : Bias) (V A B : Finset ℤ)
    (hA : A ⊆ V) (hB : B ⊆ V) (hd : Disjoint A B) (hne : A.Nonempty) (s : Bool) :
    prob β V (monoBlock A ∩ constant B s) = β.T A.card * (β.π s)^B.card := by
  have he : monoBlock A ∩ constant B s =
      (constant A false ∩ constant B s) ∪ (constant A true ∩ constant B s) := by
    ext S; simp only [monoBlock, Set.mem_inter_iff, Set.mem_union]; tauto
  have hdis : Disjoint (constant A false ∩ constant B s)
      (constant A true ∩ constant B s) := by
    apply Set.disjoint_left.mpr
    intro S h0 h1
    exact Set.disjoint_left.mp (constant_disjoint A hne) h0.1 h1.1
  rw [he, prob_union β V hdis, two_constant_prob β V A B hA hB hd,
    two_constant_prob β V A B hA hB hd]
  simp only [Bias.T, Bias.π, Bool.false_eq_true, ↓reduceIte]
  ring

private theorem two_blocks_prob (β : Bias) (V A B : Finset ℤ)
    (hA : A ⊆ V) (hB : B ⊆ V) (hd : Disjoint A B)
    (hneA : A.Nonempty) (hneB : B.Nonempty) :
    prob β V (monoBlock A ∩ monoBlock B) = β.T A.card * β.T B.card := by
  have hs (C : Finset ℤ) : SupportedOn C (monoBlock C) := by
    intro S R h
    have hc (u : Bool) : S ∈ constant C u ↔ R ∈ constant C u := by
      constructor <;> intro hC i hi
      · rw [← h i hi]; exact hC i hi
      · rw [h i hi]; exact hC i hi
    exact or_congr (hc false) (hc true)
  rw [prob_independent β V A B hA hB hd _ _ (hs A) (hs B),
    monoBlock_prob β V A hA hneA, monoBlock_prob β V B hB hneB]

private theorem zero_insert (E : Finset ℤ) (e : ℤ) :
    zeroEdges (insert e E) = zeroEdges E ∩ {S | S e = S (e + 1)} := by
  ext S; simp only [zeroEdges, Set.mem_inter_iff, Set.mem_setOf_eq,
    Finset.forall_mem_insert]; tauto

private theorem pair_zero_eq_block (e : ℤ) :
    {S : Spins | S e = S (e + 1)} = monoBlock {e, e + 1} := by
  ext S
  simp only [monoBlock, constant, Set.mem_union, Set.mem_setOf_eq, Finset.forall_mem_insert,
    Finset.mem_singleton, forall_eq]
  cases h0 : S e <;> cases h1 : S (e + 1) <;> simp [h0, h1]

private theorem repeated_edge_prob (β : Bias) (V : Finset ℤ) (L e : ℤ) (n : ℕ)
    (hV : pathVertices L n ⊆ V) (he : e ∈ pathEdges L n) :
    prob β V (zeroEdges (insert e (pathEdges L n))) = β.T (n + 1) := by
  rw [Finset.insert_eq_of_mem he, zero_path_prob β V L n hV]

private theorem separated_edge_prob (β : Bias) (V : Finset ℤ) (L e : ℤ) (n : ℕ)
    (hV : pathVertices L n ⊆ V) (heV : {e, e + 1} ⊆ V)
    (hd : Disjoint ({e, e + 1} : Finset ℤ) (pathVertices L n)) :
    prob β V (zeroEdges (insert e (pathEdges L n))) = β.T 2 * β.T (n + 1) := by
  rw [zero_insert, zero_path_eq_block, pair_zero_eq_block,
    two_blocks_prob β V _ _ hV heV hd.symm
      ⟨L, by simp [pathVertices]⟩ ⟨e, by simp⟩, vertices_card]
  have hc : ({e, e + 1} : Finset ℤ).card = 2 := by simp
  rw [hc, mul_comm]

end SpinWindow
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical



end

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace SpinWindow

/-- An integer path's vertices are precisely incident to its edges when it is nonempty. -/
theorem path_vertices_supported (V : Finset ℤ) (L : ℤ) {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ e ∈ pathEdges L n, e ∈ V ∧ e + 1 ∈ V) : pathVertices L n ⊆ V := by
  intro v hv
  have hv' : L ≤ v ∧ v ≤ L + n := by simpa [pathVertices] using hv
  by_cases he : v ≤ L + n - 1
  · exact (h v (by simp [pathEdges]; omega)).1
  · have hm : v - 1 ∈ pathEdges L n := by simp [pathEdges]; omega
    have hp := (h (v - 1) hm).2
    simpa using hp

/-- The required new mass rules out repetition and a vertex-disjoint edge. -/
private theorem mass_forces_extension (β : Bias) (V : Finset ℤ) (L e : ℤ) {n : ℕ}
    (hn : 1 ≤ n) (hV : pathVertices L n ⊆ V) (heV : {e, e + 1} ⊆ V)
    (hm : prob β V (zeroEdges (insert e (pathEdges L n))) = β.T (n + 2)) :
    e = L - 1 ∨ e = L + n := by
  rcases integer_edge_trichotomy L e hn with hrep | hext | hsep
  · have hsame := repeated_edge_prob β V L e n hV hrep
    have hlt := β.T_succ_lt (n + 1)
    rw [hm] at hsame
    linarith
  · exact hext
  · have hdis := separated_edge_prob β V L e n hV heV hsep
    obtain ⟨m, hm'⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    subst n
    have hlt := β.detached_gap_pos m
    rw [hm] at hdis
    have heq : β.T (m + 3) = β.T 2 * β.T (m + 2) := by
      simpa only [Nat.add_assoc] using hdis
    linarith

/-- A finite list is supported together with both endpoints of each queried edge. -/
def SupportsEdges (V : Finset ℤ) (es : List ℤ) : Prop :=
  ∀ e ∈ es, e ∈ V ∧ e + 1 ∈ V

def PrefixMasses (β : Bias) (V : Finset ℤ) (es : List ℤ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ es.length →
    prob β V (zeroEdges (es.take r).toFinset) = β.T (r + 1)

/-- Query order is arbitrary: each prefix may extend either endpoint. -/
theorem prefixes_force_consecutive (β : Bias) (V : Finset ℤ) (es : List ℤ)
    (hV : SupportsEdges V es) (hm : PrefixMasses β V es) (hk : 1 ≤ es.length) :
    es.Nodup ∧ ∃ L : ℤ, es.toFinset = pathEdges L es.length := by
  revert hV hm hk
  induction es using List.reverseRecOn with
  | nil => intro _ _ h; simp at h
  | append_singleton es e ih =>
    intro hV hm hk
    by_cases hempty : es = []
    · subst es
      refine ⟨by simp, e, ?_⟩
      simp [pathEdges]
    have hlen : 1 ≤ es.length := List.length_pos_iff.mpr hempty
    have holdV : SupportsEdges V es := fun a ha => hV a (by simp [ha])
    have holdm : PrefixMasses β V es := by
      intro r hr hrk
      have hp := hm r hr (by simp; omega)
      simpa only [List.take_append_of_le_length hrk] using hp
    obtain ⟨hnod, L, hL⟩ := ih holdV holdm hlen
    have hvpath : pathVertices L es.length ⊆ V :=
      path_vertices_supported V L hlen (fun a ha => holdV a (by simpa [← hL] using ha))
    have hev : {e, e + 1} ⊆ V := by
      have hv := hV e (by simp)
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hv.1
      · exact hv.2
    have hnew : prob β V (zeroEdges (insert e (pathEdges L es.length))) =
        β.T (es.length + 2) := by
      have hp := hm (es ++ [e]).length (by simp) le_rfl
      rw [List.take_length] at hp
      simpa [hL, Nat.add_assoc] using hp
    have hext := mass_forces_extension β V L e hlen hvpath hev hnew
    have hnot : e ∉ es := by
      intro he
      have hmemb : e ∈ pathEdges L es.length := by
        rw [← hL]
        exact List.mem_toFinset.mpr he
      simp only [pathEdges, Finset.mem_Icc] at hmemb
      rcases hext with h | h <;> omega
    refine ⟨by simpa using List.Nodup.concat hnot hnod, ?_⟩
    rcases hext with rfl | rfl
    · refine ⟨L - 1, ?_⟩
      simpa [hL] using extend_left L es.length
    · refine ⟨L, ?_⟩
      simpa [hL] using extend_right L es.length

/-- Both actual target-spin sections exclude a target vertex on the recovered path. -/
private theorem joint_masses_force_target_separation (β : Bias) (V : Finset ℤ)
    (es : List ℤ) (q L : ℤ) (hk : 1 ≤ es.length)
    (hV : SupportsEdges V es) (hL : es.toFinset = pathEdges L es.length)
    (htarget : ∀ s : Bool,
      prob β V (zeroEdges es.toFinset ∩ {S | S q = s}) = β.π s * β.T (es.length + 1)) :
    q ∉ pathVertices L es.length := by
  intro hq
  have hvpath : pathVertices L es.length ⊆ V :=
    path_vertices_supported V L hk (fun a ha => hV a (by simpa [← hL] using ha))
  have hp (s : Bool) : (β.π s)^es.length = β.T (es.length + 1) := by
    have hc := target_collision_conditional β V L q es.length hvpath hq s
    rw [← hL, htarget s, mul_comm (β.π s) (β.T (es.length + 1)),
      mul_div_cancel_right₀ _ (ne_of_gt (β.π_pos s))] at hc
    exact hc.symm
  have hne := β.unequal_powers hk
  apply hne
  exact (hp false).trans (hp true).symm

/-- Prefix and target masses together recover injective consecutive edges detached from q. -/
theorem finite_path_geometry (β : Bias) (V : Finset ℤ) (es : List ℤ) (q : ℤ)
    (hk : 1 ≤ es.length) (hV : SupportsEdges V es) (hm : PrefixMasses β V es)
    (htarget : ∀ s : Bool,
      prob β V (zeroEdges es.toFinset ∩ {S | S q = s}) = β.π s * β.T (es.length + 1)) :
    es.Nodup ∧ ∃ L : ℤ, es.toFinset = pathEdges L es.length ∧
      q ∉ pathVertices L es.length := by
  obtain ⟨hnod, L, hL⟩ := prefixes_force_consecutive β V es hV hm hk
  exact ⟨hnod, L, hL,
    joint_masses_force_target_separation β V es q L hk hV hL htarget⟩

end SpinWindow
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end
