/- GID: D5/S1/Words/Complexity/LacunaryBinomialMarkers
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/LacunaryBinomialMarkers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binomial counts and word-factor reconstruction for lacunary marked hierarchies. -/

/-
admission_basis: escape-witness
proof_shape: content (`marker_profile_two_injective`, `marker_strict_one_two`); supporting
lemmas are consumed on those live proof paths.
escape_witness: `marker_factor_eq_of_counts`, the lacunary block reconstruction used by
`marker_profile_two_injective`.
Direct frozen dependencies: extracted from the scoped Lean report.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23567.
-/

import Batteries.Tactic.OpenPrivate
import Batteries.Data.List.Lemmas
import D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore
import D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall
import D5.S1.Words.Complexity.MorseHedlund
import D5.S1.Words.Complexity.VivionBinomialConverseFails
import D5.S1.Words.GoldenBalance
import D5.S1.Words.GoldenFactorComplexity
import D5.S1.Words.GoldenRecovery.GoldenFactorSecondOrderBinomialRigidity
import D5.S1.Words.GoldenWord
import D5.S1.Words.Palindromes.GoldenPalindromicFactorComplexity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1024

namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
variable {A : Type*} [Fintype A] [DecidableEq A]
theorem profile_eq_iff {n k : Nat} {u v : Fin n → A} :
    binomialProfile k u = binomialProfile k v ↔
      ∀ pattern : List A, pattern.length ≤ k →
        scatteredCount pattern (List.ofFn u) =
          scatteredCount pattern (List.ofFn v) := by
  constructor
  · intro h pattern hp
    have he := congrFun (congrFun h (⟨pattern.length, by omega⟩ : Fin (k + 1)))
      pattern.get
    simpa only [binomialProfile, List.ofFn_get] using he
  · intro h
    funext length pattern
    exact h (List.ofFn pattern) (by simpa using Nat.le_of_lt_succ length.isLt)
theorem profile_eq_mono {n j k : Nat} (hjk : j ≤ k) {u v : Fin n → A}
    (h : binomialProfile k u = binomialProfile k v) :
    binomialProfile j u = binomialProfile j v := by
  apply profile_eq_iff.mpr
  intro pattern hp
  exact profile_eq_iff.mp h pattern (hp.trans hjk)
private def restrictProfile {j k : Nat} (hjk : j ≤ k)
    (p : (m : Fin (k + 1)) → (Fin m.val → A) → Nat) :
    (m : Fin (j + 1)) → (Fin m.val → A) → Nat :=
  fun m pattern => p ⟨m.val, by omega⟩ pattern
private theorem complexity_mono (word : Nat → A) {j k : Nat} (hjk : j ≤ k) (n : Nat) :
    binomialComplexity word j n ≤ binomialComplexity word k n := by
  classical
  have heq : binomialProfile (A := A) (n := n) j =
      restrictProfile hjk ∘ binomialProfile k := rfl
  unfold binomialComplexity
  rw [heq, ← Finset.image_image]
  exact Finset.card_image_le
theorem complexity_eq_factor_iff (word : Nat → A) (k n : Nat) :
    binomialComplexity word k n = (wordFactorSet word n).card ↔
      Set.InjOn (binomialProfile k) (wordFactorSet word n : Set (Fin n → A)) := by
  classical
  exact Finset.card_image_iff
theorem complexity_lt_of_split (word : Nat → A) {j k n : Nat} (hjk : j ≤ k)
    {u v : Fin n → A} (hu : u ∈ wordFactorSet word n)
    (hv : v ∈ wordFactorSet word n)
    (hlow : binomialProfile j u = binomialProfile j v)
    (hhigh : binomialProfile k u ≠ binomialProfile k v) :
    binomialComplexity word j n < binomialComplexity word k n := by
  classical
  apply lt_of_le_of_ne (complexity_mono word hjk n)
  intro hcard
  have hrestr :
      Set.InjOn (restrictProfile (A := A) hjk)
        ((wordFactorSet word n).image (binomialProfile k) :
          Set ((m : Fin (k + 1)) → (Fin m.val → A) → Nat)) := by
    apply Finset.card_image_iff.mp
    rw [Finset.image_image]
    exact hcard
  apply hhigh
  apply hrestr
  · exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  · exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  · exact hlow
end D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
private theorem map_sublistsLen (g : A → B) (source : List A) (m : Nat) :
    (source.map g).sublistsLen m = (source.sublistsLen m).map (List.map g) := by
  induction source generalizing m with
  | nil => cases m <;> simp
  | cons a source ih =>
      cases m with
      | zero => simp
      | succ m =>
          simp only [List.map_cons, List.sublistsLen_succ_cons, ih,
            List.map_append, List.map_map, Function.comp_def]
theorem profile_eq_map (g : A → B) {n k : Nat} {u v : Fin n → A}
    (h : binomialProfile k u = binomialProfile k v) :
    binomialProfile k (g ∘ u) = binomialProfile k (g ∘ v) := by
  apply profile_eq_iff.mpr
  intro pattern hp
  have hdeck : exactKDeck pattern.length (List.ofFn u) =
      exactKDeck pattern.length (List.ofFn v) := by
    funext q
    have hdec : (fun a b : A => Classical.propDecidable (a = b)) =
        (inferInstance : DecidableEq A) := Subsingleton.elim _ _
    unfold exactKDeck
    rw [hdec]
    exact profile_eq_iff.mp h q.val (q.property.trans_le hp)
  have hperm := sublistsLen_perm_of_exactKDeck_eq pattern.length
    (List.ofFn u) (List.ofFn v) hdeck
  have hcounts := (hperm.map (List.map g)).count_eq pattern
  rw [scatteredCount_eq_count_sublistsLen, scatteredCount_eq_count_sublistsLen]
  simpa only [List.map_ofFn, ← map_sublistsLen] using hcounts
private theorem factorSet_map (g : A → B) (word : Nat → A) (n : Nat) :
    wordFactorSet (g ∘ word) n =
      (wordFactorSet word n).image (fun u => g ∘ u) := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨i, rfl⟩ := mem_wordFactorSet.mp hu
    exact Finset.mem_image.mpr
      ⟨wordFactor word n i, mem_wordFactorSet.mpr ⟨i, rfl⟩, rfl⟩
  · intro hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨i, rfl⟩ := mem_wordFactorSet.mp hv
    exact mem_wordFactorSet.mpr ⟨i, rfl⟩
end D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
private theorem card_image_le_of_kernel {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (f : α → β) (g : α → γ)
    (hkernel : ∀ u ∈ s, ∀ v ∈ s, g u = g v → f u = f v) :
    (s.image f).card ≤ (s.image g).card := by
  classical
  let pick (z : ↥(s.image g)) : α := Classical.choose (Finset.mem_image.mp z.property)
  have pick_mem (z : ↥(s.image g)) : pick z ∈ s :=
    (Classical.choose_spec (Finset.mem_image.mp z.property)).1
  have pick_value (z : ↥(s.image g)) : g (pick z) = z.val :=
    (Classical.choose_spec (Finset.mem_image.mp z.property)).2
  let decode (z : ↥(s.image g)) : ↥(s.image f) :=
    ⟨f (pick z), Finset.mem_image.mpr ⟨pick z, pick_mem z, rfl⟩⟩
  have hsurj : Function.Surjective decode := by
    intro y
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp y.property
    let z : ↥(s.image g) := ⟨g u, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
    refine ⟨z, Subtype.ext ?_⟩
    exact (hkernel (pick z) (pick_mem z) u hu (pick_value z)).trans heq
  simpa only [Fintype.card_coe] using Fintype.card_le_of_surjective decode hsurj
theorem complexity_map_le (g : A → B) (word : Nat → A) (k n : Nat) :
    binomialComplexity (g ∘ word) k n ≤ binomialComplexity word k n := by
  classical
  unfold binomialComplexity
  rw [factorSet_map, Finset.image_image]
  exact card_image_le_of_kernel (wordFactorSet word n)
    (fun u => binomialProfile k (g ∘ u)) (binomialProfile k)
    (fun u _ v _ h => profile_eq_map g h)
theorem split_of_complexity_lt (word : Nat → A) {j k n : Nat} (hjk : j ≤ k)
    (hlt : binomialComplexity word j n < binomialComplexity word k n) :
    ∃ u ∈ wordFactorSet word n, ∃ v ∈ wordFactorSet word n,
      binomialProfile j u = binomialProfile j v ∧
        binomialProfile k u ≠ binomialProfile k v := by
  classical
  have hc : (((wordFactorSet word n).image (binomialProfile k)).image
      (restrictProfile (A := A) hjk)).card <
        ((wordFactorSet word n).image (binomialProfile k)).card := by
    rw [Finset.image_image]
    exact hlt
  obtain ⟨p, hp, q, hq, hpq, heq⟩ := Finset.exists_ne_map_eq_of_card_image_lt hc
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨u, hu, v, hv, heq, hpq⟩
theorem product_profile_injective (x : Nat → A) (y : Nat → B) (k n : Nat)
    (hx : Set.InjOn (binomialProfile k) (wordFactorSet x n : Set (Fin n → A)))
    (hy : Set.InjOn (binomialProfile k) (wordFactorSet y n : Set (Fin n → B))) :
    Set.InjOn (binomialProfile k)
      (wordFactorSet (fun i => (x i, y i)) n : Set (Fin n → A × B)) := by
  intro u hu v hv heq
  obtain ⟨s, rfl⟩ := mem_wordFactorSet.mp hu
  obtain ⟨t, rfl⟩ := mem_wordFactorSet.mp hv
  have hfirst : wordFactor x n s = wordFactor x n t :=
    hx (mem_wordFactorSet.mpr ⟨s, rfl⟩) (mem_wordFactorSet.mpr ⟨t, rfl⟩)
      (profile_eq_map Prod.fst heq)
  have hsecond : wordFactor y n s = wordFactor y n t :=
    hy (mem_wordFactorSet.mpr ⟨s, rfl⟩) (mem_wordFactorSet.mpr ⟨t, rfl⟩)
      (profile_eq_map Prod.snd heq)
  funext r
  exact Prod.ext (congrFun hfirst r) (congrFun hsecond r)
theorem strict_lifts_through_constant_tag (x : Nat → A) (y : Nat → B)
    (tag : B) {j k n : Nat} (hjk : j ≤ k)
    (hlift : ∀ u ∈ wordFactorSet x n,
      (fun r => (u r, tag)) ∈ wordFactorSet (fun i => (x i, y i)) n)
    (hlt : binomialComplexity x j n < binomialComplexity x k n) :
    binomialComplexity (fun i => (x i, y i)) j n <
      binomialComplexity (fun i => (x i, y i)) k n := by
  obtain ⟨u, hu, v, hv, hlow, hhigh⟩ := split_of_complexity_lt x hjk hlt
  apply complexity_lt_of_split _ hjk (hlift u hu) (hlift v hv)
  · exact profile_eq_map (fun a => (a, tag)) hlow
  · intro heq
    exact hhigh (profile_eq_map Prod.fst heq)
end D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
open D5.S1.Words.Complexity
variable {A : Type*} [Fintype A] [DecidableEq A]
theorem constant_tag_factors_of_recurrence (x : Nat → A) (y : Nat → Bool)
    (hrecur : ∀ n, ∀ u ∈ wordFactorSet x n,
      ∃ R, ∀ s, ∃ t, s ≤ t ∧ t + n ≤ s + R ∧ u = wordFactor x n t)
    (hzeros : ∀ R, ∃ s, ∀ q, s ≤ q → q < s + R → y q = false) :
    ∀ n, ∀ u ∈ wordFactorSet x n,
      (fun r => (u r, false)) ∈ wordFactorSet (fun i => (x i, y i)) n := by
  intro n u hu
  obtain ⟨R, hR⟩ := hrecur n u hu
  obtain ⟨s, hs⟩ := hzeros R
  obtain ⟨t, hst, htend, ht⟩ := hR s
  apply mem_wordFactorSet.mpr
  refine ⟨t, ?_⟩
  funext r
  apply Prod.ext
  · exact congrFun ht r
  · exact (hs (t + r.val) (by omega) (by have := r.isLt; omega)).symm
end D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
theorem complexity_map_eq_of_leftInverse (g : A → B) (r : B → A)
    (hr : Function.LeftInverse r g) (word : Nat → A) (k n : Nat) :
    binomialComplexity (g ∘ word) k n = binomialComplexity word k n := by
  apply le_antisymm (complexity_map_le g word k n)
  have h := complexity_map_le r (g ∘ word) k n
  have hw : r ∘ (g ∘ word) = word := by exact (Set.eqOn_univ (r ∘ g ∘ word) word).mp fun ⦃x⦄ _ => hr (word x)
  rwa [hw] at h
theorem factor_card_map_eq_of_injective (g : A → B) (hg : Function.Injective g)
    (word : Nat → A) (n : Nat) :
    (wordFactorSet (g ∘ word) n).card = (wordFactorSet word n).card := by
  classical
  rw [factorSet_map]
  apply Finset.card_image_of_injective
  intro u v huv
  funext i
  exact hg (congrFun huv i)
def pairCode : Bool × Bool → Fin 4
  | (false, false) => 0
  | (false, true) => 1
  | (true, false) => 2
  | (true, true) => 3
def pairDecode (a : Fin 4) : Bool × Bool :=
  (decide (2 ≤ a.val), decide (a.val % 2 = 1))
theorem pairCode_leftInverse : Function.LeftInverse pairDecode pairCode := by
  intro a
  rcases a with ⟨a, b⟩
  cases a <;> cases b <;> rfl
end D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
def boolCode : Bool → Fin 4
  | false => 0
  | true => 1
def boolDecode (a : Fin 4) : Bool := decide (a.val = 1)
theorem boolCode_leftInverse : Function.LeftInverse boolDecode boolCode := by
  intro a
  cases a <;> rfl
end D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary
open D5.S1.Words.Complexity.VivionBinomialConverseFails
private theorem positions_cons (a : Bool) (source : List Bool) :
    (a :: source).findIdxs id =
      if a then 0 :: (source.findIdxs id).map Nat.succ
      else (source.findIdxs id).map Nat.succ := by
  rw [List.findIdxs_cons, List.findIdxs_start]
  cases a <;> rfl
private theorem sum_map_succ (positions : List Nat) :
    (positions.map Nat.succ).sum = positions.sum + positions.length := by
  change (positions.map (fun n => n + 1)).sum = positions.sum + positions.length
  rw [List.sum_map_add]
  simp
private theorem onesPositions_length (source : List Bool) :
    (source.findIdxs id).length = scatteredCount [true] source := by
  rw [List.length_findIdxs,
    D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall.scatteredCount_singleton_eq_count,
    List.count_eq_countP]
  congr 1
private theorem pair_offsets_identity (source : List Bool) :
    2 * (((List.findIdxs id source)).sum + scatteredCount [true] source) =
      2 * scatteredCount [false, true] source +
        scatteredCount [true] source * (scatteredCount [true] source + 1) := by
  induction source with
  | nil => rfl
  | cons a source ih =>
      cases a <;>
        simp only [positions_cons, List.findIdxs_nil, List.sum_cons, zero_add, sum_map_succ,
          onesPositions_length, scatteredCount, Bool.false_eq_true,
          Bool.true_eq_false, ite_false, ite_true, add_zero] <;>
        nlinarith
private theorem onesPositions_injective {u v : List Bool} (hlen : u.length = v.length)
    (hpos : (List.findIdxs id u) = (List.findIdxs id v)) : u = v := by
  induction u generalizing v with
  | nil =>
      have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
      exact hv.symm
  | cons a u ih =>
      cases v with
      | nil => simp at hlen
      | cons b v =>
          have hlen' : u.length = v.length := by exact Nat.add_right_cancel hlen
          cases a <;> cases b
          · simp only [positions_cons, List.findIdxs_nil] at hpos
            have hp := (List.map_inj_right Nat.succ_injective).mp hpos
            exact congrArg (List.cons false) (ih hlen' hp)
          · have hz : 0 ∈ (List.findIdxs id (false :: u)) := by
              rw [hpos]; simp [positions_cons, List.findIdxs_nil]
            simpa [positions_cons, List.findIdxs_nil] using hz
          · have hz : 0 ∈ (List.findIdxs id (false :: v)) := by
              rw [← hpos]; simp [positions_cons, List.findIdxs_nil]
            simpa [positions_cons, List.findIdxs_nil] using hz
          · simp only [positions_cons, List.findIdxs_nil, if_true, List.cons.injEq, true_and] at hpos
            have hp := (List.map_inj_right Nat.succ_injective).mp hpos
            exact congrArg (List.cons true) (ih hlen' hp)
private theorem moments_eq_of_counts {u v : List Bool}
    (hones : scatteredCount [true] u = scatteredCount [true] v)
    (hpairs : scatteredCount [false, true] u = scatteredCount [false, true] v) :
    ((List.findIdxs id u)).length = ((List.findIdxs id v)).length ∧
      ((List.findIdxs id u)).sum = ((List.findIdxs id v)).sum := by
  constructor
  · simpa only [onesPositions_length] using hones
  · have hu := pair_offsets_identity u
    have hv := pair_offsets_identity v
    rw [hones, hpairs] at hu
    omega
end D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary
private theorem onesPositions_mem (source : List Bool) (r : Nat) :
    r ∈ source.findIdxs id ↔ source[r]? = some true := by
  simp only [List.mem_findIdxs_iff_exists_getElem_pos, id_eq,
    List.getElem?_eq_some_iff]
private theorem onesPositions_pairwise (source : List Bool) :
    (source.findIdxs id).Pairwise (· < ·) :=
  List.pairwise_findIdxs
end D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary
open D5.S1.Words.Complexity.VivionBinomialConverseFails
theorem singleton_counts_total (u : List Bool) :
    scatteredCount [false] u + scatteredCount [true] u = u.length := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> simp [scatteredCount] <;> omega
theorem profile_one_eq_of_true_count {n : Nat} {u v : Fin n → Bool}
    (h : scatteredCount [true] (List.ofFn u) = scatteredCount [true] (List.ofFn v)) :
    binomialProfile 1 u = binomialProfile 1 v := by
  apply D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection.profile_eq_iff.mpr
  intro pattern hp
  cases pattern with
  | nil => simp [scatteredCount]
  | cons a tail =>
      have ht : tail = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hp; omega)
      subst tail
      cases a
      · have hu := singleton_counts_total (List.ofFn u)
        have hv := singleton_counts_total (List.ofFn v)
        simp only [List.length_ofFn] at hu hv
        omega
      · exact h
end D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers
open scoped BigOperators
def Lacunary (p : Nat → Nat) : Prop :=
  0 < p 0 ∧ ∀ i, 3 * p i ≤ p (i + 1)
private theorem positive {p : Nat → Nat} (hp : Lacunary p) (i : Nat) : 0 < p i := by
  induction i with
  | zero => exact hp.1
  | succ i ih => have hs := hp.2 i; omega
private theorem strictMono {p : Nat → Nat} (hp : Lacunary p) : StrictMono p := by
  apply strictMono_nat_of_lt_succ
  intro i
  have hs := hp.2 i
  have hi := positive hp i
  omega
private theorem triple_le {p : Nat → Nat} (hp : Lacunary p) {i j : Nat}
    (hij : i < j) : 3 * p i ≤ p j := by
  exact (hp.2 i).trans ((strictMono hp).monotone (by omega))
private theorem block_sum_separation {p : Nat → Nat} (hp : Lacunary p)
    {i j : Nat} (hij : i < j) (h : Nat) :
    3 * (∑ d ∈ Finset.range h, p (i + d)) ≤
      ∑ d ∈ Finset.range h, p (j + d) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun d _ => triple_le hp (by omega))
private theorem block_sum_lower {p : Nat → Nat} (hp : Lacunary p)
    (j h : Nat) (hh : 2 ≤ h) :
    2 * h * p j ≤ ∑ d ∈ Finset.range h, p (j + d) := by
  obtain ⟨r, rfl⟩ : ∃ r, h = r + 2 := ⟨h - 2, by omega⟩
  induction r with
  | zero =>
      simp only [Nat.zero_add, Finset.sum_range_succ, Finset.sum_range_zero,
        Nat.add_zero, Nat.add_one, zero_add]
      have hs := hp.2 j
      nlinarith
  | succ r ih =>
      rw [show r + 1 + 2 = (r + 2) + 1 by omega, Finset.sum_range_succ]
      have hs : 3 * p j ≤ p (j + (r + 2)) := triple_le hp (by omega)
      nlinarith [ih (by omega)]
private theorem marker_block_sum_obstruction {p : Nat → Nat} (hp : Lacunary p)
    {i j h s t : Nat} (hij : i < j) (hh : 2 ≤ h) (ht : t ≤ p j)
    (heq : h * t + (∑ d ∈ Finset.range h, p (i + d)) =
      h * s + (∑ d ∈ Finset.range h, p (j + d))) : False := by
  have hsep := block_sum_separation hp hij h
  have hlo := block_sum_lower hp j h hh
  have hpos := positive hp j
  have htp : h * t ≤ h * p j := Nat.mul_le_mul_left h ht
  nlinarith [Nat.zero_le (h * s)]
def marker (n : Nat) : Nat := Nat.fib (3 * n + 2)
theorem marker_lacunary : Lacunary marker := by
  constructor
  · decide
  · intro i
    let n := 3 * i + 2
    change 3 * Nat.fib n ≤ Nat.fib (3 * (i + 1) + 2)
    rw [show 3 * (i + 1) + 2 = (n + 1) + 2 by omega]
    rw [Nat.fib_add_two (n := n + 1), Nat.fib_add_two (n := n)]
    have hmono : Nat.fib n ≤ Nat.fib (n + 1) := Nat.fib_le_fib_succ
    nlinarith
end D5.S1.Words.Complexity.LacunaryBinomialMarkers
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers
theorem scaled_lacunary {p : Nat → Nat} (hp : Lacunary p) (q : Nat) (hq : 0 < q) :
    Lacunary (fun i => q * p i) := by
  constructor
  · exact Nat.mul_pos hq hp.1
  · intro i
    simpa only [Nat.mul_assoc, Nat.mul_left_comm 3 q] using Nat.mul_le_mul_left q (hp.2 i)
end D5.S1.Words.Complexity.LacunaryBinomialMarkers
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers
open scoped BigOperators
private theorem index_le {p : Nat → Nat} (hp : Lacunary p) (i : Nat) : i ≤ p i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
      have hs := hp.2 i
      have hi := positive hp i
      omega
private noncomputable def firstAfter (p : Nat → Nat) (hp : Lacunary p) (s : Nat) : Nat :=
  Nat.find (show ∃ i, s ≤ p i from ⟨s, index_le hp s⟩)
private theorem firstAfter_spec {p : Nat → Nat} (hp : Lacunary p) (s : Nat) :
    s ≤ p (firstAfter p hp s) := by
  unfold firstAfter
  exact Nat.find_spec (show ∃ i, s ≤ p i from ⟨s, index_le hp s⟩)
private theorem firstAfter_le_iff {p : Nat → Nat} (hp : Lacunary p) (s i : Nat) :
    firstAfter p hp s ≤ i ↔ s ≤ p i := by
  constructor
  · intro hi
    exact (firstAfter_spec hp s).trans ((strictMono hp).monotone hi)
  · intro hi
    exact Nat.find_min' _ hi
private theorem lt_firstAfter_iff {p : Nat → Nat} (hp : Lacunary p) (s i : Nat) :
    i < firstAfter p hp s ↔ p i < s := by
  have h := firstAfter_le_iff hp s i
  omega
private theorem firstAfter_mono {p : Nat → Nat} (hp : Lacunary p) :
    Monotone (firstAfter p hp) := by
  intro s t hst
  exact (firstAfter_le_iff hp s _).mpr (hst.trans (firstAfter_spec hp t))
noncomputable def markerWord (p : Nat → Nat) (n : Nat) : Bool :=
  by
    classical
    exact if ∃ i, p i = n then true else false
theorem markerWord_eq_true (p : Nat → Nat) (n : Nat) :
    markerWord p n = true ↔ ∃ i, p i = n := by
  classical
  simp [markerWord]
end D5.S1.Words.Complexity.LacunaryBinomialMarkers
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary
private theorem marker_factor_member (p : Nat → Nat) (n s r : Nat) :
    r ∈ (List.findIdxs id (List.ofFn (wordFactor (markerWord p) n s))) ↔
      r < n ∧ ∃ i, p i = s + r := by
  by_cases hr : r < n <;>
    simp [onesPositions_mem, List.getElem?_ofFn, hr, wordFactor, markerWord_eq_true]
private theorem marker_factor_positions {p : Nat → Nat} (hp : Lacunary p) (n s : Nat) :
    (List.findIdxs id (List.ofFn (wordFactor (markerWord p) n s))) =
      List.ofFn (fun d : Fin (firstAfter p hp (s + n) - firstAfter p hp s) =>
        p (firstAfter p hp s + d.val) - s) := by
  let a := firstAfter p hp s
  let b := firstAfter p hp (s + n)
  have hab : a ≤ b := firstAfter_mono hp (by omega)
  have hsa : s ≤ p a := firstAfter_spec hp s
  apply List.Pairwise.eq_of_mem_iff (onesPositions_pairwise _) ?_ ?_
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    have hlt : p (a + i.val) < p (a + j.val) := (strictMono hp) (by exact Nat.add_lt_add_left hij a)
    have hlo : s ≤ p (a + i.val) := hsa.trans ((strictMono hp).monotone (by omega))
    change p (a + i.val) - s < p (a + j.val) - s
    omega
  · intro r
    rw [marker_factor_member, List.mem_ofFn]
    constructor
    · rintro ⟨hr, q, hq⟩
      have haq : a ≤ q := (firstAfter_le_iff hp s q).mpr (by omega)
      have hqb : q < b := (lt_firstAfter_iff hp (s + n) q).mpr (by omega)
      refine ⟨⟨q - a, by change q - a < b - a; omega⟩, ?_⟩
      change p (a + (q - a)) - s = r
      rw [show a + (q - a) = q by omega, hq]
      omega
    · rintro ⟨d, hd⟩
      have had : a ≤ a + d.val := by exact Nat.le_add_right a d.val
      have hdb : a + d.val < b := by have := d.isLt; change d.val < b - a at this; omega
      have hlo : s ≤ p (a + d.val) := (firstAfter_le_iff hp s _).mp had
      have hhi : p (a + d.val) < s + n := (lt_firstAfter_iff hp (s + n) _).mp hdb
      change p (a + d.val) - s = r at hd
      exact ⟨by omega, a + d.val, by omega⟩
end D5.S1.Words.Complexity.LacunaryBinomialMarkers
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers
open scoped BigOperators
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary
private def blockOffsets (p : Nat → Nat) (s i h : Nat) : List Nat :=
  List.ofFn (fun d : Fin h => p (i + d.val) - s)
private theorem block_sum_identity {p : Nat → Nat} (hp : Lacunary p)
    (s i h : Nat) (hsi : s ≤ p i) :
    h * s + (blockOffsets p s i h).sum = ∑ d ∈ Finset.range h, p (i + d) := by
  unfold blockOffsets
  rw [Fin.sum_ofFn, ← Finset.sum_range (n := h) (fun d => p (i + d) - s)]
  calc
    h * s + (∑ d ∈ Finset.range h, (p (i + d) - s)) =
        ∑ d ∈ Finset.range h, (s + (p (i + d) - s)) := by
      simp [Finset.sum_add_distrib]
    _ = ∑ d ∈ Finset.range h, p (i + d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hle : s ≤ p (i + d) := hsi.trans ((strictMono hp).monotone (by omega))
      omega
private theorem block_offsets_eq_of_sum {p : Nat → Nat} (hp : Lacunary p)
    (s t i j h : Nat) (hsi : s ≤ p i) (htj : t ≤ p j)
    (hsum : (blockOffsets p s i h).sum = (blockOffsets p t j h).sum) :
    blockOffsets p s i h = blockOffsets p t j h := by
  by_cases hh : 2 ≤ h
  · have hsum_i := block_sum_identity hp s i h hsi
    have hsum_j := block_sum_identity hp t j h htj
    have heq : h * t + (∑ d ∈ Finset.range h, p (i + d)) =
        h * s + (∑ d ∈ Finset.range h, p (j + d)) := by omega
    have hij : i = j := by
      rcases lt_trichotomy i j with hij | hij | hji
      · exact (marker_block_sum_obstruction hp hij hh htj heq).elim
      · exact hij
      · exact (marker_block_sum_obstruction hp hji hh hsi heq.symm).elim
    subst j
    have hst : s = t := Nat.eq_of_mul_eq_mul_left (by omega : 0 < h) (by omega)
    subst t
    rfl
  · have hsmall : h = 0 ∨ h = 1 := by omega
    rcases hsmall with rfl | rfl
    · rfl
    · simpa [blockOffsets, List.ofFn_succ] using hsum
private theorem marker_factor_eq_of_counts {p : Nat → Nat} (hp : Lacunary p)
    (n s t : Nat)
    (hones : scatteredCount [true] (List.ofFn (wordFactor (markerWord p) n s)) =
      scatteredCount [true] (List.ofFn (wordFactor (markerWord p) n t)))
    (hpairs : scatteredCount [false, true] (List.ofFn (wordFactor (markerWord p) n s)) =
      scatteredCount [false, true] (List.ofFn (wordFactor (markerWord p) n t))) :
    wordFactor (markerWord p) n s = wordFactor (markerWord p) n t := by
  have hmom := moments_eq_of_counts hones hpairs
  let i := firstAfter p hp s
  let j := firstAfter p hp t
  let h := firstAfter p hp (s + n) - i
  let m := firstAfter p hp (t + n) - j
  have hs : (List.findIdxs id (List.ofFn (wordFactor (markerWord p) n s))) =
      blockOffsets p s i h := marker_factor_positions hp n s
  have ht : (List.findIdxs id (List.ofFn (wordFactor (markerWord p) n t))) =
      blockOffsets p t j m := marker_factor_positions hp n t
  have hhm : h = m := by
    simpa only [hs, ht, blockOffsets, List.length_ofFn] using hmom.1
  have ht' : (List.findIdxs id (List.ofFn (wordFactor (markerWord p) n t))) =
      blockOffsets p t j h := by simpa only [hhm] using ht
  have hsum : (blockOffsets p s i h).sum = (blockOffsets p t j h).sum := by
    rw [← hs, ← ht']
    exact hmom.2
  have hb := block_offsets_eq_of_sum hp s t i j h
    (firstAfter_spec hp s) (firstAfter_spec hp t) hsum
  have hpositions :
      (List.findIdxs id (List.ofFn (wordFactor (markerWord p) n s))) =
        (List.findIdxs id (List.ofFn (wordFactor (markerWord p) n t))) := by rw [hs, ht', hb]
  exact List.ofFn_injective (onesPositions_injective (by simp) hpositions)
theorem marker_profile_two_injective {p : Nat → Nat} (hp : Lacunary p) (n : Nat) :
    Set.InjOn (binomialProfile 2)
      (wordFactorSet (markerWord p) n : Set (Fin n → Bool)) := by
  intro u hu v hv heq
  obtain ⟨s, rfl⟩ := mem_wordFactorSet.mp hu
  obtain ⟨t, rfl⟩ := mem_wordFactorSet.mp hv
  apply marker_factor_eq_of_counts hp n s t
  · exact congrFun (congrFun heq (⟨1, by omega⟩ : Fin 3)) (fun _ => true)
  · exact congrFun (congrFun heq (⟨2, by omega⟩ : Fin 3)) ![false, true]
theorem marker_complexity_two {p : Nat → Nat} (hp : Lacunary p) (n : Nat) :
    binomialComplexity (markerWord p) 2 n = (wordFactorSet (markerWord p) n).card := by
  classical
  exact Finset.card_image_of_injOn (marker_profile_two_injective hp n)
end D5.S1.Words.Complexity.LacunaryBinomialMarkers
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary
private theorem windowCount_formula {p : Nat → Nat} (hp : Lacunary p) (n s : Nat) :
    scatteredCount [true] (List.ofFn (wordFactor (markerWord p) n s)) = firstAfter p hp (s + n) - firstAfter p hp s := by
  rw [← onesPositions_length, marker_factor_positions hp, List.length_ofFn]
private theorem firstAfter_zero {p : Nat → Nat} (hp : Lacunary p) : firstAfter p hp 0 = 0 := by
  have h := (firstAfter_le_iff hp 0 0).mpr (Nat.zero_le _)
  omega
private theorem firstAfter_marker_add_one {p : Nat → Nat} (hp : Lacunary p) (i : Nat) :
    firstAfter p hp (p i + 1) = i + 1 := by
  have hlo : i < firstAfter p hp (p i + 1) :=
    (lt_firstAfter_iff hp (p i + 1) i).mpr (by omega)
  have hhi : firstAfter p hp (p i + 1) ≤ i + 1 :=
    (firstAfter_le_iff hp _ _).mpr ((strictMono hp (Nat.lt_succ_self i)))
  omega
private theorem windowCount_prefix {p : Nat → Nat} (hp : Lacunary p) (i : Nat) :
    scatteredCount [true] (List.ofFn (wordFactor (markerWord p) (p i + 1) 0)) = i + 1 := by
  rw [windowCount_formula hp]
  simp only [Nat.zero_add, firstAfter_zero hp, firstAfter_marker_add_one hp, Nat.sub_zero]
private theorem firstAfter_step {p : Nat → Nat} (hp : Lacunary p) (s : Nat) :
    firstAfter p hp (s + 1) ≤ firstAfter p hp s + 1 := by
  apply (firstAfter_le_iff hp _ _).mpr
  have hs := firstAfter_spec hp s
  have hlt : p (firstAfter p hp s) < p (firstAfter p hp s + 1) := strictMono hp (by omega)
  omega
private theorem windowCount_drop_le_one {p : Nat → Nat} (hp : Lacunary p) (n s : Nat) :
    scatteredCount [true] (List.ofFn (wordFactor (markerWord p) n s)) ≤ scatteredCount [true] (List.ofFn (wordFactor (markerWord p) n (s + 1))) + 1 := by
  rw [windowCount_formula hp, windowCount_formula hp]
  have hleft := firstAfter_step hp s
  have hright := firstAfter_mono hp (show s + n ≤ s + 1 + n by omega)
  have hbase := firstAfter_mono hp (show s ≤ s + n by omega)
  have hnext := firstAfter_mono hp (show s + 1 ≤ s + 1 + n by omega)
  omega
private theorem windowCount_has_zero {p : Nat → Nat} (hp : Lacunary p) (n : Nat) :
    ∃ s, scatteredCount [true] (List.ofFn (wordFactor (markerWord p) n s)) = 0 := by
  let i := n + 1
  let s := p i + 1
  have hlarge : n < p i := by
    change n < p (n + 1)
    have := index_le hp (n + 1)
    omega
  have hgap : s + n ≤ p (i + 1) := by have := hp.2 i; dsimp [s]; omega
  have ha : firstAfter p hp s = i + 1 := firstAfter_marker_add_one hp i
  have hb : firstAfter p hp (s + n) = i + 1 := by
    have hlo := firstAfter_mono hp (show s ≤ s + n by omega)
    have hhi := (firstAfter_le_iff hp (s + n) (i + 1)).mpr hgap
    omega
  exact ⟨s, by rw [windowCount_formula hp, ha, hb, Nat.sub_self]⟩
private theorem hits_every_level {f : Nat → Nat}
    (hstep : ∀ s, f s ≤ f (s + 1) + 1) (hz : ∃ s, f s = 0)
    (m : Nat) (hm : m ≤ f 0) : ∃ s, f s = m := by
  have hex : ∃ s, f s ≤ m := by obtain ⟨s, hs⟩ := hz; exact ⟨s, by omega⟩
  let t := Nat.find hex
  have ht : f t ≤ m := Nat.find_spec hex
  refine ⟨t, ?_⟩
  by_cases hzero : t = 0
  · rw [hzero] at ht ⊢
    exact Nat.le_antisymm ht hm
  · obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hprev : ¬ f s ≤ m := Nat.find_min hex (by dsimp [t] at hs ⊢; omega)
    have hd := hstep s
    rw [← hs] at hd
    omega
private theorem marker_count_realizes_levels {p : Nat → Nat} (hp : Lacunary p) (i m : Nat)
    (hm : m ≤ i + 1) : ∃ s, scatteredCount [true] (List.ofFn (wordFactor (markerWord p) (p i + 1) s)) = m := by
  apply hits_every_level (windowCount_drop_le_one hp _) (windowCount_has_zero hp _) m
  rwa [windowCount_prefix hp]
end D5.S1.Words.Complexity.LacunaryBinomialMarkers
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers
open scoped BigOperators
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary
theorem marker_unbounded_abelian {p : Nat → Nat} (hp : Lacunary p) :
    ∀ bound : Nat, ∃ n : Nat, bound < binomialComplexity (markerWord p) 1 n := by
  classical
  intro bound
  let n := p bound + 1
  let factors := wordFactorSet (markerWord p) n
  let count := fun u : Fin n → Bool => scatteredCount [true] (List.ofFn u)
  have hsub : Finset.range (bound + 2) ⊆ factors.image count := by
    intro m hm
    obtain ⟨s, hs⟩ := marker_count_realizes_levels hp bound m (by have := Finset.mem_range.mp hm; omega)
    exact Finset.mem_image.mpr
      ⟨wordFactor (markerWord p) n s, mem_wordFactorSet.mpr ⟨s, rfl⟩, hs⟩
  have hc : bound + 2 ≤ (factors.image count).card := by
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hk : (factors.image count).card ≤ binomialComplexity (markerWord p) 1 n := by
    apply card_image_le_of_kernel factors count (binomialProfile 1)
    intro u hu v hv heq
    exact congrFun (congrFun heq (⟨1, by omega⟩ : Fin 2)) (fun _ => true)
  exact ⟨n, by omega⟩
theorem marker_zero_intervals {p : Nat → Nat} (hp : Lacunary p) :
    ∀ R, ∃ s, ∀ q, s ≤ q → q < s + R → markerWord p q = false := by
  intro R
  obtain ⟨s, hs⟩ := windowCount_has_zero hp R
  have hpos : (List.findIdxs id (List.ofFn (wordFactor (markerWord p) R s))) = [] :=
    List.length_eq_zero_iff.mp ((onesPositions_length _).trans hs)
  refine ⟨s, ?_⟩
  intro q hsq hq
  have hr : q - s < R := by exact Nat.sub_lt_left_of_lt_add hsq hq
  cases hy : markerWord p q with
  | false => rfl
  | true =>
      have hm : q - s ∈ (List.findIdxs id (List.ofFn (wordFactor (markerWord p) R s))) := by
        rw [onesPositions_mem]
        simp [List.getElem?_ofFn, hr, wordFactor, show s + (q - s) = q by omega, hy]
      rw [hpos] at hm
      exact (List.not_mem_nil hm).elim
private theorem firstAfter_marker {p : Nat → Nat} (hp : Lacunary p) (i : Nat) :
    firstAfter p hp (p i) = i := by
  have hlo : i ≤ firstAfter p hp (p i) :=
    (strictMono hp).le_iff_le.mp (firstAfter_spec hp (p i))
  have hhi : firstAfter p hp (p i) ≤ i := (firstAfter_le_iff hp _ _).mpr le_rfl
  omega
theorem marker_strict_one_two {p : Nat → Nat} (hp : Lacunary p)
    (n : Nat) (hn : 2 ≤ n) :
    binomialComplexity (markerWord p) 1 n < binomialComplexity (markerWord p) 2 n := by
  let i := n + 1
  let s := p i
  let t := p i + 1 - n
  have hpn : n ≤ p n := index_le hp n
  have hpi : n + 1 ≤ p i := index_le hp i
  have hprev := hp.2 n
  have hnext := hp.2 i
  have htlo : p n < t := by dsimp [t, i]; omega
  have hthi : t ≤ p i := by dsimp [t]; omega
  have htsum : t + n = p i + 1 := by dsimp [t]; omega
  have hsstart : firstAfter p hp s = i := firstAfter_marker hp i
  have htstart : firstAfter p hp t = i := by
    have hlo := (lt_firstAfter_iff hp t n).mpr htlo
    have hhi := (firstAfter_le_iff hp t i).mpr hthi
    dsimp [i] at hhi ⊢
    omega
  have hsend : firstAfter p hp (s + n) = i + 1 := by
    have hlo : i < firstAfter p hp (s + n) :=
      (lt_firstAfter_iff hp _ i).mpr (by dsimp [s]; omega)
    have hhi : firstAfter p hp (s + n) ≤ i + 1 :=
      (firstAfter_le_iff hp _ _).mpr (by dsimp [s]; omega)
    omega
  have htend : firstAfter p hp (t + n) = i + 1 := by
    rw [htsum, firstAfter_marker_add_one hp]
  have hspos : (List.findIdxs id (List.ofFn (wordFactor (markerWord p) n s))) = [0] := by
    rw [marker_factor_positions hp, hsstart, hsend]
    simp [List.ofFn_succ, s]
  have htpos : (List.findIdxs id (List.ofFn (wordFactor (markerWord p) n t))) = [n - 1] := by
    rw [marker_factor_positions hp, htstart, htend]
    simp only [Nat.add_sub_cancel_left, List.ofFn_succ, Fin.val_zero, Nat.add_zero,
      List.ofFn_zero]
    congr 1
    dsimp [t]
    omega
  apply complexity_lt_of_split (markerWord p) (by omega : 1 ≤ 2)
    (mem_wordFactorSet.mpr ⟨s, rfl⟩) (mem_wordFactorSet.mpr ⟨t, rfl⟩)
  · apply profile_one_eq_of_true_count
    rw [← onesPositions_length, ← onesPositions_length, hspos, htpos]
    rfl
  · intro heq
    have hones := congrFun (congrFun heq (⟨1, by omega⟩ : Fin 3)) (fun _ => true)
    have hpairs := congrFun (congrFun heq (⟨2, by omega⟩ : Fin 3)) ![false, true]
    have hmom := (moments_eq_of_counts hones hpairs).2
    rw [hspos, htpos] at hmom
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hmom
    omega
end D5.S1.Words.Complexity.LacunaryBinomialMarkers
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers.Golden
open D5.S1.Words D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.GoldenRecovery.GoldenFactorSecondOrderBinomialRigidity
open D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall (scatteredCount_singleton_eq_count)
open scoped BigOperators
private theorem true_false_snoc (source : List Bool) (a : Bool) :
    scatteredCount [true, false] (source ++ [a]) =
      scatteredCount [true, false] source +
        if a = false then scatteredCount [true] source else 0 := by
  induction source with
  | nil => cases a <;> simp [scatteredCount]
  | cons b source ih =>
      have hs := scatteredCount_singleton_eq_count false (source ++ [a])
      rw [List.count_append, ← scatteredCount_singleton_eq_count] at hs
      cases a <;> cases b <;>
        simp [scatteredCount, ih, hs] <;> omega
theorem golden_true_count (n i : Nat) :
    scatteredCount [true] (List.ofFn (wordFactor goldenWord n i)) =
      goldenWindowTrueCount i n := by
  rw [scatteredCount_singleton_eq_count]
  exact goldenFactor_count_true n i
theorem golden_pair_count (n i : Nat) :
    scatteredCount [true, false] (List.ofFn (wordFactor goldenWord n i)) =
      goldenTrueFalseCount i n := by
  change scatteredCount [true, false] (goldenFactor n i) = _
  induction n with
  | zero => simp [goldenFactor, goldenTrueFalseCount, scatteredCount]
  | succ n ih =>
      rw [goldenFactor_succ, true_false_snoc, ih]
      change goldenTrueFalseCount i n +
        (if goldenWord (i + n) = false then scatteredCount [true] (goldenFactor n i) else 0) = _
      have hc : scatteredCount [true] (goldenFactor n i) = goldenWindowTrueCount i n :=
        golden_true_count n i
      rw [hc]
      unfold goldenTrueFalseCount
      rw [Finset.sum_range_succ]
      cases h : goldenWord (i + n) <;> simp [h]
theorem golden_profile_two_injective (n : Nat) :
    Set.InjOn (binomialProfile 2) (wordFactorSet goldenWord n : Set (Fin n → Bool)) := by
  intro u hu v hv heq
  obtain ⟨i, rfl⟩ := mem_wordFactorSet.mp hu
  obtain ⟨j, rfl⟩ := mem_wordFactorSet.mp hv
  have hone := (D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection.profile_eq_iff.mp heq) [true] (by decide)
  have hpair := (D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection.profile_eq_iff.mp heq) [true, false] (by decide)
  rw [golden_true_count, golden_true_count] at hone
  rw [golden_pair_count, golden_pair_count] at hpair
  exact List.ofFn_injective (golden_factor_eq_of_second_order_counts n i j hone hpair)
end D5.S1.Words.Complexity.LacunaryBinomialMarkers.Golden
namespace D5.S1.Words.Complexity.LacunaryBinomialMarkers.Golden
open D5.S1.Words D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
theorem golden_abelian_bound (n : Nat) : binomialComplexity goldenWord 1 n ≤ 3 := by
  classical
  let factors := wordFactorSet goldenWord n
  let count := fun u : Fin n → Bool => scatteredCount [true] (List.ofFn u)
  let c := goldenWindowTrueCount 0 n
  have hk : ∀ u ∈ factors, ∀ v ∈ factors, count u = count v →
      binomialProfile 1 u = binomialProfile 1 v := by
    intro u _ v _ h
    exact D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary.profile_one_eq_of_true_count h
  have hs : factors.image count ⊆ ({c - 1, c, c + 1} : Finset Nat) := by
    intro a ha
    obtain ⟨u, hu, hau⟩ := Finset.mem_image.mp ha
    obtain ⟨i, rfl⟩ := mem_wordFactorSet.mp hu
    have hc : a = goldenWindowTrueCount i n := hau.symm.trans (golden_true_count n i)
    have hb := abs_le.mp (goldenWord_balanced_one i 0 n)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    dsimp [c]
    omega
  calc
    binomialComplexity goldenWord 1 n ≤ (factors.image count).card :=
      D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection.card_image_le_of_kernel factors (binomialProfile 1) count hk
    _ ≤ ({c - 1, c, c + 1} : Finset Nat).card := Finset.card_le_card hs
    _ ≤ 3 := by
      have h1 := Finset.card_insert_le (c - 1) ({c, c + 1} : Finset Nat)
      have h2 := Finset.card_insert_le c ({c + 1} : Finset Nat)
      simp only [Finset.card_singleton] at h2
      omega
end D5.S1.Words.Complexity.LacunaryBinomialMarkers.Golden
