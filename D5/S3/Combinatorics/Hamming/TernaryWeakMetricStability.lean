/- GID: D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hamming/TernaryWeakMetricStability
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact retained ternary near-maximum weak metric dimensions. -/

/-
admission_basis: escape-witness (candidate; native admission not yet established).
Reg audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23304.
Current compiled telescopes, axiom closures and live dependencies must be
checked separately against these exact source bytes; Reg binding remains unfinished.
The preregistered live consumer is result and least_threshold: the complete
ternary deficit-four/five family below Kumar's sufficient cutoff, rather than
another statement of the eventual theorem.  full_separation_bound supplies the
non-bind-only uniform estimate through neutral words and the coordinate
recurrence; the two distinct translation orbits and singleton supply actual
attainers.  All helpers are consumed by this chain.  The d=2 values are published
prerequisites, not novelty claims; their structural proofs establish leastness.

Sources: Aryan Kumar, Weak k-metric dimension of Hamming graphs: rectangular
products and near-maximum parameters, arXiv:2609.32161v1, Section 6.3--6.4 and
Section 7.  Elena Fernandez, Sandi Klavzar, Dorota Kuziak, Manuel Munoz-Marquez
and Ismael G. Yero, On the weak k-metric dimension of Hamming graphs,
arXiv:2505.19642v1, introduction (k=1) and Theorem 1.1 (k=2).
The named Hamming owners and pinned Mathlib supply no generic theorem of this
exact threshold in the inspected scope.  This is no claim of global priority.

Utility none: the main mathematical content is uniform in every dimension,
with symbolic coordinate sums, extremal constructions, and a structural
lower-dimensional obstruction.  Scalar finite-alphabet normalization and
finite-set cardinal arithmetic are internal proof steps, not retained
finite-instance contributions.  No native_decide declarations are retained.
The mirror-E rationale concerns the absence of an experimental evidence file;
it is not an open-problem-resolution admission waiver or a Reg exception.
Direct frozen project mathematical dependencies: none.  Native Hamming metric,
finite-sum, finite-function, and order APIs are reused from pinned Mathlib.
Original Lean implementation by OpenAI Codex, licensed under Apache-2.0.
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Nat.Dist
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false

namespace D5.S3.Combinatorics.Hamming.TernaryWeakMetricStability

open scoped BigOperators

abbrev Word (d : ℕ) := Fin d → Fin 3

def distance {d : ℕ} (x y : Word d) : ℕ :=
  ∑ i : Fin d, if x i = y i then 0 else 1

theorem distance_eq_hammingDist {d : ℕ} (x y : Word d) :
    distance x y = hammingDist x y := by
  simp only [distance, hammingDist, Finset.card_filter, ne_eq, ite_not]

def separation {d : ℕ} (T : Finset (Word d)) (x y : Word d) : ℕ :=
  ∑ z ∈ T, Nat.dist (distance x z) (distance y z)

def IsWeakResolving (d k : ℕ) (S : Finset (Word d)) : Prop :=
  ∀ x y, x ≠ y → k ≤ separation S x y

noncomputable def metricDimension (d k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ S : Finset (Word d), IsWeakResolving d k S ∧ S.card = n}

def kappa (d : ℕ) : ℕ := 2 * 3 ^ (d - 1)

def omittedCapacity (t : ℕ) : ℕ := 3 * (t / 2) + (t % 2)

def complement {d : ℕ} (T : Finset (Word d)) : Finset (Word d) :=
  (Finset.univ : Finset (Word d)) \ T

theorem complement_card {d : ℕ} (T : Finset (Word d)) :
    (complement T).card + T.card = 3 ^ d := by
  classical
  simpa [complement] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)

theorem separation_complement {d : ℕ} (T : Finset (Word d)) (x y : Word d) :
    separation (complement T) x y + separation T x y =
      separation (Finset.univ : Finset (Word d)) x y := by
  classical
  exact Finset.sum_sdiff (Finset.subset_univ T)

private def orbit {d : ℕ} (x : Word d) : Finset (Word d) :=
  {x, fun i => ⟨((x i).val + 1) % 3, by omega⟩,
    fun i => ⟨((x i).val + 2) % 3, by omega⟩}

private def constantWord {d : ℕ} (a : Fin 3) : Word d := fun _ => a

private def mixedWord {d : ℕ} : Word d := fun i => if i.val = 0 then 0 else 1

private def extraWord {d : ℕ} : Word d :=
  fun i => if i.val = 0 then 0 else if i.val = 1 then 2 else 0

private def baseOmitted {d : ℕ} : Finset (Word d) :=
  orbit (constantWord 0) ∪ orbit mixedWord

private def oddOmitted {d : ℕ} : Finset (Word d) :=
  insert extraWord (baseOmitted (d := d))

private def distanceExcept {d : ℕ} (i : Fin d) (x z : Word d) : ℕ :=
  ∑ j ∈ (Finset.univ.erase i), if x j = z j then 0 else 1

private theorem distance_eq_update_sum {d : ℕ} (i : Fin d) (x z : Word d) :
    distance x z = (if x i = z i then 0 else 1) + distanceExcept i x z := by
  classical
  unfold distance distanceExcept
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp [add_comm]

/- The coordinate recurrence is symbolic in dimension.  No enumeration of
   vertex pairs, dimensions, or omitted subsets is used in this argument. -/
private def zeroCount {d : ℕ} (x y : Word d) : ℕ :=
  ∑ z : Word d, if distance x z = distance y z then 1 else 0

private theorem sum_word_cons {d : ℕ} (f : Word (d + 1) → ℕ) :
    (∑ z, f z) = ∑ z : Word d, ∑ c : Fin 3, f (Fin.cons c z) := by
  rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => Fin 3)).sum_comp f]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

private theorem distance_cons {d : ℕ} (a b : Fin 3) (x y : Word d) :
    distance (Fin.cons a x) (Fin.cons b y) =
      distance x y + (if a = b then 0 else 1) := by
  simp [distance, Fin.sum_univ_succ, add_comm]

private theorem distance_self {d : ℕ} (x : Word d) : distance x x = 0 := by
  simp [distance]

private theorem distance_pos {d : ℕ} {x y : Word d} (hxy : x ≠ y) :
    1 ≤ distance x y := by
  simpa only [distance_eq_hammingDist] using (Nat.succ_le_iff.mpr (hammingDist_pos.mpr hxy))

private theorem distance_le {d : ℕ} (x y : Word d) : distance x y ≤ d := by
  simpa only [distance_eq_hammingDist, Fintype.card_fin] using
    hammingDist_le_card_fintype (x := x) (y := y)

private def neutralLetter (a b : Fin 3) : Fin 3 :=
  if a = b then a else if a ≠ 0 ∧ b ≠ 0 then 0
    else if a ≠ 1 ∧ b ≠ 1 then 1 else 2

private theorem neutralLetter_spec (a b : Fin 3) :
    (if a = neutralLetter a b then 0 else 1 : ℕ) =
      (if b = neutralLetter a b then 0 else 1 : ℕ) ∧
    (a ≠ b → neutralLetter a b ≠ a ∧ neutralLetter a b ≠ b) := by
  fin_cases a <;> fin_cases b <;> decide

private def neutralWord {d : ℕ} (x y : Word d) : Word d :=
  fun i => neutralLetter (x i) (y i)

private theorem neutralWord_distance {d : ℕ} (x y : Word d) :
    distance x (neutralWord x y) = distance y (neutralWord x y) := by
  exact Finset.sum_congr rfl (fun i _ => (neutralLetter_spec (x i) (y i)).1)

private theorem gap_exists {d : ℕ} {x y : Word d} (hxy : x ≠ y) :
    ∃ z : Word d, distance x z + 1 = distance y z := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    exact not_forall.mp (fun h => hxy (funext h))
  let z := Function.update (neutralWord x y) i (x i)
  refine ⟨z, ?_⟩
  have he : distanceExcept i x z = distanceExcept i y z := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [z, Function.update_of_ne hji]
    exact (neutralLetter_spec (x j) (y j)).1
  rw [distance_eq_update_sum i x z, distance_eq_update_sum i y z, he]
  simp [z, Ne.symm hi, add_comm]

private theorem indicator_sum_pos {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] (hp : ∃ a, p a) :
    1 ≤ ∑ a, if p a then 1 else 0 := by
  obtain ⟨a, ha⟩ := hp
  calc
    1 = (if p a then 1 else 0 : ℕ) := by simp [ha]
    _ ≤ ∑ a, if p a then 1 else 0 :=
      Finset.single_le_sum (f := fun a => if p a then 1 else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

private theorem zeroCount_pos {d : ℕ} (x y : Word d) : 1 ≤ zeroCount x y := by
  exact indicator_sum_pos _ ⟨neutralWord x y, neutralWord_distance x y⟩

private theorem zeroCount_cons_same {d : ℕ} (a : Fin 3) (x y : Word d) :
    zeroCount (Fin.cons a x) (Fin.cons a y) = 3 * zeroCount x y := by
  unfold zeroCount
  rw [sum_word_cons]
  simp_rw [distance_cons, Nat.add_right_cancel_iff]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Finset.mul_sum]

private theorem zeroCount_cons_eq {d : ℕ} {a b : Fin 3} (hab : a ≠ b)
    (x : Word d) : zeroCount (Fin.cons a x) (Fin.cons b x) = 3 ^ d := by
  unfold zeroCount
  rw [sum_word_cons]
  have hp (z : Word d) :
      (∑ c : Fin 3, if distance (Fin.cons a x) (Fin.cons c z) =
        distance (Fin.cons b x) (Fin.cons c z) then 1 else 0) = 1 := by
    simp_rw [distance_cons, Nat.add_left_cancel_iff]
    rw [Fin.sum_univ_three]
    fin_cases a <;> fin_cases b <;> simp_all
  simp_rw [hp]
  simp

private theorem zeroCount_cons_ne {d : ℕ} {a b : Fin 3} (hab : a ≠ b)
    {x y : Word d} (hxy : x ≠ y) :
    3 ≤ zeroCount (Fin.cons a x) (Fin.cons b y) := by
  unfold zeroCount
  rw [sum_word_cons, Finset.sum_comm]
  calc
    3 = ∑ _c : Fin 3, (1 : ℕ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c _
      apply indicator_sum_pos
      by_cases hca : c = a
      · obtain ⟨z, hz⟩ := gap_exists hxy.symm
        exact ⟨z, by simpa [distance_cons, hca, hab, hab.symm] using hz.symm⟩
      · by_cases hcb : c = b
        · obtain ⟨z, hz⟩ := gap_exists hxy
          exact ⟨z, by simpa [distance_cons, hcb, hab, hab.symm] using hz⟩
        · exact ⟨neutralWord x y, by
            simpa only [distance_cons, ite_eq_right (Ne.symm hca), ite_eq_right (Ne.symm hcb), Nat.add_right_cancel_iff] using neutralWord_distance x y⟩

private theorem zeroCount_three {d : ℕ} (hd : 2 ≤ d) (x y : Word d) :
    3 ≤ zeroCount x y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y]
  by_cases hab : x 0 = y 0
  · rw [hab, zeroCount_cons_same]
    have hz := zeroCount_pos (Fin.tail x) (Fin.tail y)
    omega
  · by_cases ht : Fin.tail x = Fin.tail y
    · rw [ht, zeroCount_cons_eq hab]
      have hn : 1 ≤ n := by omega
      calc
        3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by decide) hn
    · exact zeroCount_cons_ne hab ht

private theorem ternary_distance_step (a b : Fin 3) (A B : ℕ) :
    (∑ c : Fin 3, Nat.dist (A + if a = c then 0 else 1)
      (B + if b = c then 0 else 1)) =
      3 * Nat.dist A B + if a ≠ b ∧ A = B then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_three, Nat.dist] <;> (try split_ifs) <;> omega

private theorem full_separation_cons {d : ℕ} (a b : Fin 3) (x y : Word d) :
    separation Finset.univ (Fin.cons a x) (Fin.cons b y) =
      3 * separation Finset.univ x y + if a = b then 0 else 2 * zeroCount x y := by
  classical
  unfold separation zeroCount
  rw [sum_word_cons]
  simp_rw [distance_cons, ternary_distance_step]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  by_cases h : a = b
  · simp [h]
  · simp only [h, ite_false]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : distance x z = distance y z <;> simp [h, hz]

private theorem weak_full_bound : ∀ d : ℕ, ∀ x y : Word d, x ≠ y →
    kappa d + 2 * (distance x y - 1) ≤ separation Finset.univ x y := by
  intro d
  induction d with
  | zero =>
      intro x y hxy
      exact (hxy (Subsingleton.elim _ _)).elim
  | succ n ih =>
      intro x y hxy
      let a := x 0
      let b := y 0
      let u := Fin.tail x
      let v := Fin.tail y
      have hx : Fin.cons a u = x := Fin.cons_self_tail x
      have hy : Fin.cons b v = y := Fin.cons_self_tail y
      rw [← hx, ← hy, distance_cons, full_separation_cons]
      by_cases huv : u = v
      · have hab : a ≠ b := by
          intro hab
          exact hxy (by rw [← hx, ← hy, huv, hab])
        have hz : zeroCount u v = 3 ^ n := by simp [huv, zeroCount]
        simp only [ite_eq_right hab]
        rw [hz]
        simp [huv, distance_self, kappa, separation]
      · have hn : 1 ≤ n := (distance_pos huv).trans (distance_le u v)
        have hp := ih u v huv
        have hr := distance_pos huv
        have hz := zeroCount_pos u v
        have hk : kappa (n + 1) = 3 * kappa n := by
          have hp : 3 ^ n = 3 ^ (n - 1) * 3 := by
            calc
              3 ^ n = 3 ^ ((n - 1) + 1) := congrArg (fun m => 3 ^ m) (by omega)
              _ = _ := pow_succ 3 (n - 1)
          unfold kappa
          rw [show n + 1 - 1 = n by omega, hp]
          omega
        rw [hk]
        by_cases hab : a = b <;> simp only [hab, ite_true, ite_false, add_zero]
        · omega
        · omega

/-- In dimension at least three the full universe gains at least six for
    every extra differing coordinate. This is the uniform escape estimate. -/
theorem full_separation_bound {d : ℕ} (hd : 3 ≤ d) (x y : Word d) (hxy : x ≠ y) :
    kappa d + 6 * (distance x y - 1) ≤ separation Finset.univ x y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  let a := x 0
  let b := y 0
  let u := Fin.tail x
  let v := Fin.tail y
  have hx : Fin.cons a u = x := Fin.cons_self_tail x
  have hy : Fin.cons b v = y := Fin.cons_self_tail y
  rw [← hx, ← hy, distance_cons, full_separation_cons]
  by_cases huv : u = v
  · have hab : a ≠ b := by
      intro hab
      exact hxy (by rw [← hx, ← hy, huv, hab])
    have hz : zeroCount u v = 3 ^ n := by simp [huv, zeroCount]
    simp only [ite_eq_right hab]
    rw [hz]
    simp [huv, distance_self, kappa, separation]
  · have hn : 2 ≤ n := by omega
    have hp := weak_full_bound n u v huv
    have hr := distance_pos huv
    have hz := zeroCount_three hn u v
    have hk : kappa (n + 1) = 3 * kappa n := by
      have hp : 3 ^ n = 3 ^ (n - 1) * 3 := by
        calc
          3 ^ n = 3 ^ ((n - 1) + 1) := congrArg (fun m => 3 ^ m) (by omega)
          _ = _ := pow_succ 3 (n - 1)
      unfold kappa
      rw [show n + 1 - 1 = n by omega, hp]
      omega
    rw [hk]
    by_cases hab : a = b <;> simp only [hab, ite_true, ite_false, add_zero]
    · omega
    · omega

private theorem adjacent_separation {d : ℕ} (i : Fin d) (a b : Fin 3) (hab : a ≠ b)
    (T : Finset (Word d)) :
    separation T (Function.update (constantWord 0) i a)
        (Function.update (constantWord 0) i b) =
      (T.filter (fun z => z i = a ∨ z i = b)).card := by
  classical
  have he (z : Word d) :
      distanceExcept i (Function.update (constantWord 0) i a) z =
        distanceExcept i (Function.update (constantWord 0) i b) z := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp [Function.update_of_ne hji]
  have hpoint (z : Word d) :
      Nat.dist (distance (Function.update (constantWord 0) i a) z)
          (distance (Function.update (constantWord 0) i b) z) =
        (if z i = a ∨ z i = b then 1 else 0) := by
    rw [distance_eq_update_sum i, distance_eq_update_sum i, he]
    by_cases hza : z i = a <;> by_cases hzb : z i = b
    · exact (hab (hza.symm.trans hzb)).elim
    · simp [hza, hab, hab.symm, Nat.dist]
    · simp [hzb, hab, hab.symm, Nat.dist]
    · simp [hza, hzb, Ne.symm hza, Ne.symm hzb]
  simp only [separation]
  simp_rw [hpoint]
  exact (Finset.card_filter _ _).symm

private theorem adjacent_pair_bound {d : ℕ} (hd : 1 ≤ d) (T : Finset (Word d))
    {t : ℕ} (hT : ∀ a b : Fin 3, a ≠ b →
      separation T (Function.update (constantWord 0) ⟨0, by omega⟩ a)
        (Function.update (constantWord 0) ⟨0, by omega⟩ b) ≤ t) :
    T.card ≤ omittedCapacity t := by
  classical
  let i : Fin d := ⟨0, by omega⟩
  have h01 := hT 0 1 (by decide)
  have h02 := hT 0 2 (by decide)
  have h12 := hT 1 2 (by decide)
  rw [adjacent_separation i 0 1 (by decide)] at h01
  rw [adjacent_separation i 0 2 (by decide)] at h02
  rw [adjacent_separation i 1 2 (by decide)] at h12
  have htotal :
      (T.filter (fun z => z i = 0 ∨ z i = 1)).card +
      (T.filter (fun z => z i = 0 ∨ z i = 2)).card +
      (T.filter (fun z => z i = 1 ∨ z i = 2)).card = 2 * T.card := by
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _z ∈ T, (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro z _
        generalize z i = v
        fin_cases v <;> simp
      _ = _ := by simp [mul_comm]
  unfold omittedCapacity
  omega

private theorem univ_coordinate_card {d : ℕ} (i : Fin d)
    (a b : Fin 3) (hab : a ≠ b) :
    ((Finset.univ : Finset (Word d)).filter (fun z => z i = a ∨ z i = b)).card =
      2 * 3 ^ (d - 1) := by
  classical
  have hdis : Disjoint
      ((Finset.univ : Finset (Word d)).filter (fun z => z i = a))
      ((Finset.univ : Finset (Word d)).filter (fun z => z i = b)) := by
    rw [Finset.disjoint_left]
    intro z hza hzb
    exact hab ((Finset.mem_filter.mp hza).2.symm.trans (Finset.mem_filter.mp hzb).2)
  rw [Finset.filter_or, Finset.card_union_of_disjoint hdis]
  have hc (c : Fin 3) :
      ((Finset.univ : Finset (Word d)).filter (fun z => z i = c)).card =
        3 ^ (d - 1) := by
    simpa using Fintype.card_filter_piFinset_const
      (Finset.univ : Finset (Fin 3)) i c
  rw [hc a, hc b]
  omega

private theorem complement_omitted_bound {d : ℕ} (hd : 2 ≤ d) (t : ℕ)
    (S : Finset (Word d))
    (hS : IsWeakResolving d (kappa d - t) S)
    (hkt : t ≤ kappa d) :
    (complement S).card ≤ omittedCapacity t := by
  apply adjacent_pair_bound (by omega) (complement S)
  intro a b hab
  let i : Fin d := ⟨0, by omega⟩
  let x := Function.update (constantWord 0) i a
  let y := Function.update (constantWord 0) i b
  have hxy : x ≠ y := by
    intro h
    have hh := congrArg (fun z => z i) h
    exact hab (by simpa [x, y] using hh)
  change separation (complement S) x y ≤ t
  have hs := hS x y hxy
  have hc := separation_complement S x y
  have hu := adjacent_separation i a b hab (Finset.univ : Finset (Word d))
  have hcard := univ_coordinate_card i a b hab
  rw [hu, hcard] at hc
  simp only [kappa] at hs hkt
  omega

private theorem orbit_card {d : ℕ} (hd : 1 ≤ d) (x : Word d) : (orbit x).card = 3 := by
  classical
  let i : Fin d := ⟨0, by omega⟩
  have h01 : x ≠ fun j => ⟨((x j).val + 1) % 3, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (congr_fun h i)
    dsimp only at hv
    have hx := (x i).isLt
    omega
  have h02 : x ≠ fun j => ⟨((x j).val + 2) % 3, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (congr_fun h i)
    dsimp only at hv
    have hx := (x i).isLt
    omega
  have h12 : (fun j => ⟨((x j).val + 1) % 3, by omega⟩ : Word d) ≠
      fun j => ⟨((x j).val + 2) % 3, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (congr_fun h i)
    dsimp only at hv
    have hx := (x i).isLt
    omega
  simp [orbit, h01, h02, h12]

private theorem orbit_disjoint_constant_mixed {d : ℕ} (hd : 2 ≤ d) :
    Disjoint (orbit (constantWord (d := d) 0)) (orbit mixedWord) := by
  classical
  rw [Finset.disjoint_left]
  intro z hz0 hz1
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hz0 hz1
  rcases hz0 with rfl | rfl | rfl <;> rcases hz1 with h | h | h
  all_goals
    have h0 := congrArg Fin.val (congr_fun h ⟨0, by omega⟩)
    have h1 := congrArg Fin.val (congr_fun h ⟨1, by omega⟩)
    simp [constantWord, mixedWord] at h0 h1

private theorem baseOmitted_card {d : ℕ} (hd : 2 ≤ d) : (baseOmitted (d := d)).card = 6 := by
  classical
  rw [baseOmitted, Finset.card_union_of_disjoint (orbit_disjoint_constant_mixed hd)]
  rw [orbit_card (by omega) (constantWord 0), orbit_card (by omega) mixedWord]

private theorem extra_not_mem {d : ℕ} (hd : 2 ≤ d) :
    extraWord (d := d) ∉ baseOmitted (d := d) := by
  unfold extraWord baseOmitted orbit
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  intro h
  rcases h with (h | h | h) | (h | h | h)
  all_goals
    have h0 := congrArg Fin.val (congr_fun h ⟨0, by omega⟩)
    have h1 := congrArg Fin.val (congr_fun h ⟨1, by omega⟩)
    simp [constantWord, mixedWord] at h0 h1

private theorem oddOmitted_card {d : ℕ} (hd : 2 ≤ d) : (oddOmitted (d := d)).card = 7 := by
  classical
  simp [oddOmitted, extra_not_mem hd, baseOmitted_card hd]

private theorem dist_sum_le {α : Type*} (s : Finset α) (f g : α → ℕ) :
    Nat.dist (∑ a ∈ s, f a) (∑ a ∈ s, g a) ≤
      ∑ a ∈ s, Nat.dist (f a) (g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have h := Nat.dist.triangle_inequality (f a + ∑ x ∈ s, f x)
        (g a + ∑ x ∈ s, f x) (g a + ∑ x ∈ s, g x)
      rw [Nat.dist_add_add_right, Nat.dist_add_add_left] at h
      calc
        Nat.dist (f a + ∑ x ∈ s, f x) (g a + ∑ x ∈ s, g x) ≤
            Nat.dist (f a) (g a) +
              Nat.dist (∑ x ∈ s, f x) (∑ x ∈ s, g x) := by simpa [add_comm] using h
        _ ≤ Nat.dist (f a) (g a) + ∑ x ∈ s, Nat.dist (f x) (g x) :=
          Nat.add_le_add_left ih _

private theorem orbit_coordinate_bound {d : ℕ} (u : Word d) (i : Fin d)
    (a b : Fin 3) :
    (∑ z ∈ orbit u,
      Nat.dist (if a = z i then 0 else 1) (if b = z i then 0 else 1)) ≤
      2 * (if a = b then 0 else 1) := by
  classical
  have h01 : u ≠ fun j => ⟨((u j).val + 1) % 3, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (congr_fun h i)
    dsimp only at hv
    have hx := (u i).isLt
    omega
  have h02 : u ≠ fun j => ⟨((u j).val + 2) % 3, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (congr_fun h i)
    dsimp only at hv
    have hx := (u i).isLt
    omega
  have h12 : (fun j => ⟨((u j).val + 1) % 3, by omega⟩ : Word d) ≠
      fun j => ⟨((u j).val + 2) % 3, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (congr_fun h i)
    dsimp only at hv
    have hx := (u i).isLt
    omega
  unfold orbit
  rw [Finset.sum_insert (by simp [h01, h02]),
    Finset.sum_insert (by simp [h12]), Finset.sum_singleton]
  generalize hui : u i = c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [hui, Nat.dist]

private theorem orbit_separation_le {d : ℕ} (u x y : Word d) :
    separation (orbit u) x y ≤ 2 * distance x y := by
  classical
  calc
    separation (orbit u) x y ≤
        ∑ z ∈ orbit u, ∑ i : Fin d,
          Nat.dist (if x i = z i then 0 else 1) (if y i = z i then 0 else 1) := by
      apply Finset.sum_le_sum
      intro z hz
      exact dist_sum_le Finset.univ
        (fun i => if x i = z i then 0 else 1)
        (fun i => if y i = z i then 0 else 1)
    _ = ∑ i : Fin d, ∑ z ∈ orbit u,
          Nat.dist (if x i = z i then 0 else 1) (if y i = z i then 0 else 1) := by
      exact Finset.sum_comm
    _ ≤ ∑ i : Fin d, 2 * (if x i = y i then 0 else 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact orbit_coordinate_bound u i (x i) (y i)
    _ = 2 * distance x y := by
      simp [distance, Finset.mul_sum]

private theorem singleton_separation_le {d : ℕ} (z x y : Word d) :
    separation {z} x y ≤ distance x y := by
  have hxy : distance x z ≤ distance x y + distance y z := by
    simpa [distance_eq_hammingDist] using hammingDist_triangle x y z
  have hyx : distance y z ≤ distance x y + distance x z := by
    have := hammingDist_triangle y x z
    simpa [distance_eq_hammingDist, hammingDist_comm] using this
  simp only [separation, Finset.sum_singleton]
  unfold Nat.dist
  omega

private theorem base_separation_le {d : ℕ} (hd : 2 ≤ d) (x y : Word d) :
    separation (baseOmitted (d := d)) x y ≤ 4 * distance x y := by
  have h₁ := orbit_separation_le (constantWord 0) x y
  have h₂ := orbit_separation_le mixedWord x y
  have he : separation (baseOmitted (d := d)) x y =
      separation (orbit (constantWord 0)) x y + separation (orbit mixedWord) x y :=
    Finset.sum_union (orbit_disjoint_constant_mixed hd)
  omega

private theorem odd_separation_le {d : ℕ} (hd : 2 ≤ d) (x y : Word d) :
    separation (oddOmitted (d := d)) x y ≤ 5 * distance x y := by
  have h₁ := base_separation_le hd x y
  have h₂ := singleton_separation_le extraWord x y
  have he : separation (oddOmitted (d := d)) x y =
      Nat.dist (distance x extraWord) (distance y extraWord) +
        separation (baseOmitted (d := d)) x y :=
    Finset.sum_insert (extra_not_mem hd)
  simp only [separation, Finset.sum_singleton] at h₂
  omega

private theorem base_complement_resolves {d : ℕ} (hd : 3 ≤ d) :
    IsWeakResolving d (kappa d - 4) (complement (baseOmitted (d := d))) := by
  intro x y hxy
  have hf := full_separation_bound hd x y hxy
  have hl := base_separation_le (by omega : 2 ≤ d) x y
  have hc := separation_complement (baseOmitted (d := d)) x y
  have hr := distance_pos hxy
  omega

private theorem odd_complement_resolves {d : ℕ} (hd : 3 ≤ d) :
    IsWeakResolving d (kappa d - 5) (complement (oddOmitted (d := d))) := by
  intro x y hxy
  have hf := full_separation_bound hd x y hxy
  have hl := odd_separation_le (by omega : 2 ≤ d) x y
  have hc := separation_complement (oddOmitted (d := d)) x y
  have hr := distance_pos hxy
  omega

/- Published two-dimensional boundary values, used only to establish the
   exceptional line and the leastness of the uniform threshold. -/
private def word2 (a b : Fin 3) : Word 2 := fun i => if i = 0 then a else b

private theorem distance_two (x y : Word 2) :
    distance x y = (if x 0 = y 0 then 0 else 1) +
      (if x 1 = y 1 then 0 else 1) := by
  simp [distance, Fin.sum_univ_succ]

private theorem coordinate_recover (a b p q : Fin 3) (hpq : p ≠ q) (s t : ℕ)
    (hp : s + (if a = p then 0 else 1) = t + (if b = p then 0 else 1))
    (hq : s + (if a = q then 0 else 1) = t + (if b = q then 0 else 1)) : a = b := by
  fin_cases a <;> fin_cases b <;> fin_cases p <;> fin_cases q <;> simp_all <;> omega

private theorem l_separation (a b c e : Fin 3) (hab : a ≠ b) (hce : c ≠ e)
    (x y : Word 2) (hxy : x ≠ y) :
    1 ≤ Nat.dist (distance x (word2 a c)) (distance y (word2 a c)) +
      Nat.dist (distance x (word2 a e)) (distance y (word2 a e)) +
      Nat.dist (distance x (word2 b c)) (distance y (word2 b c)) := by
  by_contra hn
  have h0 : distance x (word2 a c) = distance y (word2 a c) :=
    Nat.eq_of_dist_eq_zero (by omega)
  have h1 : distance x (word2 a e) = distance y (word2 a e) :=
    Nat.eq_of_dist_eq_zero (by omega)
  have h2 : distance x (word2 b c) = distance y (word2 b c) :=
    Nat.eq_of_dist_eq_zero (by omega)
  have hx0 : x 0 = y 0 := coordinate_recover (x 0) (y 0) a b hab
    (if x 1 = c then 0 else 1) (if y 1 = c then 0 else 1)
    (by simpa [distance_two, word2, add_comm] using h0)
    (by simpa [distance_two, word2, add_comm] using h2)
  have hx1 : x 1 = y 1 := coordinate_recover (x 1) (y 1) c e hce
    (if x 0 = a then 0 else 1) (if y 0 = a then 0 else 1)
    (by simpa [distance_two, word2] using h0)
    (by simpa [distance_two, word2] using h1)
  apply hxy
  funext i
  fin_cases i <;> assumption

private def d2S_four : Finset (Word 2) :=
  {word2 0 0, word2 0 1, word2 1 0, word2 1 1}

private def d2S_five : Finset (Word 2) :=
  {word2 0 0, word2 0 1, word2 1 0}

private theorem d2S_four_card : d2S_four.card = 4 := by decide
private theorem d2S_five_card : d2S_five.card = 3 := by decide

private theorem d2S_five_resolves : IsWeakResolving 2 1 d2S_five := by
  intro x y hxy
  have hp := l_separation 0 1 0 1 (by decide) (by decide) x y hxy
  simpa [separation, d2S_five, show word2 0 0 ≠ word2 0 1 by decide,
    show word2 0 0 ≠ word2 1 0 by decide,
    show word2 0 1 ≠ word2 1 0 by decide, add_assoc] using hp

private theorem d2S_four_resolves : IsWeakResolving 2 2 d2S_four := by
  intro x y hxy
  have h0 := l_separation 0 1 0 1 (by decide) (by decide) x y hxy
  have h1 := l_separation 0 1 1 0 (by decide) (by decide) x y hxy
  have h2 := l_separation 1 0 0 1 (by decide) (by decide) x y hxy
  have h3 := l_separation 1 0 1 0 (by decide) (by decide) x y hxy
  have he : separation d2S_four x y =
      Nat.dist (distance x (word2 0 0)) (distance y (word2 0 0)) +
      Nat.dist (distance x (word2 0 1)) (distance y (word2 0 1)) +
      Nat.dist (distance x (word2 1 0)) (distance y (word2 1 0)) +
      Nat.dist (distance x (word2 1 1)) (distance y (word2 1 1)) := by
    simp [separation, d2S_four, show word2 0 0 ≠ word2 0 1 by decide,
      show word2 0 0 ≠ word2 1 0 by decide, show word2 0 0 ≠ word2 1 1 by decide,
      show word2 0 1 ≠ word2 1 0 by decide, show word2 0 1 ≠ word2 1 1 by decide,
      show word2 1 0 ≠ word2 1 1 by decide, add_assoc]
  omega

private theorem two_landmarks_fail (a b : Word 2) :
    ∃ x y : Word 2, x ≠ y ∧ distance x a = distance y a ∧
      distance x b = distance y b := by
  by_cases h0 : a 0 = b 0
  · let c : Fin 3 := ⟨((a 0).val + 1) % 3, by omega⟩
    let e : Fin 3 := ⟨((a 0).val + 2) % 3, by omega⟩
    have hn : c ≠ e ∧ c ≠ a 0 ∧ e ≠ a 0 := by
      have ha := (a 0).isLt
      dsimp [c, e]
      constructor
      · intro h; have := congrArg Fin.val h; dsimp only at this; omega
      · constructor <;> intro h <;> have := congrArg Fin.val h <;> dsimp only at this <;> omega
    refine ⟨word2 c 0, word2 e 0, ?_, ?_, ?_⟩
    · intro h; exact hn.1 (by simpa [word2] using congr_fun h 0)
    · simp [distance_two, word2, hn.2.1, hn.2.2]
    · simp [distance_two, word2, ← h0, hn.2.1, hn.2.2]
  · by_cases h1 : a 1 = b 1
    · let c : Fin 3 := ⟨((a 1).val + 1) % 3, by omega⟩
      let e : Fin 3 := ⟨((a 1).val + 2) % 3, by omega⟩
      have hn : c ≠ e ∧ c ≠ a 1 ∧ e ≠ a 1 := by
        have ha := (a 1).isLt
        dsimp [c, e]
        constructor
        · intro h; have := congrArg Fin.val h; dsimp only at this; omega
        · constructor <;> intro h <;> have := congrArg Fin.val h <;> dsimp only at this <;> omega
      refine ⟨word2 0 c, word2 0 e, ?_, ?_, ?_⟩
      · intro h; exact hn.1 (by simpa [word2] using congr_fun h 1)
      · simp [distance_two, word2, hn.2.1, hn.2.2]
      · simp [distance_two, word2, ← h1, hn.2.1, hn.2.2]
    · refine ⟨word2 (a 0) (b 1), word2 (b 0) (a 1), ?_, ?_, ?_⟩
      · intro h; exact h0 (by simpa [word2] using congr_fun h 0)
      · simp [distance_two, word2, h0, h1, Ne.symm h0, Ne.symm h1]
      · simp [distance_two, word2, h0, h1, Ne.symm h0, Ne.symm h1]

private theorem d2_lower_five (S : Finset (Word 2)) (hS : IsWeakResolving 2 1 S) :
    3 ≤ S.card := by
  classical
  by_contra hn
  have hs : S.card ≤ 2 := by omega
  obtain ⟨a, b, hsub⟩ : ∃ a b : Word 2, S ⊆ {a, b} := by
    by_cases h1 : S.card ≤ 1
    · obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp h1
      exact ⟨a, a, by simpa using ha⟩
    · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp (by omega : S.card = 2)
      exact ⟨a, b, Finset.Subset.refl _⟩
  obtain ⟨x, y, hxy, ha, hb⟩ := two_landmarks_fail a b
  have he : separation S x y = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    have hz' := hsub hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
    rcases hz' with rfl | rfl <;> simp [ha, hb]
  have := hS x y hxy
  omega

private theorem d2_lower_four (S : Finset (Word 2)) (hS : IsWeakResolving 2 2 S) :
    4 ≤ S.card := by
  classical
  by_contra hn
  have hcard : S.card ≤ 3 := by omega
  have hcount (i : Fin 2) (a : Fin 3) : (S.filter (fun z => z i = a)).card ≤ 1 := by
    let b : Fin 3 := ⟨(a.val + 1) % 3, by omega⟩
    let c : Fin 3 := ⟨(a.val + 2) % 3, by omega⟩
    have hbc : b ≠ c := by
      intro h; have := congrArg Fin.val h; have := a.isLt; dsimp [b, c] at *; omega
    have hxy : Function.update (constantWord 0) i b ≠
        Function.update (constantWord 0) i c := by
      intro h; exact hbc (by simpa using congr_fun h i)
    have hp := hS _ _ hxy
    rw [adjacent_separation i b c hbc] at hp
    have he : (S.filter (fun z => z i = a)).card +
        (S.filter (fun z => z i = b ∨ z i = c)).card = S.card := by
      simp only [Finset.card_filter]
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ _z ∈ S, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro z _
          generalize z i = v
          fin_cases a <;> fin_cases v <;> simp [b, c]
        _ = _ := by simp
    omega
  have hi (i : Fin 2) {z w : Word 2} (hz : z ∈ S) (hw : w ∈ S)
      (he : z i = w i) : z = w :=
    Finset.card_le_one.mp (hcount i (z i)) z (by simp [hz]) w (by simp [hw, he])
  have hthree : S.card = 3 := by
    have := d2_lower_five S (by intro x y hxy; have := hS x y hxy; omega)
    omega
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hthree
  have ha : a ∈ S := by simp [hset]
  have hb : b ∈ S := by simp [hset]
  have hc : c ∈ S := by simp [hset]
  have hab0 : a 0 ≠ b 0 := fun h => hab (hi 0 ha hb h)
  have hab1 : a 1 ≠ b 1 := fun h => hab (hi 1 ha hb h)
  have hac0 : a 0 ≠ c 0 := fun h => hac (hi 0 ha hc h)
  have hac1 : a 1 ≠ c 1 := fun h => hac (hi 1 ha hc h)
  have hbc0 : b 0 ≠ c 0 := fun h => hbc (hi 0 hb hc h)
  have hbc1 : b 1 ≠ c 1 := fun h => hbc (hi 1 hb hc h)
  let x := word2 (a 0) (b 1)
  let y := word2 (b 0) (a 1)
  have hxy : x ≠ y := by
    intro h; exact hab0 (by simpa [x, y, word2] using congr_fun h 0)
  have he : separation S x y = 0 := by
    simp [hset, separation, hab, hac, hbc, x, y, distance_two, word2,
      hab0, hab1, Ne.symm hab0, Ne.symm hab1, hac0, hac1, hbc0, hbc1, Nat.dist]
  have := hS x y hxy
  omega

theorem d2_metricDimension_four : metricDimension 2 (kappa 2 - 4) = 4 := by
  have hk : kappa 2 - 4 = 2 := by decide
  rw [hk]
  apply le_antisymm
  · exact csInf_le' ⟨d2S_four, d2S_four_resolves, d2S_four_card⟩
  · apply le_csInf
    · exact ⟨4, d2S_four, d2S_four_resolves, d2S_four_card⟩
    · rintro n ⟨S, hS, rfl⟩
      exact d2_lower_four S hS

theorem d2_metricDimension_five : metricDimension 2 (kappa 2 - 5) = 3 := by
  have hk : kappa 2 - 5 = 1 := by decide
  rw [hk]
  apply le_antisymm
  · exact csInf_le' ⟨d2S_five, d2S_five_resolves, d2S_five_card⟩
  · apply le_csInf
    · exact ⟨3, d2S_five, d2S_five_resolves, d2S_five_card⟩
    · rintro n ⟨S, hS, rfl⟩
      exact d2_lower_five S hS

private theorem deficit_feasible {d : ℕ} (hd : 2 ≤ d) : 5 < kappa d := by
  have hp : 3 ^ 1 ≤ 3 ^ (d - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hp
  unfold kappa
  omega

private theorem exact_four {d : ℕ} (hd : 3 ≤ d) :
    metricDimension d (kappa d - 4) = 3 ^ d - 6 := by
  classical
  have hc := complement_card (baseOmitted (d := d))
  have ho := baseOmitted_card (by omega : 2 ≤ d)
  have hr := base_complement_resolves hd
  have hw : (complement (baseOmitted (d := d))).card = 3 ^ d - 6 := by omega
  apply le_antisymm
  · exact csInf_le' ⟨complement (baseOmitted (d := d)), hr, hw⟩
  · apply le_csInf
    · exact ⟨3 ^ d - 6, complement (baseOmitted (d := d)), hr, hw⟩
    · rintro n ⟨S, hS, rfl⟩
      have ht := complement_omitted_bound (by omega : 2 ≤ d) 4 S hS
        (by have := deficit_feasible (by omega : 2 ≤ d); omega)
      have hcs := complement_card S
      norm_num [omittedCapacity] at ht
      omega

private theorem exact_five {d : ℕ} (hd : 3 ≤ d) :
    metricDimension d (kappa d - 5) = 3 ^ d - 7 := by
  classical
  let T := oddOmitted (d := d)
  have hc := complement_card T
  have ho : T.card = 7 := oddOmitted_card (by omega : 2 ≤ d)
  have hr : IsWeakResolving d (kappa d - 5) (complement T) := odd_complement_resolves hd
  have hw : (complement T).card = 3 ^ d - 7 := by omega
  apply le_antisymm
  · exact csInf_le' ⟨complement T, hr, hw⟩
  · apply le_csInf
    · exact ⟨3 ^ d - 7, complement T, hr, hw⟩
    · rintro n ⟨S, hS, rfl⟩
      have ht := complement_omitted_bound (by omega : 2 ≤ d) 5 S hS
        (by have := deficit_feasible (by omega : 2 ≤ d); omega)
      have hcs := complement_card S
      norm_num [omittedCapacity] at ht
      omega

/-- Exact dimensions for every requested dimension, with the genuine d=2 boundary. -/
theorem result (d t : ℕ) (hd : 2 ≤ d) (ht : t = 4 ∨ t = 5) :
    metricDimension d (kappa d - t) =
      if d = 2 then (if t = 4 then 4 else 3) else 3 ^ d - omittedCapacity t := by
  rcases ht with rfl | rfl
  · by_cases h : d = 2
    · simpa [h] using d2_metricDimension_four
    · simpa [h, omittedCapacity] using exact_four (by omega : 3 ≤ d)
  · by_cases h : d = 2
    · simpa [h] using d2_metricDimension_five
    · simpa [h, omittedCapacity] using exact_five (by omega : 3 ≤ d)

/-- Maximum omitted sets, including explicit attainers and universal sharpness. -/
theorem omitted_maximum (d t : ℕ) (hd : 2 ≤ d) (ht : t = 4 ∨ t = 5) :
    let M := if d = 2 then (if t = 4 then 5 else 6) else omittedCapacity t
    (∃ T : Finset (Word d), T.card = M ∧
      IsWeakResolving d (kappa d - t) (complement T)) ∧
    ∀ T : Finset (Word d), IsWeakResolving d (kappa d - t) (complement T) →
      T.card ≤ M := by
  classical
  have hcc (T : Finset (Word d)) : complement (complement T) = T := by
    ext z
    simp [complement]
  dsimp
  constructor
  · by_cases h : d = 2
    · subst d
      rcases ht with rfl | rfl
      · refine ⟨complement d2S_four, ?_, ?_⟩
        · have hc := complement_card d2S_four
          have hs := d2S_four_card
          simpa using (show (complement d2S_four).card = 5 by omega)
        · simpa [hcc, kappa] using d2S_four_resolves
      · refine ⟨complement d2S_five, ?_, ?_⟩
        · have hc := complement_card d2S_five
          have hs := d2S_five_card
          simpa using (show (complement d2S_five).card = 6 by omega)
        · simpa [hcc, kappa] using d2S_five_resolves
    · rcases ht with rfl | rfl
      · refine ⟨baseOmitted, ?_, base_complement_resolves (by omega)⟩
        simpa [h, omittedCapacity] using baseOmitted_card (by omega : 2 ≤ d)
      · refine ⟨oddOmitted, ?_, odd_complement_resolves (by omega)⟩
        simpa [h, omittedCapacity] using oddOmitted_card (by omega : 2 ≤ d)
  · intro T hT
    have hm := result d t hd ht
    have hmin : metricDimension d (kappa d - t) ≤ (complement T).card :=
      csInf_le' ⟨complement T, hT, rfl⟩
    have hc := complement_card T
    by_cases h : d = 2
    · subst d
      rcases ht with rfl | rfl <;> norm_num at hm ⊢ <;> omega
    · have ht' := complement_omitted_bound hd t (complement T) hT
        (by rcases ht with rfl | rfl <;> have := deficit_feasible hd <;> omega)
      simpa [h, hcc T] using ht'

/-- The least eventual stabilization dimension is three for each deficit. -/
theorem least_threshold (t : ℕ) (ht : t = 4 ∨ t = 5) :
    IsLeast {D : ℕ | ∀ d, 2 ≤ d → D ≤ d →
      metricDimension d (kappa d - t) = 3 ^ d - omittedCapacity t} 3 := by
  constructor
  · intro d _ hd
    have he := result d t (by omega) ht
    simpa [show d ≠ 2 by omega] using he
  · intro D h
    by_contra hn
    have he := h 2 (by decide) (by omega)
    have hb := result 2 t (by decide) ht
    rcases ht with rfl | rfl <;> norm_num [omittedCapacity] at he hb <;> omega

end D5.S3.Combinatorics.Hamming.TernaryWeakMetricStability
