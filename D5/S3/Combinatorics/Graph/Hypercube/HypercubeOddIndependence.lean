/- GID: D5/S3/Combinatorics/Graph/Hypercube/HypercubeOddIndependence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/HypercubeOddIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd independent sets in Boolean cubes via parity and syndrome classes. -/

import D5.S3.Combinatorics.Graph.HypercubeSubQuorum
import Mathlib.Combinatorics.Pigeonhole

/-! Odd independence via a smallest even-parity syndrome fiber. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Hypercube.HypercubeOddIndependence

open scoped BigOperators Classical
open Hypercube HypercubeSubQuorum

/-- Independence with the zero-or-odd alternative at every external vertex. -/
def IsOddIndependent {n : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, ¬ (hypercube n).Adj x y) ∧
    ∀ x ∉ S, ((hypercube n).neighborFinset x ∩ S).card = 0 ∨
      Odd ((hypercube n).neighborFinset x ∩ S).card

/-- The actual bounded finite maximum of odd-independent cardinalities. -/
noncomputable def oddIndependenceNumber (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => ∃ S : Finset (Fin n → Bool), IsOddIndependent S ∧ S.card = m)
    (2 ^ n)

private def flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

private theorem flip_adj {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (hypercube n).Adj x (flip x i) := by
  change (Finset.univ.filter (fun j => x j ≠ flip x i j)).card = 1
  have h : Finset.univ.filter (fun j => x j ≠ flip x i j) = {i} := by
    apply Finset.ext
    intro j
    rw [Finset.mem_filter, Finset.mem_singleton]
    by_cases hj : j = i
    · subst j; simp [flip]
    · simp [flip, hj]
  simp [h]

private theorem flip_injective {n : ℕ} (x : Fin n → Bool) :
    Function.Injective (flip x) := by
  intro i j hij
  by_contra hne
  have h := congrFun hij i
  simp [flip, Function.update_of_ne hne] at h

private theorem flip_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (fun x : Fin n → Bool => flip x i) := by
  intro x
  funext j
  by_cases h : j = i
  · subst j; simp [flip]
  · simp [flip, h]

private theorem neighbors_eq_image {n : ℕ} (x : Fin n → Bool) :
    (hypercube n).neighborFinset x = Finset.univ.image (flip x) := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    simpa only [SimpleGraph.mem_neighborFinset] using flip_adj x i
  · rw [Finset.card_image_of_injective _ (flip_injective x)]
    simp [(hypercube_regular n).degree_eq]

private theorem flip_parity {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    cubeParity (flip x i) = !cubeParity x := by
  have h := cubeParity_ne_of_adj (flip_adj x i)
  cases hx : cubeParity x <;> cases hy : cubeParity (flip x i) <;> simp_all

private theorem parity_card {n : ℕ} (hn : 0 < n) :
    2 * (Finset.univ.filter (fun x : Fin n → Bool => cubeParity x = false)).card = 2 ^ n := by
  let E := Finset.univ.filter (fun x : Fin n → Bool => cubeParity x = false)
  let O := Finset.univ.filter (fun x : Fin n → Bool => cubeParity x = true)
  let i : Fin n := ⟨0, hn⟩
  have himage : E.image (fun x => flip x i) = O := by
    ext x
    simp only [Finset.mem_image, E, O, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp [flip_parity, hy]
    · intro hx
      refine ⟨flip x i, by simp [flip_parity, hx], flip_involutive i x⟩
  have hcard : E.card = O.card := by
    rw [← himage, Finset.card_image_of_injective _ (flip_involutive i).injective]
  have hunion : E ∪ O = Finset.univ := by
    ext x
    cases hx : cubeParity x <;> simp [E, O, hx]
  have hdisj : Disjoint E O := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [E, O, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    simp_all
  have hsum := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hsum
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hsum
  change 2 * E.card = 2 ^ n
  omega

private theorem independent_card_le {n : ℕ} (hn : 0 < n)
    (S : Finset (Fin n → Bool))
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ (hypercube n).Adj x y) :
    2 * S.card ≤ 2 ^ n := by
  let i : Fin n := ⟨0, hn⟩
  let T := S.image (fun x => flip x i)
  have hcard : T.card = S.card :=
    Finset.card_image_of_injective _ (flip_involutive i).injective
  have hdisj : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxt
    exact hS y hy (flip y i) hx (flip_adj y i)
  have hle := Finset.card_le_card (Finset.subset_univ (S ∪ T))
  rw [Finset.card_union_of_disjoint hdisj, hcard] at hle
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hle
  omega

private def syndrome {n k : ℕ} (label : Fin n → (Fin k → Bool))
    (x : Fin n → Bool) : Fin k → Bool :=
  ∑ i, if x i then label i else 0

private theorem check_self {k : ℕ} (s : Fin k → Bool) : s + s = 0 := by
  funext j
  exact Bool.xor_self (s j)

private theorem syndrome_flip {n k : ℕ} (label : Fin n → (Fin k → Bool))
    (x : Fin n → Bool) (i : Fin n) :
    syndrome label (flip x i) = syndrome label x + label i := by
  classical
  let R := ∑ j ∈ Finset.univ.erase i, if x j then label j else 0
  have h1 : syndrome label x = (if x i then label i else 0) + R :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hsum : (∑ j ∈ Finset.univ.erase i, if flip x i j then label j else 0) = R := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [flip, Function.update_of_ne (Finset.mem_erase.mp hj).1]
  have h2 : syndrome label (flip x i) = (if !x i then label i else 0) + R := by
    unfold syndrome
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hsum]
    simp only [flip, Function.update_self]
  rw [h1, h2]
  cases hx : x i <;> simp [add_comm, ← add_assoc, check_self]

private theorem syndrome_eq_iff {k : ℕ} (s a b : Fin k → Bool) :
    s + b = a ↔ b = s + a := by
  constructor
  · intro h
    rw [← h, ← add_assoc, check_self, zero_add]
  · intro h
    rw [h, ← add_assoc, check_self, zero_add]

private def classComplement {n k : ℕ} (label : Fin n → (Fin k → Bool))
    (a : Fin k → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun x => cubeParity x = false ∧ syndrome label x ≠ a

private theorem classComplement_oddIndependent {n k : ℕ} (hn : Even n)
    (label : Fin n → (Fin k → Bool))
    (hlabel : ∀ a, Odd (Finset.univ.filter (fun i => label i = a)).card)
    (a : Fin k → Bool) : IsOddIndependent (classComplement label a) := by
  constructor
  · intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2.1
    have hy' := (Finset.mem_filter.mp hy).2.1
    exact cubeParity_ne_of_adj hxy (hx'.trans hy'.symm)
  · intro x hx
    by_cases hp : cubeParity x = false
    · left
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨hxy, hyS⟩ := Finset.mem_inter.mp hy
      exact cubeParity_ne_of_adj (by simpa only [SimpleGraph.mem_neighborFinset] using hxy)
        (hp.trans (Finset.mem_filter.mp hyS).2.1.symm)
    · right
      have hp' : cubeParity x = true := by cases h : cubeParity x <;> simp_all
      have hfilter : ((hypercube n).neighborFinset x ∩ classComplement label a) =
          (Finset.univ.filter (fun i => label i ≠ syndrome label x + a)).image (flip x) := by
        rw [neighbors_eq_image]
        ext y
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_filter]
        constructor
        · rintro ⟨⟨i, rfl⟩, hi⟩
          refine ⟨i, ?_, rfl⟩
          have hs := (Finset.mem_filter.mp hi).2.2
          rw [syndrome_flip] at hs
          exact fun h => hs ((syndrome_eq_iff _ _ _).mpr h)
        · rintro ⟨i, hi, rfl⟩
          refine ⟨⟨i, rfl⟩, ?_⟩
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          refine ⟨by simp [flip_parity, hp'], ?_⟩
          rw [syndrome_flip]
          exact fun h => hi ((syndrome_eq_iff _ _ _).mp h)
      rw [hfilter, Finset.card_image_of_injective _ (flip_injective x)]
      have hc := hlabel (syndrome label x + a)
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun i => label i = syndrome label x + a)
      simp only [Finset.card_univ, Fintype.card_fin] at hpartition
      change (Finset.univ.filter (fun i => label i = syndrome label x + a)).card +
        (Finset.univ.filter (fun i => label i ≠ syndrome label x + a)).card = n at hpartition
      obtain ⟨r, hr⟩ := hn
      obtain ⟨s, hs⟩ := hc
      refine ⟨r - s - 1, ?_⟩
      omega

private theorem odd_labels (n k : ℕ) (hk : 0 < k) (hn : Even n) (hkn : 2 ^ k ≤ n) :
    ∃ label : Fin n → (Fin k → Bool),
      ∀ a, Odd (Finset.univ.filter (fun i => label i = a)).card := by
  classical
  let A := Fin k → Bool
  let r := n - 2 ^ k
  let e : Fin n ≃ A ⊕ Fin r := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_fun, Fintype.card_bool, A, r]
    omega)
  let f : A ⊕ Fin r → A := Sum.elim id (fun _ => 0)
  refine ⟨f ∘ e, ?_⟩
  intro a
  have hc : (Finset.univ.filter (fun i : Fin n => f (e i) = a)).card =
      1 + if a = 0 then r else 0 := by
    calc
      _ = ∑ i : Fin n, if f (e i) = a then (1 : ℕ) else 0 := by
        exact (Finset.sum_boole (R := ℕ) (fun i : Fin n => f (e i) = a) Finset.univ).symm
      _ = ∑ j : A ⊕ Fin r, if f j = a then (1 : ℕ) else 0 :=
        e.sum_comp (fun j => if f j = a then (1 : ℕ) else 0)
      _ = 1 + if a = 0 then r else 0 := by
        rw [Fintype.sum_sum_type]
        change (∑ x : A, if x = a then (1 : ℕ) else 0) +
          (∑ _ : Fin r, if (0 : A) = a then (1 : ℕ) else 0) = _
        rw [Fintype.sum_ite_eq' a (fun _ => (1 : ℕ))]
        by_cases ha : a = 0 <;> simp [ha, eq_comm]
  change Odd (Finset.univ.filter (fun i : Fin n => f (e i) = a)).card
  rw [hc]
  by_cases ha : a = 0
  · rw [ite_eq_left ha]
    obtain ⟨t, ht⟩ := hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    refine ⟨t - 2 ^ j, ?_⟩
    dsimp [r]
    rw [pow_succ] at hkn ⊢
    omega
  · simp [ha]

private theorem dense_family (n k : ℕ) (hk : 0 < k) (hn : Even n)
    (hkn : 2 ^ k ≤ n) :
    ∃ S : Finset (Fin n → Bool), IsOddIndependent S ∧
      (2 ^ n : ℝ) * (1 / 2 - 1 / (2 * 2 ^ k)) ≤ (S.card : ℝ) := by
  classical
  have hnpos : 0 < n := lt_of_lt_of_le (pow_pos (by decide) k) hkn
  obtain ⟨label, hlabel⟩ := odd_labels n k hk hn hkn
  let E := Finset.univ.filter (fun x : Fin n → Bool => cubeParity x = false)
  have hmpos : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) k
  have hb : (E.card : ℝ) ≤
      (Finset.univ : Finset (Fin k → Bool)).card • ((E.card : ℝ) / 2 ^ k) := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [mul_div_cancel₀ _ (ne_of_gt hmpos)]
  obtain ⟨a, _, ha⟩ := Finset.exists_card_fiber_le_of_card_le_nsmul
    (s := E) (t := Finset.univ) (f := syndrome label) Finset.univ_nonempty hb
  refine ⟨classComplement label a, classComplement_oddIndependent hn label hlabel a, ?_⟩
  have hfilter : E.filter (fun x => syndrome label x ≠ a) = classComplement label a := by
    apply Finset.ext
    intro x
    simp [E, classComplement]
  have hc := Finset.card_filter_add_card_filter_not (s := E) (fun x => syndrome label x = a)
  rw [hfilter] at hc
  have hc' : ((E.filter (fun x => syndrome label x = a)).card : ℝ) +
      (classComplement label a).card = E.card := by exact_mod_cast hc
  have he : 2 * (E.card : ℝ) = (2 ^ n : ℝ) := by
    exact_mod_cast parity_card hnpos
  calc
    (2 ^ n : ℝ) * (1 / 2 - 1 / (2 * 2 ^ k)) = E.card - (E.card : ℝ) / 2 ^ k := by
      rw [← he]
      field_simp
    _ ≤ (classComplement label a).card := by linarith

private theorem maximum_spec (n : ℕ) :
    ∃ S : Finset (Fin n → Bool), IsOddIndependent S ∧ S.card = oddIndependenceNumber n := by
  unfold oddIndependenceNumber
  apply Nat.findGreatest_spec
    (P := fun m => ∃ S : Finset (Fin n → Bool), IsOddIndependent S ∧ S.card = m)
    (m := 0) (Nat.zero_le _)
  refine ⟨∅, ?_, rfl⟩
  constructor
  · simp
  · intro x _
    left
    simp

private theorem card_le_maximum {n : ℕ} (S : Finset (Fin n → Bool))
    (hS : IsOddIndependent S) : S.card ≤ oddIndependenceNumber n := by
  apply Nat.le_findGreatest
  · simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ S)
  · exact ⟨S, hS, rfl⟩

/-- The odd independence ratio tends to one half through every sufficiently
large even dimension, with the quotient taken in the real numbers. -/
theorem result : ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, ∀ d : ℕ,
    Even d → D ≤ d → |(oddIndependenceNumber d : ℝ) / (2 ^ d : ℝ) - 1 / 2| < ε := by
  intro ε hε
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  let k := j + 1
  refine ⟨2 ^ k, ?_⟩
  intro d hd hkd
  have hdpos : 0 < d := lt_of_lt_of_le (pow_pos (by decide) k) hkd
  have hp : (0 : ℝ) < 2 ^ d := pow_pos (by norm_num) d
  have hm : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) k
  obtain ⟨S, hS, hlower⟩ := dense_family d k (by omega) hd hkd
  have hmax : (S.card : ℝ) ≤ (oddIndependenceNumber d : ℝ) :=
    Nat.cast_le.mpr (card_le_maximum S hS)
  obtain ⟨T, hT, hTcard⟩ := maximum_spec d
  have hupper : 2 * (oddIndependenceNumber d : ℝ) ≤ (2 ^ d : ℝ) := by
    have h := independent_card_le hdpos T hT.1
    rw [hTcard] at h
    exact_mod_cast h
  have hratio : (oddIndependenceNumber d : ℝ) / (2 ^ d : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hp).mpr
    linarith
  have herror : 1 / 2 - (oddIndependenceNumber d : ℝ) / (2 ^ d : ℝ) ≤
      1 / (2 * 2 ^ k) := by
    have hl : (2 ^ d : ℝ) * (1 / 2 - 1 / (2 * 2 ^ k)) ≤
        (oddIndependenceNumber d : ℝ) := hlower.trans hmax
    have hdiv : 1 / 2 - 1 / (2 * 2 ^ k) ≤
        (oddIndependenceNumber d : ℝ) / (2 ^ d : ℝ) :=
      (le_div_iff₀ hp).mpr (by nlinarith [hl])
    linarith
  have herrsmall : (1 : ℝ) / (2 * 2 ^ k) < ε := by
    have hle : (1 : ℝ) / (2 * 2 ^ k) ≤ (1 / 2 : ℝ) ^ j := by
      dsimp [k]
      rw [div_pow, one_pow, pow_succ]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
    exact hle.trans_lt hj
  rw [abs_of_nonpos (sub_nonpos.mpr hratio)]
  linarith

#print axioms result

end D5.S3.Combinatorics.Graph.Hypercube.HypercubeOddIndependence
