/- GID: D5/S3/Combinatorics/Sequenceability/OriginalFiniteOrderSharpness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/OriginalFiniteOrderSharpness
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Finite abelian labels attain the cyclic-order component bound. -/

import D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderComponentBound
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
The cyclic-order component bound is attained by finite abelian label groups.
The construction and proof route are caller supplied. The proof adapts the
Codex finite-binary source, SHA256
89322ebb5d7db149475a93d0a9783d6e9c78ce4ea49dd7761340aa08f85157bf,
which in turn adapts the integer-coordinate source, SHA256
08d642eaa8668bd03e7cd599073a8723cb0d68c733fa8799c9bda778ada3ba59.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness

open scoped Classical BigOperators
open D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering
  (MinimalZeroSupport)
open D5.S3.Combinatorics.Sequenceability.BooleanRowChargeConnectivity
  (supportIntersectionGraph)
open D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderComponentBound
  (q_containing_component_card_lt)

/-- One index for each of the m-1 pairs. -/
abbrev Index (m : ℕ) := Fin (m - 1)

/-- The four cases are q, a_j, the sentinel p, and b_j. -/
abbrev Coordinate (m : ℕ) := Option (Index m) ⊕ Option (Index m)

abbrev WitnessGroup (m : ℕ) := ZMod m × ((Index m → ZMod 2) × ZMod 2)

def q (m : ℕ) : Coordinate m := Sum.inl none
def p (m : ℕ) : Coordinate m := Sum.inr none
def a (m : ℕ) (j : Index m) : Coordinate m := Sum.inl (some j)
def b (m : ℕ) (j : Index m) : Coordinate m := Sum.inr (some j)

def full (m : ℕ) : Finset (Coordinate m) := Finset.univ

/-- The first coordinate records torsion; all remaining coordinates are binary. -/
def label (m : ℕ) : Coordinate m → WitnessGroup m
  | Sum.inl none => (1, (0, 0))
  | Sum.inl (some j) => (0, (Pi.single j 1, 0))
  | Sum.inr none => (0, (0, 1))
  | Sum.inr (some j) => (-1, (-Pi.single j 1, 0))

def triple (m : ℕ) (j : Index m) : Finset (Coordinate m) :=
  {q m, a m j, b m j}

/-- ALL proper original minimal zero supports, rather than selected triples. -/
def supports (m : ℕ) : Finset (Finset (Coordinate m)) := by
  classical
  exact (full m).powerset.filter
    (fun B => B ⊂ full m ∧ MinimalZeroSupport (label m) B)

private lemma label_order (m : ℕ) : addOrderOf (label m (q m)) = m := by
  simp [label, q, Prod.addOrderOf_mk]

private lemma label_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (label m) := by
  have hneg : (-1 : ZMod m) ≠ 0 := by
    intro hz
    have hone : (1 : ZMod m) = 0 := neg_eq_zero.mp hz
    have he : m = 1 := ZMod.one_eq_zero_iff.mp hone
    omega
  intro x y h
  have ht := congrArg (fun z : WitnessGroup m => z.1) h
  have hs := congrArg (fun z : WitnessGroup m => z.2.2) h
  have hf := congrArg (fun z : WitnessGroup m => z.2.1) h
  rcases x with (_ | i) | (_ | i) <;>
    rcases y with (_ | j) | (_ | j)
  · rfl
  · have he := congrFun hf j
    norm_num [label] at he
  · norm_num [label] at hs
  · have he := congrFun hf j
    norm_num [label] at he
  · have he := congrFun hf i
    norm_num [label] at he
  · have hij : i = j := by
      by_contra hij
      have he := congrFun hf i
      norm_num [label, Pi.single_apply, hij] at he
    subst j
    rfl
  · norm_num [label] at hs
  · exact (hneg (by simpa [label] using ht.symm)).elim
  · norm_num [label] at hs
  · norm_num [label] at hs
  · rfl
  · norm_num [label] at hs
  · have he := congrFun hf i
    norm_num [label] at he
  · exact (hneg (by simpa [label] using ht)).elim
  · norm_num [label] at hs
  · have hij : i = j := by
      by_contra hij
      have he := congrFun hf i
      norm_num [label, Pi.single_apply, hij] at he
    subst j
    rfl

private lemma label_nonzero (m : ℕ) (hm : 2 ≤ m) (x : Coordinate m) :
    label m x ≠ 0 := by
  intro h
  rcases x with (_ | j) | (_ | j)
  · have he := congrArg (fun z : WitnessGroup m => z.1) h
    have hmone : m = 1 := ZMod.one_eq_zero_iff.mp (by simpa [label] using he)
    omega
  · have he := congrArg (fun z : WitnessGroup m => z.2.1 j) h
    norm_num [label] at he
  · have he := congrArg (fun z : WitnessGroup m => z.2.2) h
    norm_num [label] at he
  · have he := congrArg (fun z : WitnessGroup m => z.2.1 j) h
    norm_num [label] at he

private lemma coordinate_sum {A : Type*} [AddCommMonoid A]
    (m : ℕ) (C : Finset (Coordinate m)) (h : Coordinate m → A) :
    (∑ x ∈ C, h x) =
      ((if q m ∈ C then h (q m) else 0) +
        ∑ j : Index m, if a m j ∈ C then h (a m j) else 0) +
      ((if p m ∈ C then h (p m) else 0) +
        ∑ j : Index m, if b m j ∈ C then h (b m j) else 0) := by
  classical
  rw [← Finset.sum_ite_mem_eq C h, Fintype.sum_sum_type]
  simp only [Fintype.sum_option, q, p, a, b]
  congr 1

private lemma sentinel_sum (m : ℕ) (C : Finset (Coordinate m)) :
    (∑ x ∈ C, label m x).2.2 = if p m ∈ C then (1 : ZMod 2) else 0 := by
  classical
  calc
    (∑ x ∈ C, label m x).2.2 = ∑ x ∈ C, (label m x).2.2 := by
      simp only [Prod.snd_sum]
    _ = ∑ x ∈ C, if x = p m then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rcases x with (_ | j) | (_ | j) <;> simp [label, p]
    _ = _ := by simp

private lemma free_sum (m : ℕ) (C : Finset (Coordinate m)) (j : Index m) :
    (∑ x ∈ C, label m x).2.1 j =
      (if a m j ∈ C then (1 : ZMod 2) else 0) -
        (if b m j ∈ C then (1 : ZMod 2) else 0) := by
  classical
  calc
    (∑ x ∈ C, label m x).2.1 j = ∑ x ∈ C, (label m x).2.1 j := by
      simp only [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
    _ = ∑ x ∈ C,
        ((if x = a m j then (1 : ZMod 2) else 0) -
          (if x = b m j then (1 : ZMod 2) else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      rcases x with (_ | i) | (_ | i)
      · simp [label, a, b]
      · by_cases hij : i = j
        · subst j
          simp [label, a, b]
        · simp [label, a, b, Pi.single_apply, hij, Ne.symm hij]
      · simp [label, a, b]
      · by_cases hij : i = j
        · subst j
          simp [label, a, b]
        · simp [label, a, b, Pi.single_apply, hij, Ne.symm hij]
    _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq']

private def selectedPairs (m : ℕ) (C : Finset (Coordinate m)) : Finset (Index m) :=
  Finset.univ.filter (fun j => b m j ∈ C)

private lemma torsion_sum (m : ℕ) (C : Finset (Coordinate m)) :
    (∑ x ∈ C, label m x).1 =
      (if q m ∈ C then (1 : ZMod m) else 0) -
        ((selectedPairs m C).card : ZMod m) := by
  classical
  have hn : (∑ j : Index m, if b m j ∈ C then (-1 : ZMod m) else 0) =
      -((selectedPairs m C).card : ZMod m) := by
    calc
      _ = ∑ j : Index m, -(if b m j ∈ C then (1 : ZMod m) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      _ = -(∑ j : Index m, if b m j ∈ C then (1 : ZMod m) else 0) := by
        rw [Finset.sum_neg_distrib]
      _ = _ := by simp only [Finset.sum_boole, selectedPairs]
  rw [Prod.fst_sum, coordinate_sum]
  change
    ((if q m ∈ C then (1 : ZMod m) else 0) +
      (∑ j : Index m, if a m j ∈ C then (0 : ZMod m) else 0)) +
    ((if p m ∈ C then (0 : ZMod m) else 0) +
      ∑ j : Index m, if b m j ∈ C then (-1 : ZMod m) else 0) = _
  simp only [ite_self, Finset.sum_const_zero, add_zero, zero_add, hn,
    sub_eq_add_neg]

private lemma triple_nonempty_zero (m : ℕ) (j : Index m) :
    (triple m j).Nonempty ∧ (∑ x ∈ triple m j, label m x) = 0 := by
  classical
  refine ⟨⟨q m, by simp [triple]⟩, ?_⟩
  apply Prod.ext
  · simp [Prod.fst_sum, triple, q, a, b, label]
  · apply Prod.ext
    · funext i
      simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, triple, q, a, b, label]
    · simp [Prod.snd_sum, triple, q, a, b, label]

/-- Classification of every nonempty zero support, before imposing minimality. -/
private lemma zero_support_iff (m : ℕ) (hm : 2 ≤ m) (C : Finset (Coordinate m)) :
    (C.Nonempty ∧ (∑ x ∈ C, label m x) = 0) ↔
      ∃ j : Index m, C = triple m j := by
  classical
  constructor
  · rintro ⟨hC, hz⟩
    have hp : p m ∉ C := by
      intro hp
      have he := congrArg (fun z : WitnessGroup m => z.2.2) hz
      rw [sentinel_sum] at he
      norm_num [hp] at he
    -- The two off-diagonal membership cases give 1 or -1 in ZMod 2.
    have hbalance (j : Index m) : a m j ∈ C ↔ b m j ∈ C := by
      have he := congrArg (fun z : WitnessGroup m => z.2.1 j) hz
      rw [free_sum] at he
      by_cases ha : a m j ∈ C <;> by_cases hb : b m j ∈ C <;>
        simp_all
    let eps : ℕ := if q m ∈ C then 1 else 0
    have heps : eps < m := by
      dsimp [eps]
      split_ifs <;> omega
    have hklt : (selectedPairs m C).card < m := by
      have hbound := Finset.card_le_univ (selectedPairs m C)
      simp only [Fintype.card_fin] at hbound
      omega
    have hcast : (eps : ZMod m) = ((selectedPairs m C).card : ZMod m) := by
      have he := congrArg (fun z : WitnessGroup m => z.1) hz
      rw [torsion_sum] at he
      have he' : (if q m ∈ C then (1 : ZMod m) else 0) -
          ((selectedPairs m C).card : ZMod m) = 0 := by simpa using he
      have heq := sub_eq_zero.mp he'
      by_cases hq : q m ∈ C <;> simpa [eps, hq] using heq
    have hcount : (selectedPairs m C).card = eps := by
      have he := congrArg ZMod.val hcast
      simpa only [ZMod.val_natCast_of_lt heps, ZMod.val_natCast_of_lt hklt]
        using he.symm
    have hq : q m ∈ C := by
      by_contra hq
      have hJ : selectedPairs m C = ∅ :=
        Finset.card_eq_zero.mp (by simpa [eps, hq] using hcount)
      have hnob (j : Index m) : b m j ∉ C := by
        intro hj
        have hjJ : j ∈ selectedPairs m C := by simp [selectedPairs, hj]
        rw [hJ] at hjJ
        exact Finset.notMem_empty j hjJ
      obtain ⟨x, hx⟩ := hC
      rcases x with (_ | j) | (_ | j)
      · exact hq hx
      · exact hnob j ((hbalance j).mp hx)
      · exact hp hx
      · exact hnob j hx
    have hcard : (selectedPairs m C).card = 1 := by
      simpa [eps, hq] using hcount
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    have hmem (i : Index m) : b m i ∈ C ↔ i = j := by
      have he : i ∈ selectedPairs m C ↔ i = j := by
        simp only [hj, Finset.mem_singleton]
      simpa [selectedPairs] using he
    refine ⟨j, ?_⟩
    ext x
    rcases x with (_ | i) | (_ | i)
    · change q m ∈ C ↔ q m ∈ triple m j
      simp [triple, hq]
    · simpa [triple, q, a, b] using (hbalance i).trans (hmem i)
    · change p m ∈ C ↔ p m ∈ triple m j
      have hpnot : p m ∉ triple m j := by simp [triple, q, p, a, b]
      simp only [hp, hpnot]
    · simpa [triple, q, a, b] using hmem i
  · rintro ⟨j, rfl⟩
    exact triple_nonempty_zero m j

private lemma minimal_support_iff (m : ℕ) (hm : 2 ≤ m)
    (B : Finset (Coordinate m)) :
    MinimalZeroSupport (label m) B ↔ ∃ j : Index m, B = triple m j := by
  classical
  constructor
  · intro hB
    exact (zero_support_iff m hm B).mp ⟨hB.1, hB.2.1⟩
  · rintro ⟨j, rfl⟩
    have ht := triple_nonempty_zero m j
    refine ⟨ht.1, ht.2, ?_⟩
    intro C hsub hCn hCz
    obtain ⟨i, rfl⟩ := (zero_support_iff m hm C).mp ⟨hCn, hCz⟩
    have hij : i = j := by
      have he := hsub (show a m i ∈ triple m i from by simp [triple])
      simpa [triple, q, a, b] using he
    subst i
    rfl

private lemma triple_proper (m : ℕ) (j : Index m) : triple m j ⊂ full m := by
  classical
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.subset_univ _, ?_⟩
  intro he
  have hp : p m ∈ triple m j := by rw [he]; exact Finset.mem_univ _
  simpa [triple, q, p, a, b] using hp

private lemma mem_supports (m : ℕ) (B : Finset (Coordinate m)) :
    B ∈ supports m ↔ B ⊂ full m ∧ MinimalZeroSupport (label m) B := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.ssubset_iff_subset_ne.mp h.1).1, h⟩

private lemma supports_eq_image (m : ℕ) (hm : 2 ≤ m) :
    supports m = Finset.univ.image (triple m) := by
  classical
  ext B
  rw [mem_supports]
  constructor
  · intro hB
    obtain ⟨j, rfl⟩ := (minimal_support_iff m hm B).mp hB.2
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  · intro hB
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨triple_proper m j, (minimal_support_iff m hm _).mpr ⟨j, rfl⟩⟩

private lemma triple_injective (m : ℕ) : Function.Injective (triple m) := by
  classical
  intro i j he
  have ha : a m i ∈ triple m j := he ▸ (by simp [triple])
  simpa [triple, q, a, b] using ha

set_option maxHeartbeats 800000 in
/-- The cyclic torsion bound on the actual ALL-support component count is
attained for every m >= 2 by an explicit finite abelian group. No endpoint,
classification, incidence, injectivity, or finiteness premise is assumed. -/
theorem sharpness (m : ℕ) (hm : 2 ≤ m) :
    Finite (WitnessGroup m) ∧
    Function.Injective (label m) ∧
    (∀ x : Coordinate m, label m x ≠ 0) ∧
    q m ∈ full m ∧
    addOrderOf (label m (q m)) = m ∧
    (∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, label m x) = 0) ↔
        ∃ j : Index m, C = triple m j) ∧
    (∀ B : Finset (Coordinate m),
      B ∈ supports m ↔ B ⊂ full m ∧ MinimalZeroSupport (label m) B) ∧
    (supports m).card = m - 1 ∧
    (∀ B ∈ supports m, q m ∈ B) ∧
    (∀ B ∈ supports m, ∀ D ∈ supports m, B ≠ D →
      Disjoint (B.erase (q m)) (D.erase (q m))) ∧
    (((Finset.univ : Finset (supports m)).filter (fun B => q m ∈ B.val)).image
      (supportIntersectionGraph (supports m) (q m)).connectedComponentMk).card = m - 1 := by
  classical
  letI : NeZero m := ⟨by omega⟩
  have hfinite : Finite (WitnessGroup m) := by infer_instance
  have hE := supports_eq_image m hm
  have hcard : (supports m).card = m - 1 := by
    rw [hE, Finset.card_image_of_injective _ (triple_injective m)]
    simp
  have hq : ∀ B ∈ supports m, q m ∈ B := by
    intro B hB
    rw [hE] at hB
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    simp [triple]
  have hdis : ∀ B ∈ supports m, ∀ D ∈ supports m, B ≠ D →
      Disjoint (B.erase (q m)) (D.erase (q m)) := by
    intro B hB D hD hne
    rw [hE] at hB hD
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hD
    have hij : i ≠ j := fun he => hne (congrArg (triple m) he)
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨hxq, hxi⟩ := Finset.mem_erase.mp hxi
    have hxj := (Finset.mem_erase.mp hxj).2
    simp only [triple, Finset.mem_insert, Finset.mem_singleton] at hxi hxj
    rcases hxi with hx | hx | hx
    · exact hxq hx
    · subst x
      rcases hxj with he | he | he
      · simpa [a, q] using he
      · exact hij (by simpa [a] using he)
      · simpa [a, b] using he
    · subst x
      rcases hxj with he | he | he
      · simpa [b, q] using he
      · simpa [a, b] using he
      · exact hij (by simpa [b] using he)
  let H := supportIntersectionGraph (supports m) (q m)
  let T : Finset (supports m) := Finset.univ.filter (fun B => q m ∈ B.val)
  let K := T.image H.connectedComponentMk
  have hnoadj (B D : supports m) : ¬ H.Adj B D := by
    rintro ⟨hne, x, hxq, hxB, hxD⟩
    have hBD : B.val ≠ D.val := fun he => hne (Subtype.ext he)
    exact Finset.disjoint_left.mp (hdis B.val B.property D.val D.property hBD)
      (Finset.mem_erase.mpr ⟨hxq, hxB⟩)
      (Finset.mem_erase.mpr ⟨hxq, hxD⟩)
  have hHbot : H = ⊥ :=
    SimpleGraph.eq_bot_iff_forall_not_adj.mpr hnoadj
  have hcompinj : Function.Injective H.connectedComponentMk := by
    intro B D he
    have hr : H.Reachable B D := SimpleGraph.ConnectedComponent.exact he
    rw [hHbot] at hr
    exact SimpleGraph.reachable_bot.mp hr
  have hT : T = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro B _
    exact hq B.val B.property
  -- The lower bound uses all original rows and their disjoint punctures.
  have hlower : m - 1 ≤ K.card := by
    calc
      m - 1 = (supports m).card := hcard.symm
      _ = (Finset.univ : Finset (supports m)).card := by simp
      _ = (T.image H.connectedComponentMk).card := by
        rw [Finset.card_image_of_injective _ hcompinj, hT]
      _ ≤ K.card := Nat.le_refl _
  have hmzero : m • label m (q m) = 0 := by
    simpa only [label_order m] using addOrderOf_nsmul_eq_zero (label m (q m))
  -- The upper bound is the supplied structural theorem on the canonical graph.
  have hcanonical :=
    q_containing_component_card_lt (α := Coordinate m) (G := WitnessGroup m)
      (label m) (full m) (supports m) (mem_supports m) (q m) m hm hmzero
  have hupper : K.card < m := by
    refine lt_of_eq_of_lt ?_ hcanonical
    congr 1
    ext c
    simp [K, T, H]
  have hcount : K.card = m - 1 := by
    exact Nat.le_antisymm (Nat.le_sub_one_of_lt hupper) hlower
  refine ⟨hfinite, label_injective m hm, label_nonzero m hm, Finset.mem_univ _,
    label_order m, zero_support_iff m hm, mem_supports m, hcard, hq, hdis, ?_⟩
  refine Eq.trans ?_ hcount
  congr 1

end D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
