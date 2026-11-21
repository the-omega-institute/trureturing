/- GID: D5/S3/Combinatorics/Matroids/CircuitRestrictionImage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CircuitRestrictionImage
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Exact integral image of signed restriction to a spanning circuit. -/

module

public import D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
public import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.GCD
import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.Tactic.Ring

/-! The signed circuit restriction for a one-element extension of a spanning circuit. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.CircuitRestrictionImage

open OrderedCycleFactorization
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

variable {V : Type*} [LinearOrder V]

/-- Pair a top chain with the oriented augmented boundary of the circuit simplex. -/
def signedRestriction (K : Finset V) (z : Chain V) : ℤ :=
  ∑ a ∈ K, simplexBoundary K (K.erase a) * z (K.erase a)

/-- The gcd of the sizes of the fibers of the dual singleton-closure map on the circuit. -/
noncomputable def dualClassGcd (M : Matroid V) (K : Finset V) : ℕ := by
  classical
  let cl : V → Set V := fun a => M✶.closure {a}
  exact (K.image cl).gcd fun P => (K.filter fun a => cl a = P).card

private lemma sign_square (F : Finset V) (a : V) :
    insertionSign F a * insertionSign F a = 1 :=
  sign_sq _

private def facetChain (E : Finset V) (p : V → ℤ) (F : Finset V) : ℤ :=
  ∑ a ∈ E, (insertionSign E a * p a) * simplex (E.erase a) F

private def potentialChain (E : Finset V) (p : V → ℤ) : Chain V :=
  boundaryOn E (facetChain E p)

private lemma facetChain_erase (E : Finset V) (p : V → ℤ) {a : V} (ha : a ∈ E) :
    facetChain E p (E.erase a) = insertionSign E a * p a := by
  unfold facetChain
  rw [sum_eq_single a]
  · simp [simplex]
  · intro b _ hba
    have hne : E.erase a ≠ E.erase b := fun h =>
      (notMem_erase a E) (h.symm ▸ mem_erase.mpr ⟨Ne.symm hba, ha⟩)
    simp [simplex, hne]
  · exact fun hn => (hn ha).elim

private lemma facetChain_one (E : Finset V) :
    facetChain E (fun _ => 1) = simplexBoundary E := by
  funext F
  by_cases h : ∃ a ∈ E, F = E.erase a
  · obtain ⟨a, ha, rfl⟩ := h
    rw [facetChain_erase E _ ha, simplexBoundary_erase ha, mul_one]
    unfold insertionSign
    rw [filter_erase, erase_eq_of_notMem (by simp)]
  · rw [not_ne_iff.mp (mt simplexBoundary_support.mp h)]
    apply sum_eq_zero
    intro a ha
    have hne : F ≠ E.erase a := fun he => h ⟨a, ha, he⟩
    simp [simplex, hne]

private lemma insert_sdiff_pair {E : Finset V} {a b : V}
    (ha : a ∈ E) (hab : a ≠ b) :
    insert a (E \ {a, b}) = E.erase b := by
  ext y
  by_cases hy : y = a
  · subst y
    simp [ha, hab]
  · simp [hy, and_comm]

private lemma potentialChain_pair_sum {E : Finset V} (p : V → ℤ) {a b : V}
    (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) :
    let F := E \ {a, b}
    potentialChain E p F =
      insertionSign F a * (insertionSign E b * p b) +
      insertionSign F b * (insertionSign E a * p a) := by
  let F := E \ {a, b}
  have hp : ({a, b} : Finset V) ⊆ E := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact ha
    · exact hb
  have hd : E \ F = {a, b} := by
    ext y
    by_cases hy : y ∈ ({a, b} : Finset V)
    · simp [F, hy, hp hy]
    · simp [F, hy]
  have hinB : insert b F = E.erase a := by
    dsimp [F]
    rw [pair_comm]
    exact insert_sdiff_pair hb hab.symm
  change (∑ y ∈ E \ F, insertionSign F y * facetChain E p (insert y F)) = _
  rw [hd, sum_insert (by simpa using hab), sum_singleton, insert_sdiff_pair ha hab, hinB,
    facetChain_erase E p hb, facetChain_erase E p ha]

private lemma potentialChain_pair {E : Finset V} (p : V → ℤ) {a b : V}
    (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) :
    let F := E \ {a, b}
    potentialChain E p F =
      (insertionSign F a * insertionSign E b) * (p b - p a) := by
  let F := E \ {a, b}
  have hzero : potentialChain E (fun _ => 1) F = 0 := by
    rw [potentialChain, facetChain_one, simplexBoundary, boundaryOn_squared]
  have hopp : insertionSign F b * insertionSign E a =
      -(insertionSign F a * insertionSign E b) := by
    have h := (potentialChain_pair_sum (fun _ => 1) ha hb hab).symm.trans hzero
    simpa only [mul_one, ← eq_neg_iff_add_eq_zero] using
      (show insertionSign F b * insertionSign E a + insertionSign F a * insertionSign E b = 0 by
        simpa only [mul_one, add_comm] using h)
  change potentialChain E p F = _
  rw [potentialChain_pair_sum p ha hb hab, ← mul_assoc, ← mul_assoc, hopp]
  ring

private lemma potentialChain_support {E : Finset V} {p : V → ℤ} {F : Finset V}
    (hn : potentialChain E p F ≠ 0) :
    ∃ a ∈ E, ∃ b ∈ E, a ≠ b ∧ F = E \ {a, b} := by
  classical
  by_contra! h
  apply hn
  apply sum_eq_zero
  intro a ha
  apply mul_eq_zero.mpr
  right
  apply sum_eq_zero
  intro b hb
  have hne : insert a F ≠ E.erase b := by
    intro he
    have haF := (mem_sdiff.mp ha).2
    have hab : a ≠ b := (mem_erase.mp (he ▸ mem_insert_self a F)).1
    apply h a (mem_sdiff.mp ha).1 b hb hab
    rw [← erase_insert haF, he]
    ext y
    simp only [mem_erase, mem_sdiff, mem_insert, mem_singleton]
    tauto
  simp [simplex, hne]

private lemma potentialChain_cycle [Fintype V] (E : Finset V) (p : V → ℤ)
    (R : Finset V) : boundaryOn univ (potentialChain E p) R = 0 := by
  classical
  have hs : E \ R ⊆ univ \ R := by simp
  have he : boundaryOn univ (potentialChain E p) R = boundaryOn E (potentialChain E p) R := by
    unfold boundaryOn
    symm
    apply sum_subset hs
    intro a ha hnot
    have haE : a ∉ E := fun hm => hnot (mem_sdiff.mpr ⟨hm, (mem_sdiff.mp ha).2⟩)
    have hz : potentialChain E p (insert a R) = 0 := by
      by_contra hn
      obtain ⟨b, _, c, _, _, hF⟩ := potentialChain_support hn
      exact haE ((mem_sdiff.mp (hF ▸ mem_insert_self a R)).1)
    rw [hz, mul_zero]
  rw [he, potentialChain, boundaryOn_squared]

private lemma cycle_eq_of_away [Fintype V] {z w : Chain V} {x : V}
    (hz : ∀ R, boundaryOn univ z R = 0) (hw : ∀ R, boundaryOn univ w R = 0)
    (haway : ∀ F : Finset V, x ∉ F → z F = w F) : z = w := by
  classical
  funext F
  by_cases hx : x ∈ F
  · let R := F.erase x
    have hd : x ∈ univ \ R := by simp [R]
    have hsum : (∑ a ∈ univ \ R, insertionSign R a *
        (z (insert a R) - w (insert a R))) = 0 := by
      calc
        _ = boundaryOn univ z R - boundaryOn univ w R := by
          simp only [boundaryOn, mul_sub, sum_sub_distrib]
        _ = 0 := by rw [hz, hw, sub_self]
    rw [sum_eq_single x] at hsum
    · rw [insert_erase hx] at hsum
      exact sub_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left (insertionSign_ne_zero _ _))
    · intro a _ hax
      rw [haway _ (by simp [R, Ne.symm hax]), sub_self, mul_zero]
    · exact fun hn => (hn hd).elim
  · exact haway F hx

private lemma dual_complement_base {M : Matroid V} {E A : Finset V}
    (hE : M.E = (E : Set V)) (hA : A ⊆ E) :
    M✶.IsBase (↑A : Set V) ↔ M.IsBase (↑(E \ A) : Set V) := by
  rw [Matroid.dual_isBase_iff (hE.symm ▸ coe_subset.mpr hA), hE, coe_sdiff]

private lemma primal_base_complement_pair {M : Matroid V} {E F : Finset V}
    (hE : M.E = (E : Set V)) (hF : M.IsBase (F : Set V))
    (hcard : ∀ B, M✶.IsBase B → B.encard = 2) :
    ∃ a ∈ E, ∃ b ∈ E, a ≠ b ∧ F = E \ {a, b} := by
  have hFE : F ⊆ E := coe_subset.mp (hE ▸ hF.subset_ground)
  have hB : M✶.IsBase (↑(E \ F) : Set V) := by
    apply (dual_complement_base hE sdiff_subset).2
    rwa [Finset.sdiff_sdiff_eq_self hFE]
  have htwo : (E \ F).card = 2 := by
    exact_mod_cast (hcard _ hB).trans (by rfl : (2 : ENat) = ((2 : ℕ) : ENat))
  obtain ⟨a, b, hab, hp⟩ := card_eq_two.mp htwo
  refine ⟨a, (mem_sdiff.mp (hp.symm ▸ mem_insert_self a ({b} : Finset V))).1,
    b, (mem_sdiff.mp (hp.symm ▸ mem_insert_of_mem (mem_singleton_self b))).1, hab, ?_⟩
  rw [← hp, Finset.sdiff_sdiff_eq_self hFE]

private lemma circuit_face_eq {K : Finset V} {x a : V} (hx : x ∉ K) :
    insert x K \ {a, x} = K.erase a := by
  ext y
  by_cases hy : y = x
  · subst y
    simp [hx]
  · simp [hy, and_comm]

private lemma missing_pivot_face {K F : Finset V} {x : V} (hx : x ∉ K)
    (hxF : x ∉ F)
    (hF : ∃ a ∈ insert x K, ∃ b ∈ insert x K, a ≠ b ∧ F = insert x K \ {a, b}) :
    ∃ a ∈ K, F = K.erase a := by
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := hF
  have hxpair : x ∈ ({a, b} : Finset V) := by
    by_contra hn
    exact hxF (mem_sdiff.mpr ⟨mem_insert_self _ _, hn⟩)
  rcases (show x = a ∨ x = b by simpa using hxpair) with h | h
  · subst a
    refine ⟨b, (mem_insert.mp hb).resolve_left hab.symm, ?_⟩
    rw [pair_comm, circuit_face_eq hx]
  · subst b
    exact ⟨a, (mem_insert.mp ha).resolve_left hab, circuit_face_eq hx⟩

private lemma dual_star_base {M : Matroid V} {K : Finset V} {x a : V}
    (hE : M.E = (↑(insert x K) : Set V)) (hx : x ∉ K)
    (hK : M.IsCircuit (K : Set V)) (hspan : M.Spanning (K : Set V)) (ha : a ∈ K) :
    M✶.IsBase {a, x} := by
  have hsubset : ({a, x} : Finset V) ⊆ insert x K := by
    intro y hy
    have h : y = a ∨ y = x := by simpa using hy
    rcases h with rfl | rfl
    · exact mem_insert_of_mem ha
    · exact mem_insert_self _ _
  have hB := (dual_complement_base hE hsubset).2
    (by rw [circuit_face_eq hx]; exact (circuit_erase_basis hK ha).isBase_of_spanning hspan)
  simpa only [coe_insert, coe_singleton] using hB

omit [LinearOrder V] in
private lemma pair_base_iff_indep {M : Matroid V}
    (hcard : ∀ B, M.IsBase B → B.encard = 2) {a b : V} (hab : a ≠ b) :
    M.IsBase {a, b} ↔ M.Indep {a, b} := by
  refine ⟨Matroid.IsBase.indep, fun h => ?_⟩
  obtain ⟨B, hB, hsub⟩ := h.exists_isBase_superset
  have hpair : ({a, b} : Set V).encard = 2 := Set.encard_eq_two.mpr ⟨a, b, hab, rfl⟩
  have he : ({a, b} : Set V) = B :=
    (Set.toFinite _).eq_of_subset_of_encard_le hsub (by rw [hcard B hB, hpair])
  exact he ▸ hB

private def restrictionChain (K : Finset V) (x : V) (p : V → ℤ) : Chain V :=
  potentialChain (insert x K) (fun a => -insertionSign (insert x K) x * p a)

private lemma restrictionChain_erase {K : Finset V} {x a : V}
    (hx : x ∉ K) (ha : a ∈ K) {p : V → ℤ} (hp : p x = 0) :
    restrictionChain K x p (K.erase a) = insertionSign (K.erase a) a * p a := by
  have hax : a ≠ x := fun he => hx (he ▸ ha)
  rw [restrictionChain, ← circuit_face_eq hx (a := a),
    potentialChain_pair _ (mem_insert_of_mem ha) (mem_insert_self x K) hax,
    circuit_face_eq hx, hp]
  have hs := sign_square (insert x K) x
  calc
    _ = insertionSign (K.erase a) a *
        ((insertionSign (insert x K) x * insertionSign (insert x K) x) * p a) := by ring
    _ = _ := by rw [hs, one_mul]

private lemma signedRestriction_chain {K : Finset V} {x : V} (hx : x ∉ K)
    {p : V → ℤ} (hp : p x = 0) :
    signedRestriction K (restrictionChain K x p) = ∑ a ∈ K, p a := by
  apply sum_congr rfl
  intro a ha
  rw [simplexBoundary_erase ha, restrictionChain_erase hx ha hp, ← mul_assoc, sign_square,
    one_mul]

private lemma eq_restrictionChain_of_cycle [Fintype V] {M : Matroid V}
    {K : Finset V} {x : V} (hE : M.E = (↑(insert x K) : Set V)) (hx : x ∉ K)
    (hcard : ∀ B, M✶.IsBase B → B.encard = 2) {z : Chain V} (hz : TopCycle M z) :
    ∃ p : V → ℤ, p x = 0 ∧ z = restrictionChain K x p := by
  classical
  let p (a : V) := if a ∈ K then insertionSign (K.erase a) a * z (K.erase a) else 0
  have hp : p x = 0 := ite_eq_right hx
  refine ⟨p, hp, cycle_eq_of_away (x := x) hz.cycle (potentialChain_cycle _ _) ?_⟩
  intro F hxF
  by_cases h : ∃ a ∈ K, F = K.erase a
  · obtain ⟨a, ha, rfl⟩ := h
    rw [restrictionChain_erase hx ha hp]
    simp only [p, ite_eq_left ha, ← mul_assoc, sign_square, one_mul]
  have hzF : z F = 0 := hz.vanishes F fun hF =>
    h (missing_pivot_face hx hxF (primal_base_complement_pair hE hF hcard))
  have hwF : restrictionChain K x p F = 0 := by
    by_contra hn
    exact h (missing_pivot_face hx hxF (potentialChain_support hn))
  rw [hzF, hwF]

private lemma restrictionChain_pair_zero_iff {K : Finset V} {x a b : V} {p : V → ℤ}
    (ha : a ∈ insert x K) (hb : b ∈ insert x K) (hab : a ≠ b) :
    restrictionChain K x p (insert x K \ {a, b}) = 0 ↔ p a = p b := by
  rw [restrictionChain, potentialChain_pair _ ha hb hab, mul_eq_zero,
    or_iff_right (mul_ne_zero (insertionSign_ne_zero _ _) (insertionSign_ne_zero _ _)),
    sub_eq_zero, mul_right_inj' (neg_ne_zero.mpr (insertionSign_ne_zero _ _)), eq_comm]

omit [LinearOrder V] in
private lemma sum_fibers {ι : Type*} [DecidableEq ι] {S : Finset V} (f : V → ι) (q : ι → ℤ) :
    (∑ a ∈ S, q (f a)) = ∑ c ∈ S.image f, ((S.filter fun a => f a = c).card : ℤ) * q c := by
  simpa only [sum_const, nsmul_eq_mul] using
    (sum_fiberwise_of_maps_to' (fun _ h => mem_image_of_mem f h) q).symm

private lemma gcd_eq_sum {ι : Type*} (S : Finset ι) (w : ι → ℕ) :
    ∃ q : ι → ℤ, ((S.gcd w : ℕ) : ℤ) = ∑ c ∈ S, (w c : ℤ) * q c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨q, hq⟩ := ih
    let u := Nat.gcdA (w a) (S.gcd w)
    let v := Nat.gcdB (w a) (S.gcd w)
    refine ⟨fun c => if c = a then u else q c * v, ?_⟩
    rw [gcd_insert, sum_insert ha]
    change ((Nat.gcd (w a) (S.gcd w) : ℕ) : ℤ) = _
    rw [Nat.gcd_eq_gcd_ab, show Nat.gcdA (w a) (S.gcd w) = u from rfl,
      show Nat.gcdB (w a) (S.gcd w) = v from rfl, hq, sum_mul]
    congr 1
    · simp
    · apply sum_congr rfl
      intro c hc
      have hca : c ≠ a := fun he => ha (he ▸ hc)
      simp only [ite_eq_right hca, mul_assoc]

/-- The attainable signed restrictions are exactly the multiples of the gcd of the dual
parallel-class sizes in the spanning circuit. -/
theorem exists_topCycle_signedRestriction_iff [Fintype V] (M : Matroid V) (K : Finset V) (x : V)
    (hE : M.E = (↑(insert x K) : Set V)) (hx : x ∉ K)
    (hK : M.IsCircuit (K : Set V)) (hspan : M.Spanning (K : Set V)) (n : ℤ) :
    (∃ z : Chain V, TopCycle M z ∧ signedRestriction K z = n) ↔
      (dualClassGcd M K : ℤ) ∣ n := by
  classical
  let E := insert x K
  let cl (a : V) := M✶.closure {a}
  let classes := K.image cl
  let size (P : Set V) := (K.filter fun a => cl a = P).card
  have hstar (a : V) (ha : a ∈ K) := dual_star_base hE hx hK hspan ha
  obtain ⟨k, hk⟩ := hK.nonempty
  have hkK : k ∈ K := hk
  have hkx : k ≠ x := fun h => hx (h ▸ hkK)
  have hcard (B : Set V) (hB : M✶.IsBase B) : B.encard = 2 :=
    (hB.encard_eq_encard_of_isBase (hstar k hkK)).trans (Set.encard_eq_two.mpr ⟨k, x, hkx, rfl⟩)
  have hclass (a b : V) (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b) :
      cl a = cl b ↔ ¬ M✶.IsBase {a, b} := by
    have han := (hstar a ha).indep.isNonloop_of_mem (Set.mem_insert a {x})
    have hbn := (hstar b hb).indep.isNonloop_of_mem (Set.mem_insert b {x})
    rw [pair_base_iff_indep hcard hab]
    simpa only [cl, hab, false_or] using han.closure_eq_closure_iff_eq_or_dep hbn
  have hpair (a b : V) (ha : a ∈ E) (hb : b ∈ E) :
      M✶.IsBase {a, b} ↔ M.IsBase (↑(E \ {a, b}) : Set V) := by
    have hsub : ({a, b} : Finset V) ⊆ E := by
      intro y hy
      rcases (show y = a ∨ y = b by simpa using hy) with rfl | rfl
      · exact ha
      · exact hb
    simpa only [coe_insert, coe_singleton] using dual_complement_base hE hsub
  change (∃ z : Chain V, TopCycle M z ∧ signedRestriction K z = n) ↔
    ((classes.gcd size : ℕ) : ℤ) ∣ n
  constructor
  · rintro ⟨z, hz, hzN⟩
    obtain ⟨p, hp, rfl⟩ := eq_restrictionChain_of_cycle hE hx hcard hz
    have hconst (a b : V) (ha : a ∈ K) (hb : b ∈ K) (hcl : cl a = cl b) : p a = p b := by
      by_cases hab : a = b
      · rw [hab]
      have haE : a ∈ E := mem_insert_of_mem ha
      have hbE : b ∈ E := mem_insert_of_mem hb
      apply (restrictionChain_pair_zero_iff haE hbE hab).1
      exact hz.vanishes _ fun h => (hclass a b ha hb hab).1 hcl ((hpair a b haE hbE).2 h)
    let q (P : Set V) : ℤ :=
      if h : ∃ a ∈ K, cl a = P then p h.choose else 0
    have hq (a : V) (ha : a ∈ K) : p a = q (cl a) := by
      have h : ∃ b ∈ K, cl b = cl a := ⟨a, ha, rfl⟩
      simp only [q, dite_eq_left h]
      exact hconst a h.choose ha h.choose_spec.1 h.choose_spec.2.symm
    rw [← hzN, signedRestriction_chain hx hp]
    calc
      _ ∣ ∑ a ∈ K, q (cl a) := by
        rw [sum_fibers]
        apply Finset.dvd_sum
        intro P hP
        exact dvd_mul_of_dvd_left (by exact_mod_cast (Finset.gcd_dvd (f := size) hP)) _
      _ = ∑ a ∈ K, p a := sum_congr rfl fun a ha => (hq a ha).symm
  · rintro ⟨m, hm⟩
    obtain ⟨q, hq⟩ := gcd_eq_sum classes size
    let p (a : V) := if a = x then 0 else q (cl a) * m
    have hp : p x = 0 := ite_eq_left rfl
    refine ⟨restrictionChain K x p, ⟨?_, potentialChain_cycle E _⟩, ?_⟩
    · intro F hF
      by_contra hn
      obtain ⟨a, ha, b, hb, hab, rfl⟩ := potentialChain_support hn
      have hnot : ¬ M✶.IsBase {a, b} := fun h => hF ((hpair a b ha hb).1 h)
      have hax : a ≠ x := by
        rintro rfl
        exact hnot (by rw [Set.pair_comm]; exact hstar b ((mem_insert.mp hb).resolve_left hab.symm))
      have hbx : b ≠ x := by
        rintro rfl
        exact hnot (hstar a ((mem_insert.mp ha).resolve_left hab))
      have hid := (hclass a b ((mem_insert.mp ha).resolve_left hax)
        ((mem_insert.mp hb).resolve_left hbx) hab).2 hnot
      exact hn ((restrictionChain_pair_zero_iff ha hb hab).2 (by simp [p, hax, hbx, hid]))
    rw [signedRestriction_chain hx hp, hm, hq, sum_mul]
    calc
      _ = ∑ a ∈ K, q (cl a) * m := by
        apply sum_congr rfl
        intro a ha
        have hax : a ≠ x := fun h => hx (h ▸ ha)
        exact ite_eq_right hax
      _ = _ := by rw [← sum_mul, sum_fibers, sum_mul]

end D5.S3.Combinatorics.Matroids.CircuitRestrictionImage
