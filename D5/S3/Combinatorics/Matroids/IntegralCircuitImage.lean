/- GID: D5/S3/Combinatorics/Matroids/IntegralCircuitImage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/IntegralCircuitImage
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Integral aggregate restriction along arbitrary matroid circuits. -/

module

public import D5.S3.Combinatorics.Matroids.IntegralLinkRestriction
public import D5.S3.Combinatorics.Matroids.CircuitRestrictionImage
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.IntegralCircuitImage

open OrderedCycleFactorization
open IntegralLinkRestriction
open CircuitCycleDecomposition (topCycles CircuitThrough circuit_cycle_decomposition restrictChain restrictionSign)
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Sum the signed circuit restrictions over all deleted circuit vertices. -/
noncomputable def aggregateRestrict (M : Matroid V) (K : Finset V) (z : Chain V) : Chain V :=
  ∑ a ∈ K, restrictChain M K a z

private lemma aggregate_topCycle {M : Matroid V} {K : Finset V}
    (hK : M.IsCircuit (K : Set V)) {z : Chain V} (hz : TopCycle M z) :
    TopCycle (M ／ (K : Set V)) (aggregateRestrict M K z) := by
  change aggregateRestrict M K z ∈ topCycles (M ／ (K : Set V))
  apply Submodule.sum_mem
  intro a ha
  obtain ⟨e, he, _⟩ := circuit_cycle_decomposition M a (hK.subset_ground ha)
  let C : CircuitThrough M a := ⟨K, hK, ha⟩
  have hr : (e ⟨z, hz⟩ C).val = restrictChain M K a z := by
    funext T
    simpa only [C, restrictChain, restrictionSign] using he ⟨z, hz⟩ C T
  rw [← hr]
  exact (e ⟨z, hz⟩ C).property

private lemma topCycle_dvd_iff {M : Matroid V} {q : Chain V} (hq : TopCycle M q) (d : ℤ) :
    (∃ w : Chain V, TopCycle M w ∧ q = d • w) ↔ ∀ T, d ∣ q T := by
  constructor
  · rintro ⟨w, _, rfl⟩ T
    exact ⟨w T, rfl⟩
  · intro hd
    choose w hw using hd
    have he : q = d • w := funext hw
    by_cases hn : d = 0
    · refine ⟨0, (topCycles M).zero_mem, ?_⟩
      simpa [hn] using he
    · refine ⟨w, ⟨fun T hT => ?_, fun R => ?_⟩, he⟩
      · exact (mul_eq_zero.mp ((hw T).symm.trans (hq.vanishes T hT))).resolve_left hn
      · apply (mul_eq_zero.mp _).resolve_left hn
        calc
          d * boundaryOn univ w R = boundaryOn univ q R := by
            simp only [boundaryOn, hw, mul_sum]
            apply sum_congr rfl
            intro a _
            exact mul_left_comm _ _ _
          _ = 0 := hq.cycle R

/-- Divisibility at every aggregated coordinate is equivalent to divisibility
within the integral top-cycle lattice of the circuit contraction. -/
private theorem aggregateRestrict_dvd_iff {M : Matroid V} {K : Finset V}
    (hK : M.IsCircuit (K : Set V)) {z : Chain V} (hz : TopCycle M z) (d : ℤ) :
    (∃ w : Chain V, TopCycle (M ／ (K : Set V)) w ∧ aggregateRestrict M K z = d • w) ↔
      ∀ T, d ∣ aggregateRestrict M K z T :=
  topCycle_dvd_iff (aggregate_topCycle hK hz) d


omit [Fintype V] in
private lemma facet_join {K T : Finset V} (hd : Disjoint T K) {a : V} (ha : a ∈ K) :
    signedJoin K (simplexBoundary K) (simplex T) (T ∪ K.erase a) =
      restrictionSign K a T := by
  rcases split_circuit_face hd a with ⟨hinter, hdiff⟩
  rw [signedJoin, hinter, hdiff, simplexBoundary_erase ha, simplex, ite_eq_left rfl,
    mul_one, restrictionSign, mul_comm]

private lemma restrictionSign_eq_of_dual_closure {M : Matroid V} {K T : Finset V}
    {z : Chain V} (hz : TopCycle M z) (hK : M.IsCircuit (K : Set V)) (hd : Disjoint T K)
    {a b : V} (ha : a ∈ K) (hb : b ∈ K) (hcl : M✶.closure {a} = M✶.closure {b}) :
    restrictionSign K a T * z (T ∪ K.erase a) =
      restrictionSign K b T * z (T ∪ K.erase b) := by
  by_cases hab : a = b
  · subst b
    rfl
  let R := T ∪ (K \ {a, b})
  let j := signedJoin K (simplexBoundary K) (simplex T)
  have haR : a ∉ R := by simp [R, disjoint_left.mp hd.symm ha]
  have hbR : b ∉ R := by simp [R, disjoint_left.mp hd.symm hb]
  have hinA : insert a R = T ∪ K.erase b := by
    change insert a (T ∪ (K \ {a, b})) = T ∪ K.erase b
    rw [← union_insert, CircuitRestrictionImage.insert_sdiff_pair ha hab]
  have hinB : insert b R = T ∪ K.erase a := by
    change insert b (T ∪ (K \ {a, b})) = T ∪ K.erase a
    rw [← union_insert, pair_comm, CircuitRestrictionImage.insert_sdiff_pair hb (Ne.symm hab)]
  have hpair : ({a, b} : Finset V) ⊆ univ \ R := by simp [insert_subset_iff, haR, hbR]
  have houtside (y : V) (hy : y ∈ univ \ R) (hyp : y ∉ ({a, b} : Finset V)) :
      y ∉ K ∧ y ∉ T := by
    have hyR := (mem_sdiff.mp hy).2
    exact ⟨fun hyK => hyR (mem_union_right _ (mem_sdiff.mpr ⟨hyK, hyp⟩)),
      fun hyT => hyR (mem_union_left _ hyT)⟩
  have hnonbase (y : V) (hyp : y ∉ ({a, b} : Finset V)) :
      ¬ M.IsBase (↑(insert y R) : Set V) := by
    intro hB
    apply (hB.compl_isBase_dual.indep.subset
      (show insert b ({a} : Set V) ⊆ M.E \ (↑(insert y R) : Set V) by
        have hya : y ≠ a := fun h => hyp (by simp [h])
        have hyb : y ≠ b := fun h => hyp (by simp [h])
        have ha' : a ∈ M.E \ (↑(insert y R) : Set V) :=
          ⟨hK.subset_ground ha, by simpa [Ne.symm hya] using haR⟩
        have hb' : b ∈ M.E \ (↑(insert y R) : Set V) :=
          ⟨hK.subset_ground hb, by simpa [Ne.symm hyb] using hbR⟩
        exact Set.insert_subset hb' (Set.singleton_subset_iff.2 ha'))).not_dep
    have hIa : M✶.Indep ({a} : Set V) :=
      hB.compl_isBase_dual.indep.subset (by
        have hya : y ≠ a := fun h => hyp (by simp [h])
        simp [hK.subset_ground ha, haR, Ne.symm hya])
    apply hIa.insert_dep_iff.2
    refine ⟨?_, by simpa using Ne.symm hab⟩
    rw [hcl]
    exact M✶.mem_closure_of_mem (Set.mem_singleton _) (by simpa using hK.subset_ground hb)
  have hdiff : R \ K = T := by
    simp [R, union_sdiff_distrib, Finset.sdiff_eq_self_iff_disjoint.mpr hd]
  have hj : boundaryOn univ j R = 0 := by
    have hs : boundaryOn (univ \ K) (simplex T) T = 0 := by
      apply sum_eq_zero
      intro y hy
      have hyT := (mem_sdiff.mp hy).2
      have hne : insert y T ≠ T := fun h => hyT (h ▸ mem_insert_self _ _)
      rw [simplex, ite_eq_right hne, mul_zero]
    change boundaryOn univ (signedJoin K (simplexBoundary K) (simplex T)) R = 0
    rw [boundaryOn_signedJoin, hdiff, simplexBoundary, boundaryOn_squared, hs]
    simp
  have htwo (f : Chain V) (hf : boundaryOn univ f R = 0)
      (hout : ∀ y ∈ univ \ R, y ∉ ({a, b} : Finset V) → f (insert y R) = 0) :
      insertionSign R a * f (T ∪ K.erase b) +
        insertionSign R b * f (T ∪ K.erase a) = 0 := by
    unfold boundaryOn at hf
    rw [← sum_subset (f := fun y => insertionSign R y * f (insert y R)) hpair
      (fun y hy hyp => by rw [hout y hy hyp, mul_zero]),
      sum_insert (show a ∉ ({b} : Finset V) by simpa using hab), sum_singleton, hinA, hinB] at hf
    exact hf
  have hactual := htwo z (hz.cycle R) (fun y _ hyp => hz.vanishes _ (hnonbase y hyp))
  have href := htwo j hj (fun y hy hyp => by
    obtain ⟨hyK, hyT⟩ := houtside y hy hyp
    have hne : insert y R \ K ≠ T := fun he =>
      hyT (he ▸ mem_sdiff.mpr ⟨mem_insert_self _ _, hyK⟩)
    simp [j, signedJoin, simplex, hne])
  change insertionSign R a *
      signedJoin K (simplexBoundary K) (simplex T) (T ∪ K.erase b) +
    insertionSign R b * signedJoin K (simplexBoundary K) (simplex T) (T ∪ K.erase a) = 0 at href
  rw [facet_join hd hb, facet_join hd ha] at href
  have hdiff : restrictionSign K a T * z (T ∪ K.erase b) =
      restrictionSign K b T * z (T ∪ K.erase a) := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp _).resolve_left (insertionSign_ne_zero R a)
    calc
      _ = restrictionSign K a T *
            (insertionSign R a * z (T ∪ K.erase b) + insertionSign R b * z (T ∪ K.erase a)) -
          z (T ∪ K.erase a) *
            (insertionSign R a * restrictionSign K b T + insertionSign R b * restrictionSign K a T)
          := by ring
      _ = 0 := by rw [hactual, href, mul_zero, mul_zero, sub_self]
  calc
    _ = (restrictionSign K b T * restrictionSign K b T) *
          (restrictionSign K a T * z (T ∪ K.erase a)) := by
            rw [CircuitCycleDecomposition.restrictionSign_sq, one_mul]
    _ = restrictionSign K a T * restrictionSign K b T *
          (restrictionSign K b T * z (T ∪ K.erase a)) := by ring
    _ = _ := by
      rw [← hdiff]
      calc
        _ = (restrictionSign K a T * restrictionSign K a T) *
              (restrictionSign K b T * z (T ∪ K.erase b)) := by ring
        _ = _ := by rw [CircuitCycleDecomposition.restrictionSign_sq, one_mul]

/-- Every aggregate restriction belongs to the dual class-size gcd multiple
of the full integral top-cycle lattice of the contraction. -/
private theorem aggregateRestrict_mem_gcd_smul {M : Matroid V} {K : Finset V}
    (hK : M.IsCircuit (K : Set V)) {z : Chain V} (hz : TopCycle M z) :
    ∃ w : Chain V, TopCycle (M ／ (K : Set V)) w ∧
      aggregateRestrict M K z = (CircuitRestrictionImage.dualClassGcd M K : ℤ) • w := by
  classical
  apply (aggregateRestrict_dvd_iff hK hz _).2
  intro T
  by_cases hT : (M ／ (K : Set V)).IsBase (T : Set V)
  · let f : V → Set V := fun a => M✶.closure {a}
    let q : V → ℤ := fun a => restrictionSign K a T * z (T ∪ K.erase a)
    unfold aggregateRestrict
    rw [Finset.sum_apply]
    simp only [restrictChain, ite_eq_left hT]
    change (CircuitRestrictionImage.dualClassGcd M K : ℤ) ∣ ∑ a ∈ K, q a
    let r : Set V → ℤ := fun c => if h : ∃ a ∈ K, f a = c then q h.choose else 0
    have hr (a : V) (ha : a ∈ K) : r (f a) = q a := by
      have h : ∃ b ∈ K, f b = f a := ⟨a, ha, rfl⟩
      change (if h : ∃ b ∈ K, f b = f a then q h.choose else 0) = q a
      rw [dite_eq_left h]
      exact restrictionSign_eq_of_dual_closure hz hK (contract_base_disjoint hT)
        h.choose_spec.1 ha h.choose_spec.2
    rw [sum_congr rfl (fun a ha => (hr a ha).symm)]
    rw [CircuitRestrictionImage.sum_fibers f r]
    apply Finset.dvd_sum
    intro c hc
    apply dvd_mul_of_dvd_left _ _
    exact_mod_cast (Finset.gcd_dvd hc :
      (K.image f).gcd (fun c => (K.filter fun a => f a = c).card) ∣ _)
  · rw [aggregateRestrict, Finset.sum_apply]
    simp [restrictChain, hT]


private lemma contract_base_of_basis {N : Matroid V} {I X U : Set V}
    (hI : N.IsBasis I X) (hUX : Disjoint U X) :
    (N ／ X).IsBase U ↔ N.IsBase (U ∪ I) := by
  classical
  obtain ⟨I, rfl⟩ := (Set.toFinite I).exists_finset_coe
  obtain ⟨X, rfl⟩ := (Set.toFinite X).exists_finset_coe
  obtain ⟨U, rfl⟩ := (Set.toFinite U).exists_finset_coe
  rw [← Finset.coe_union]
  exact contract_base_iff hI (by exact_mod_cast hUX)

private lemma delete_class_base_iff {M : Matroid V} {P D : Set V} {p : V}
    (hP : M✶.IsBasis {p} P) (hD : D ⊆ M.E \ P) :
    (M ＼ P).IsBase D ↔ M.IsBase (D ∪ (P \ {p})) := by
  let U := (M.E \ P) \ D
  have hp : p ∈ P := hP.subset (Set.mem_singleton _)
  have hPE : P ⊆ M.E := hP.subset_ground
  have hUE : U ⊆ M.E := Set.sdiff_subset.trans Set.sdiff_subset
  have hUP : Disjoint U P := Set.disjoint_left.2 fun _ hu hv => hu.1.2 hv
  have h₁ : (M ＼ P).E \ U = D := Set.sdiff_sdiff_cancel_left hD
  have h₂ : M.E \ (U ∪ {p}) = D ∪ (P \ {p}) := by
    ext y
    simp only [U, Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
    have hDy : y ∈ D → y ∈ M.E ∧ y ∉ P := fun h => hD h
    have hPy : y ∈ P → y ∈ M.E := fun h => hPE h
    have hpy : y = p → y ∈ P := fun e => e.symm ▸ hp
    tauto
  calc
    _ ↔ (M ＼ P)✶.IsBase U := by
      rw [Matroid.dual_isBase_iff (show U ⊆ (M ＼ P).E from Set.sdiff_subset), h₁]
    _ ↔ M✶.IsBase (U ∪ {p}) := by
      rw [Matroid.dual_delete]
      exact contract_base_of_basis hP hUP
    _ ↔ _ := by
      rw [Matroid.dual_isBase_iff (Set.union_subset hUE (Set.singleton_subset_iff.2 (hPE hp))), h₂]

private lemma delete_class_link {M : Matroid V} {K P : Finset V} {p : V}
    (hK : M.IsCircuit (K : Set V)) (hPK : P ⊆ K) (hP : M✶.IsBasis {p} (P : Set V)) :
    (M ＼ (P : Set V)).Indep (↑(K \ P) : Set V) ∧
      (M ＼ (P : Set V)) ／ (↑(K \ P) : Set V) = M ／ (K : Set V) := by
  classical
  let A : Set V := (K : Set V) \ (P : Set V)
  have hp : p ∈ K := hPK (hP.subset (Set.mem_singleton _))
  have hKp := hK.sdiff_singleton_isBasis hp
  have hunion : A ∪ ((P : Set V) \ {p}) = (K : Set V) \ {p} := by
    ext y
    simp only [A, Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
    have hyP : y ∈ P → y ∈ K := fun h => hPK h
    have hyp : y = p → y ∈ P := fun he => he.symm ▸ hP.subset (Set.mem_singleton p)
    tauto
  have hAE : A ⊆ M.E \ (P : Set V) :=
    fun _ hy => ⟨hK.subset_ground hy.1, hy.2⟩
  have hcompare (T : Set V) (hT : T ⊆ M.E \ (K : Set V)) :
      (M ＼ (P : Set V)).IsBase (T ∪ A) ↔ (M ／ (K : Set V)).IsBase T := by
    have hTE : T ⊆ M.E \ (P : Set V) := hT.trans (Set.sdiff_subset_sdiff_right (Finset.coe_subset.2 hPK))
    have hd : Disjoint T (K : Set V) := Set.disjoint_left.2 fun _ ht hk => (hT ht).2 hk
    rw [delete_class_base_iff hP (Set.union_subset hTE hAE), Set.union_assoc, hunion]
    exact (contract_base_of_basis hKp hd).symm
  obtain ⟨T, hT⟩ := (M ／ (K : Set V)).exists_isBase
  have hAI : (M ＼ (P : Set V)).Indep A :=
    ((hcompare T hT.subset_ground).2 hT).indep.subset Set.subset_union_right
  have hE : ((M ＼ (P : Set V)) ／ A).E = (M ／ (K : Set V)).E := by
    simp only [Matroid.delete_ground, Matroid.contract_ground]
    ext y
    simp only [A, Set.mem_sdiff]
    have hyP : y ∈ P → y ∈ K := fun h => hPK h
    tauto
  rw [Finset.coe_sdiff]
  refine ⟨hAI, Matroid.ext_isBase hE (fun T hT => ?_)⟩
  have hT' : T ⊆ (M ／ (K : Set V)).E := hE ▸ hT
  have hd : Disjoint T A := Set.disjoint_left.2 fun _ ht ha => (hT' ht).2 ha.1
  rw [hAI.contract_isBase_iff, and_iff_left hd]
  exact hcompare T hT'

omit [Fintype V] in
private lemma dual_class_eq_closure {M : Matroid V} {K : Finset V}
    (hK : M.IsCircuit (K : Set V)) (hc : ∀ x, ¬ M.IsColoop x) {p : V} (hp : p ∈ K) :
    let P := K.filter fun x => M✶.closure {x} = M✶.closure {p}
    (P : Set V) = M✶.closure {p} := by
  classical
  intro P
  ext y
  simp only [P, Finset.mem_coe, mem_filter]
  constructor
  · rintro ⟨hy, he⟩
    rw [← he]
    exact M✶.mem_closure_of_mem (Set.mem_singleton _) (by simpa using hK.subset_ground hy)
  · intro hy
    have hyn : M✶.IsNonloop y := Matroid.isNonloop_of_not_isLoop
      (M✶.closure_subset_ground _ hy) (hc y)
    have hcl := hyn.closure_eq_of_mem_closure hy
    refine ⟨?_, hcl⟩
    by_contra hyK
    have hyp : y ≠ p := fun he => hyK (he.symm ▸ hp)
    have hC : M✶.IsCircuit {y, p} :=
      (hyn.closure_eq_closure_iff_isCircuit_of_ne hyp).1 hcl
    apply hC.inter_isCocircuit_ne_singleton hK.isCocircuit
    ext v
    have hv (he : v = y) : v ∉ K := fun hm => hyK (he ▸ hm)
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe]
    exact ⟨fun ⟨h, hm⟩ => h.elim (fun he => (hv he hm).elim) id,
      fun he => ⟨Or.inr he, he.symm ▸ hp⟩⟩


private lemma join_class_topCycle {M : Matroid V} {P : Finset V}
    (hP : ∀ a ∈ P, M✶.IsBasis {a} (P : Set V))
    {v : Chain V} (hv : TopCycle (M ＼ (P : Set V)) v) :
    TopCycle M (signedJoin P (simplexBoundary P) v) := by
  refine ⟨fun F hF => ?_, fun R => ?_⟩
  · by_contra hn
    have hp := right_ne_zero_of_mul hn
    obtain ⟨a, ha, hA⟩ := simplexBoundary_support.mp (left_ne_zero_of_mul hp)
    have hT : (M ＼ (P : Set V)).IsBase (↑(F \ P) : Set V) := by
      by_contra h
      exact right_ne_zero_of_mul hp (hv.vanishes _ h)
    apply hF
    have hB := (delete_class_base_iff (hP a ha) hT.subset_ground).1 hT
    rw [← Finset.coe_erase, ← Finset.coe_union, ← hA, sdiff_union_inter] at hB
    exact hB
  · have hboundary (T : Finset V) : boundaryOn (univ \ P) v T = 0 := by
      rw [← hv.cycle T]
      apply sum_subset
      · intro x hx
        exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hx).2⟩
      · intro x hx hx'
        have hxP : x ∈ P := by simpa [(mem_sdiff.mp hx).2] using hx'
        rw [hv.vanishes _ (fun h => (h.subset_ground (show x ∈ (↑(insert x T) : Set V)
          from mem_insert_self _ _)).2 hxP), mul_zero]
    rw [boundaryOn_signedJoin, hboundary, simplexBoundary, boundaryOn_squared]
    simp

omit [Fintype V] in
private lemma insertionSign_union (A B : Finset V) (h : Disjoint A B) (x : V) :
    insertionSign (A ∪ B) x = insertionSign A x * insertionSign B x := by
  unfold insertionSign
  rw [filter_union, card_union_of_disjoint (h.mono (filter_subset _ _) (filter_subset _ _)),
    pow_add]

omit [Fintype V] in
private lemma shuffleSign_union_left (A B T : Finset V) (h : Disjoint A B) :
    shuffleSign (A ∪ B) T = shuffleSign A T * shuffleSign B T := by
  simp only [shuffleSign, sum_union h, pow_add]

omit [Fintype V] in
private lemma shuffleSign_union_right (D A B : Finset V) (h : Disjoint A B) :
    shuffleSign D (A ∪ B) = shuffleSign D A * shuffleSign D B := by
  have hc (x : V) : ((A ∪ B).filter (· < x)).card =
      (A.filter (· < x)).card + (B.filter (· < x)).card := by
    rw [filter_union, card_union_of_disjoint (h.mono (filter_subset _ _) (filter_subset _ _))]
  simp only [shuffleSign, hc, sum_add_distrib, pow_add]

omit [Fintype V] in
private lemma shuffleSign_sq (A T : Finset V) :
    shuffleSign A T * shuffleSign A T = 1 := sign_sq _

omit [Fintype V] in
private lemma class_join_coords {K P T : Finset V} {a : V} (hPK : P ⊆ K)
    (hd : Disjoint T K) (v : Chain V) :
    let A := K \ P
    restrictionSign K a T *
        signedJoin P (simplexBoundary P) v (T ∪ K.erase a) =
      if a ∈ P then shuffleSign P A * linkRestrict A v T else 0 := by
  intro A
  have hTA : Disjoint T A := hd.mono_right sdiff_subset
  have hTP : Disjoint T P := hd.mono_right hPK
  have hAP : Disjoint A P := disjoint_sdiff.symm
  by_cases hap : a ∈ P
  · have hKA : K.erase a = P.erase a ∪ A := by
      ext y
      by_cases hy : y ∈ P
      · simp [A, hy, hPK hy]
      · have hne : y ≠ a := fun he => hy (he.symm ▸ hap)
        simp [A, hy, hne]
    have hinter : (T ∪ K.erase a) ∩ P = P.erase a := by
      ext y
      by_cases hy : y ∈ P
      · have hyT : y ∉ T := fun h => disjoint_left.mp hTP h hy
        simp [hy, hyT, hPK hy]
      · simp [hy]
    have hdiff : (T ∪ K.erase a) \ P = T ∪ A := by
      rw [hKA, ← union_assoc, union_sdiff_distrib, union_sdiff_distrib,
        Finset.sdiff_eq_self_iff_disjoint.mpr hTP,
        sdiff_eq_empty_iff_subset.mpr (erase_subset _ _),
        Finset.sdiff_eq_self_iff_disjoint.mpr hAP, union_empty]
    have hdis : Disjoint (P.erase a) A := hAP.symm.mono_left (erase_subset _ _)
    have hshuffle : shuffleSign P A = insertionSign A a * shuffleSign (P.erase a) A := by
      unfold shuffleSign insertionSign
      conv_lhs => rw [← insert_erase hap, sum_insert (notMem_erase _ _), pow_add]
    rw [ite_eq_left hap, signedJoin, hinter, hdiff, simplexBoundary_erase hap,
      restrictionSign, hKA, insertionSign_union _ _ hdis, shuffleSign_union_left _ _ _ hdis,
      shuffleSign_union_right _ _ _ hTA, linkRestrict, ite_eq_left hTA, hshuffle]
    calc
      _ = (insertionSign (P.erase a) a * insertionSign (P.erase a) a) *
          (shuffleSign (P.erase a) T * shuffleSign (P.erase a) T) *
          (insertionSign A a * shuffleSign (P.erase a) A *
            (shuffleSign A T * v (T ∪ A))) := by ring
      _ = _ := by rw [show insertionSign (P.erase a) a * insertionSign (P.erase a) a = 1
        from sign_sq _, shuffleSign_sq, one_mul, one_mul]
  · have hP : (T ∪ K.erase a) ∩ P = P := by
      apply inter_eq_right.mpr
      intro y hy
      exact mem_union_right _ (mem_erase.mpr ⟨fun he => hap (he ▸ hy), hPK hy⟩)
    simp [hap, signedJoin, hP, simplexBoundary, boundaryOn]

private lemma class_multiple_image {M : Matroid V} {K : Finset V}
    (hK : M.IsCircuit (K : Set V)) (hc : ∀ x, ¬ M.IsColoop x) {p : V} (hp : p ∈ K)
    {w : Chain V} (hw : TopCycle (M ／ (K : Set V)) w) :
    let P := K.filter fun a => M✶.closure {a} = M✶.closure {p}
    ∃ z : Chain V, TopCycle M z ∧ aggregateRestrict M K z = (P.card : ℤ) • w := by
  classical
  intro P
  let A := K \ P
  have hPK : P ⊆ K := filter_subset _ _
  have hPE : (P : Set V) = M✶.closure {p} := dual_class_eq_closure hK hc hp
  have hb (a : V) (ha : a ∈ P) : M✶.IsBasis {a} (P : Set V) := by
    have hcl := (mem_filter.mp ha).2
    have haN : M✶.IsNonloop a :=
      Matroid.isNonloop_of_not_isLoop (by simpa using hK.subset_ground (hPK ha)) (hc a)
    rw [hPE, ← hcl]
    exact haN.indep.isBasis_closure
  obtain ⟨hAI, hminor⟩ := delete_class_link hK hPK (hb p (mem_filter.mpr ⟨hp, rfl⟩))
  have hno (a : V) : ¬ (M ＼ (P : Set V)).IsColoop a := by
    rw [Matroid.IsColoop, Matroid.dual_delete, Matroid.IsLoop, Matroid.contract_loops_eq,
      hPE, Matroid.closure_closure]
    simp
  have htarget : TopCycle ((M ＼ (P : Set V)) ／ (A : Set V)) (shuffleSign P A • w) :=
    (topCycles _).smul_mem _ (hminor.symm ▸ hw)
  obtain ⟨v, hv, hvr⟩ := (exists_topCycle_linkRestrict_iff_coloop hAI _).2
    ⟨htarget, fun ⟨a, _, ha⟩ => (hno a ha).elim⟩
  refine ⟨signedJoin P (simplexBoundary P) v, join_class_topCycle hb hv, funext fun T => ?_⟩
  rw [aggregateRestrict, Finset.sum_apply]
  by_cases hT : (M ／ (K : Set V)).IsBase (T : Set V)
  · simp only [restrictChain, ite_eq_left hT]
    have hsum : (∑ a ∈ K, restrictionSign K a T *
        signedJoin P (simplexBoundary P) v (T ∪ K.erase a)) =
          ∑ a ∈ K, if a ∈ P then w T else 0 := by
      apply sum_congr rfl
      intro a ha
      rw [class_join_coords (a := a) hPK (contract_base_disjoint hT)]
      by_cases hap : a ∈ P
      · rw [ite_eq_left hap, ite_eq_left hap, hvr]
        change shuffleSign P A * (shuffleSign P A * w T) = w T
        rw [← mul_assoc, shuffleSign_sq, one_mul]
      · rw [ite_eq_right hap, ite_eq_right hap]
    have hfilter : (K.filter fun a => a ∈ P) = P := by
      ext a
      simp [and_iff_right_of_imp (fun h : a ∈ P => hPK h)]
    rw [hsum, ← sum_filter, hfilter, sum_const]
    simp
  · simp [restrictChain, hT, hw.vanishes T hT]

private noncomputable def aggregateLinear (M : Matroid V) (K : Finset V) :
    Chain V →ₗ[ℤ] Chain V where
  toFun := aggregateRestrict M K
  map_add' z w := by
    classical
    funext T
    simp only [aggregateRestrict, Pi.add_apply, Finset.sum_apply]
    by_cases hT : (M ／ (K : Set V)).IsBase (T : Set V)
    · simp only [restrictChain, ite_eq_left hT, Pi.add_apply, mul_add, sum_add_distrib]
    · simp [restrictChain, hT]
  map_smul' n z := by
    classical
    funext T
    simp only [aggregateRestrict, Finset.sum_apply, RingHom.id_apply, Pi.smul_apply,
      zsmul_eq_mul]
    by_cases hT : (M ／ (K : Set V)).IsBase (T : Set V)
    · simp only [restrictChain, ite_eq_left hT, mul_sum]
      apply sum_congr rfl
      intro a _
      exact mul_left_comm _ _ _
    · simp [restrictChain, hT]

/-- The image of integral aggregate restriction along any circuit is exactly
the dual class-size gcd times the integral top-cycle lattice of its contraction. -/
theorem exists_topCycle_aggregateRestrict_iff {M : Matroid V} {K : Finset V}
    (hK : M.IsCircuit (K : Set V)) (u : Chain V) :
    (∃ z : Chain V, TopCycle M z ∧ aggregateRestrict M K z = u) ↔
      ∃ w : Chain V, TopCycle (M ／ (K : Set V)) w ∧
        u = (CircuitRestrictionImage.dualClassGcd M K : ℤ) • w := by
  classical
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact aggregateRestrict_mem_gcd_smul hK hz
  rintro ⟨w, hw, rfl⟩
  let L := aggregateLinear M K
  by_cases hc : ∃ a, M.IsColoop a
  · obtain ⟨a, ha⟩ := hc
    have haK : a ∉ (K : Set V) := fun h => hK.not_isColoop_of_mem h ha
    have ha' : (M ／ (K : Set V)).IsColoop a := Matroid.contract_isColoop_iff.2 ⟨ha, haK⟩
    rw [topCycle_eq_zero_of_isColoop ha' hw, smul_zero]
    exact ⟨0, (topCycles M).zero_mem, L.map_zero⟩
  · let f : V → Set V := fun a => M✶.closure {a}
    let S := K.image f
    let size : Set V → ℕ := fun c => (K.filter fun a => f a = c).card
    obtain ⟨q, hq⟩ := CircuitRestrictionImage.gcd_eq_sum S size
    have hwitness (c : S) :
        ∃ z : topCycles M, L z.val = (size c.val : ℤ) • w := by
      obtain ⟨a, ha, he⟩ := mem_image.mp c.property
      obtain ⟨z, hz, hzr⟩ := class_multiple_image hK (fun a h => hc ⟨a, h⟩) ha hw
      refine ⟨⟨z, hz⟩, ?_⟩
      change aggregateRestrict M K z = (size c.val : ℤ) • w
      rw [← he]
      exact hzr
    choose v hv using hwitness
    let g : Set V → topCycles M := fun c => if h : c ∈ S then v ⟨c, h⟩ else 0
    let Z : topCycles M := ∑ c ∈ S, q c • g c
    refine ⟨Z.val, Z.property, ?_⟩
    change L Z.val = _
    simp only [Z, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
    change _ = ((S.gcd size : ℕ) : ℤ) • w
    rw [hq, sum_smul]
    apply sum_congr rfl
    intro c hc'
    have hg : L (g c).val = (size c : ℤ) • w := by
      change L ((if h : c ∈ S then v ⟨c, h⟩ else 0 : topCycles M).val) = _
      rw [dite_eq_left hc']
      exact hv ⟨c, hc'⟩
    rw [hg, smul_smul, mul_comm]

end D5.S3.Combinatorics.Matroids.IntegralCircuitImage
