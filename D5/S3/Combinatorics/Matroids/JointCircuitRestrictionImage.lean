/- GID: D5/S3/Combinatorics/Matroids/JointCircuitRestrictionImage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/JointCircuitRestrictionImage
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The simultaneous integral circuit restriction image in dual rank two. -/

module

public import D5.S3.Combinatorics.Matroids.IntegralCircuitImage
public import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.JointCircuitRestrictionImage

open OrderedCycleFactorization CircuitRestrictionImage IntegralCircuitImage
open CircuitCycleDecomposition (restrictChain restrictionSign)
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

variable {V : Type*} [LinearOrder V]

/-- The distinct dual parallel-class labels, given by singleton closures on the ground. -/
noncomputable def dualClasses (M : Matroid V) (E : Finset V) : Finset (Set V) := by
  classical
  exact E.image fun a => M✶.closure {a}

/-- The ground vertices in the fiber of a dual singleton closure. -/
noncomputable def classVertices (M : Matroid V) (E : Finset V) (P : Set V) : Finset V := by
  classical
  exact E.filter fun a => M✶.closure {a} = P

/-- The oriented integral generator for the contraction by the complementary circuit. -/
def contractionGenerator (K P : Finset V) : Chain V :=
  ((-1 : ℤ) ^ (K.card - 1) * shuffleSign K P) • simplexBoundary P

omit [LinearOrder V] in
private lemma dual_base_iff_classes {M : Matroid V} {E : Finset V}
    (hr : M✶.eRank = 2) (hn : ∀ a ∈ E, M✶.IsNonloop a)
    {a b : V} (ha : a ∈ E) (hb : b ∈ E) :
    M✶.IsBase {a, b} ↔ M✶.closure {a} ≠ M✶.closure {b} := by
  by_cases hab : a = b
  · subst b
    simp only [ne_self_iff_false, iff_false]
    intro h
    have hc := h.encard_eq_eRank.trans hr
    simp at hc
  rw [pair_base_iff_indep (fun _ h => h.encard_eq_eRank.trans hr) hab]
  have h := (hn a ha).closure_eq_closure_iff_eq_or_dep (hn b hb)
  simpa only [hab, false_or, not_not] using not_congr h.symm

private lemma primal_base_iff_classes {M : Matroid V} {E : Finset V}
    (hE : M.E = (E : Set V)) (hr : M✶.eRank = 2) (hn : ∀ a ∈ E, M✶.IsNonloop a)
    {a b : V} (ha : a ∈ E) (hb : b ∈ E) :
    M.IsBase (↑(E \ {a, b}) : Set V) ↔ M✶.closure {a} ≠ M✶.closure {b} := by
  have hsub : ({a, b} : Finset V) ⊆ E := insert_subset ha (singleton_subset_iff.mpr hb)
  rw [← dual_base_iff_classes hr hn ha hb]
  simpa only [coe_insert, coe_singleton] using (dual_complement_base hE hsub).symm

private lemma indep_iff_cross {M : Matroid V} {E K : Finset V}
    (hE : M.E = (E : Set V)) (hr : M✶.eRank = 2) (hn : ∀ a ∈ E, M✶.IsNonloop a)
    (hK : K ⊆ E) :
    M.Indep (K : Set V) ↔
      ∃ a ∈ E \ K, ∃ b ∈ E \ K, M✶.closure {a} ≠ M✶.closure {b} := by
  have hsub : (K : Set V) ⊆ M✶.E := by simpa [hE] using coe_subset.mpr hK
  rw [← Matroid.dual_coindep_iff, Matroid.coindep_iff_exists hsub,
    Matroid.dual_ground, hE, ← coe_sdiff]
  constructor
  · rintro ⟨B, hB, hBsub⟩
    obtain ⟨a, b, _, rfl⟩ := Set.encard_eq_two.mp (hB.encard_eq_eRank.trans hr)
    have ha : a ∈ E \ K := hBsub (by simp)
    have hb : b ∈ E \ K := hBsub (by simp)
    exact ⟨a, ha, b, hb, (dual_base_iff_classes hr hn (mem_sdiff.mp ha).1
      (mem_sdiff.mp hb).1).1 hB⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨{a, b}, (dual_base_iff_classes hr hn (mem_sdiff.mp ha).1
      (mem_sdiff.mp hb).1).2 hab, Set.insert_subset (show a ∈ ↑(E \ K) from ha)
        (Set.singleton_subset_iff.mpr (show b ∈ ↑(E \ K) from hb))⟩

private lemma erase_complement {E K : Finset V} (hK : K ⊆ E) {a : V} (ha : a ∈ K) :
    E \ K.erase a = insert a (E \ K) := by
  ext x
  by_cases hxa : x = a
  · subst x
    simp [hK ha]
  · simp [hxa]

private lemma isCircuit_iff_exists_class {M : Matroid V} {E K : Finset V}
    (hE : M.E = (E : Set V)) (hr : M✶.eRank = 2) (hn : ∀ a ∈ E, M✶.IsNonloop a) :
    M.IsCircuit (K : Set V) ↔
      ∃ P ∈ dualClasses M E, K = E \ classVertices M E P := by
  classical
  constructor
  · intro hC
    have hKe : K ⊆ E := coe_subset.mp (hE ▸ hC.subset_ground)
    have hsame (a b : V) (ha : a ∈ E \ K) (hb : b ∈ E \ K) :
        M✶.closure {a} = M✶.closure {b} := by
      by_contra hne
      exact hC.dep.not_indep ((indep_iff_cross hE hr hn hKe).2 ⟨a, ha, b, hb, hne⟩)
    have herase (x : V) (hx : x ∈ K) :
        ∃ a ∈ insert x (E \ K), ∃ b ∈ insert x (E \ K),
          M✶.closure {a} ≠ M✶.closure {b} := by
      rw [← erase_complement hKe hx]
      exact (indep_iff_cross hE hr hn ((erase_subset x K).trans hKe)).1
        (circuit_erase_basis hC hx).indep
    obtain ⟨x, hx⟩ := hC.nonempty
    obtain ⟨a, ha⟩ : (E \ K).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty.mp h] at herase
      simpa using herase x hx
    have hnot (b : V) (hb : b ∈ K) : M✶.closure {b} ≠ M✶.closure {a} := by
      intro he
      obtain ⟨s, hs, t, ht, hst⟩ := herase b hb
      have hall (u : V) (hu : u ∈ insert b (E \ K)) :
          M✶.closure {u} = M✶.closure {a} := by
        rcases mem_insert.mp hu with rfl | hu
        · exact he
        · exact hsame u a hu ha
      exact hst ((hall s hs).trans (hall t ht).symm)
    refine ⟨_, mem_image_of_mem (fun b => M✶.closure {b}) (mem_sdiff.mp ha).1, ?_⟩
    ext b
    by_cases hb : b ∈ K
    · simp [hb, hKe hb, classVertices, hnot b hb]
    · by_cases hbe : b ∈ E
      · simp [hb, hbe, classVertices, hsame b a (mem_sdiff.mpr ⟨hbe, hb⟩) ha]
      · simp [hb, hbe]
  · rintro ⟨P, hP, rfl⟩
    let S := classVertices M E P
    have hSE : S ⊆ E := filter_subset _ _
    have hsplit : E \ (E \ S) = S := Finset.sdiff_sdiff_eq_self hSE
    obtain ⟨a, ha, haP⟩ := mem_image.mp hP
    have haS : a ∈ S := mem_filter.mpr ⟨ha, haP⟩
    rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep]
    have hsub : (↑(E \ S) : Set V) ⊆ M.E := hE.symm ▸ coe_subset.mpr sdiff_subset
    refine ⟨(Matroid.not_indep_iff hsub).1 ?_, ?_⟩
    · rw [indep_iff_cross hE hr hn sdiff_subset, hsplit]
      rintro ⟨b, hb, c, hc, hbc⟩
      exact hbc ((mem_filter.mp hb).2.trans (mem_filter.mp hc).2.symm)
    · intro b hb
      change b ∈ E \ S at hb
      rw [← coe_singleton, ← coe_sdiff, ← erase_eq]
      rw [indep_iff_cross hE hr hn ((erase_subset b (E \ S)).trans sdiff_subset),
        erase_complement sdiff_subset hb, hsplit]
      exact ⟨b, mem_insert_self _ _, a, mem_insert_of_mem haS, fun he =>
        (mem_sdiff.mp hb).2 (mem_filter.mpr ⟨(mem_sdiff.mp hb).1, he.trans haP⟩)⟩

variable [Fintype V]

private lemma potential_iff_topCycle {M : Matroid V} {E : Finset V}
    (hE : M.E = (E : Set V)) (hr : M✶.eRank = 2) (hn : ∀ a ∈ E, M✶.IsNonloop a)
    (p : V → ℤ) :
    TopCycle M (potentialChain E p) ↔
      ∀ a ∈ E, ∀ b ∈ E, M✶.closure {a} = M✶.closure {b} → p a = p b := by
  constructor
  · intro hz a ha b hb hcl
    by_cases hab : a = b
    · rw [hab]
    have hz' := hz.vanishes (E \ {a, b}) (fun h => (primal_base_iff_classes hE hr hn ha hb).1 h hcl)
    rw [potentialChain_pair p ha hb hab] at hz'
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left
      (mul_ne_zero (insertionSign_ne_zero _ _) (insertionSign_ne_zero _ _)))).symm
  · intro hconst
    refine ⟨?_, potentialChain_cycle E p⟩
    intro F hF
    by_contra hz
    obtain ⟨a, ha, b, hb, hab, rfl⟩ := potentialChain_support hz
    have hcl := not_ne_iff.mp (mt (primal_base_iff_classes hE hr hn ha hb).2 hF)
    exact hz (by rw [potentialChain_pair p ha hb hab, hconst a ha b hb hcl, sub_self, mul_zero])

private lemma recover_potential {M : Matroid V} {E : Finset V}
    (hE : M.E = (E : Set V)) (hr : M✶.eRank = 2)
    {x : V} (hx : x ∈ E) {z : Chain V} (hz : TopCycle M z) :
    ∃ p : V → ℤ, z = potentialChain E p := by
  classical
  let p (a : V) :=
    if a = x then 0 else
      -((insertionSign (E \ {a, x}) a * insertionSign E x) * z (E \ {a, x}))
  have hp (a : V) (ha : a ∈ E) (hax : a ≠ x) :
      z (E \ {a, x}) = potentialChain E p (E \ {a, x}) := by
    rw [potentialChain_pair p ha hx hax]
    simp only [p, ite_eq_left rfl, ite_eq_right hax, zero_sub, neg_neg]
    rw [← mul_assoc, show (insertionSign (E \ {a, x}) a * insertionSign E x) *
      (insertionSign (E \ {a, x}) a * insertionSign E x) = 1 by
        unfold insertionSign
        rw [← pow_add, sign_sq], one_mul]
  have hface {F : Finset V} (hxF : x ∉ F)
      (h : ∃ a ∈ E, ∃ b ∈ E, a ≠ b ∧ F = E \ {a, b}) :
      ∃ a ∈ E, a ≠ x ∧ F = E \ {a, x} := by
    obtain ⟨a, ha, b, hb, hab, rfl⟩ := h
    have hxb : x = a ∨ x = b := by
      by_contra h
      exact hxF (mem_sdiff.mpr ⟨hx, by simpa using h⟩)
    rcases hxb with rfl | rfl
    · exact ⟨b, hb, hab.symm, by rw [pair_comm]⟩
    · exact ⟨a, ha, hab, rfl⟩
  refine ⟨p, cycle_eq_of_away (x := x) hz.cycle (potentialChain_cycle _ _) ?_⟩
  intro F hxF
  by_cases h : ∃ a ∈ E, a ≠ x ∧ F = E \ {a, x}
  · obtain ⟨a, ha, hax, rfl⟩ := h
    exact hp a ha hax
  rw [hz.vanishes F (fun hF => h (hface hxF (primal_base_complement_pair hE hF
    (fun _ hB => hB.encard_eq_eRank.trans hr))))]
  by_contra hw
  exact h (hface hxF (potentialChain_support (Ne.symm hw)))


omit [Fintype V] in
private lemma erase_pair_face {E K S : Finset V} {a b : V}
    (hKS : Disjoint K S) (hpart : K ∪ S = E) (ha : a ∈ K) (hb : b ∈ S) :
    S.erase b ∪ K.erase a = E \ {a, b} := by
  have haS : a ∉ S := fun h => disjoint_left.mp hKS ha h
  rw [← hpart]
  ext x
  by_cases hx : x ∈ S
  · have hxK : x ∉ K := fun h => disjoint_left.mp hKS h hx
    have hxa : x ≠ a := fun he => haS (he ▸ hx)
    simp [hx, hxK, hxa]
  · have hxb : x ≠ b := fun he => hx (he.symm ▸ hb)
    simp [hx, hxb, and_comm]

omit [Fintype V] in
private lemma contract_bases {M : Matroid V} {E : Finset V} {P : Set V}
    (hE : M.E = (E : Set V)) (hr : M✶.eRank = 2) (hn : ∀ a ∈ E, M✶.IsNonloop a)
    (hP : P ∈ dualClasses M E) (T : Finset V) :
    let S := classVertices M E P
    let K := E \ S
    (M ／ (K : Set V)).IsBase (T : Set V) ↔ ∃ b ∈ S, T = S.erase b := by
  classical
  intro S K
  have hC := (isCircuit_iff_exists_class hE hr hn).2 ⟨P, hP, rfl⟩
  obtain ⟨a, ha⟩ := hC.nonempty
  have haK : a ∈ K := ha
  have hSE : S ⊆ E := filter_subset _ _
  have hKS : Disjoint K S := disjoint_sdiff.symm
  have hpart : K ∪ S = E := by rw [sdiff_union_of_subset hSE]
  constructor
  · intro hT
    have hd := contract_base_disjoint hT
    have hTS : T ⊆ S := by
      intro x hx
      have h := hT.subset_ground (show x ∈ (T : Set V) from hx)
      change x ∈ M.E ∧ x ∉ (K : Set V) at h
      have hxE : x ∈ (E : Set V) := hE ▸ h.1
      by_contra hxS
      exact h.2 (mem_sdiff.mpr ⟨hxE, hxS⟩)
    have hB := (contract_base_iff (circuit_erase_basis hC ha) hd).1 hT
    obtain ⟨u, hu, v, hv, huv, hF⟩ := primal_base_complement_pair hE hB
      (fun _ hB => hB.encard_eq_eRank.trans hr)
    have haF : a ∉ T ∪ K.erase a := by
      simp [show a ∉ T from fun h => disjoint_left.mp hd h haK]
    have hapair : a = u ∨ a = v := by
      rw [hF] at haF
      by_contra h
      exact haF (mem_sdiff.mpr ⟨(mem_sdiff.mp haK).1, by simpa using h⟩)
    have finish (b : V) (hb : b ∈ E) (hab : a ≠ b)
        (heq : T ∪ K.erase a = E \ {a, b}) :
        ∃ b ∈ S, T = S.erase b := by
      have hbS : b ∈ S := by
        by_contra hbS
        have hbK : b ∈ K := mem_sdiff.mpr ⟨hb, hbS⟩
        exact (mem_sdiff.mp (heq ▸ mem_union_right T (mem_erase.mpr ⟨hab.symm, hbK⟩))).2 (by simp)
      refine ⟨b, hbS, ?_⟩
      have hUnion := heq.trans (erase_pair_face hKS hpart haK hbS).symm
      ext x
      by_cases hx : x ∈ S
      · have hxK : x ∉ K := fun h => disjoint_left.mp hKS h hx
        exact (show x ∈ T ∪ K.erase a ↔ x ∈ S.erase b ∪ K.erase a by rw [hUnion])
          |> fun h => by simpa [hxK, mem_erase] using h
      · simp [mem_erase, hx, show x ∉ T from fun h => hx (hTS h)]
    rcases hapair with rfl | rfl
    · exact finish v hv huv hF
    · exact finish u hu huv.symm (by rwa [pair_comm])
  · rintro ⟨b, hb, rfl⟩
    apply (contract_base_iff (circuit_erase_basis hC ha)
      (hKS.symm.mono_left (erase_subset _ _))).2
    rw [erase_pair_face hKS hpart haK hb, primal_base_iff_classes hE hr hn (mem_sdiff.mp haK).1 (hSE hb)]
    intro he
    exact (mem_sdiff.mp haK).2
      (mem_filter.mpr ⟨(mem_sdiff.mp haK).1, he.trans (mem_filter.mp hb).2⟩)

omit [Fintype V] in
private lemma simplex_sign_on_pair {E K S : Finset V} {a b : V}
    (hKS : Disjoint K S) (hpart : K ∪ S = E) (ha : a ∈ K) (hb : b ∈ S) :
    let A := K.erase a
    let T := S.erase b
    restrictionSign K a T * (insertionSign (T ∪ A) a * insertionSign E b) =
      (-1 : ℤ) ^ K.card * shuffleSign K S * insertionSign T b := by
  classical
  intro A T
  have hTA : Disjoint T A := hKS.symm.mono (erase_subset _ _) (erase_subset _ _)
  have hTK : Disjoint T K := hKS.symm.mono_left (erase_subset _ _)
  have haF : a ∉ T ∪ A := by
    simp [A, show a ∉ T from fun h => disjoint_left.mp hTK h ha]
  have hbR : b ∉ K ∪ T := by
    simp [T, show b ∉ K from fun h => disjoint_left.mp hKS h hb]
  have hL := left_insertion_sign (T ∪ A) A haF
  rw [union_inter_cancel_right, union_sdiff_cancel_right hTA, insert_erase ha] at hL
  have hsignL : restrictionSign K a T * insertionSign (T ∪ A) a = shuffleSign K T := by
    have hs : insertionSign (T ∪ A) a * insertionSign (T ∪ A) a = 1 := sign_sq _
    calc
      _ = (shuffleSign A T * insertionSign A a) * insertionSign (T ∪ A) a := by
        unfold restrictionSign
        ring
      _ = _ := by rw [← hL, mul_right_comm, hs, one_mul]
  have hR := right_insertion_sign (K ∪ T) K hbR
  rw [union_inter_cancel_left, union_sdiff_cancel_left hTK.symm, insert_erase hb] at hR
  have hE' : insert b (K ∪ T) = E := by
    rw [union_comm K T, ← insert_union, insert_erase hb, union_comm, hpart]
  have hEb : insertionSign E b = insertionSign (K ∪ T) b := by
    rw [← hE']
    simp [insertionSign, filter_insert]
  have hs : insertionSign (K ∪ T) b * insertionSign (K ∪ T) b = 1 := sign_sq _
  have hpar : (-1 : ℤ) ^ K.card * (-1) ^ K.card = 1 := sign_sq _
  have hsT : insertionSign T b * insertionSign T b = 1 := sign_sq _
  calc
    _ = shuffleSign K T * insertionSign (K ∪ T) b := by
      rw [← mul_assoc, hsignL, hEb]
    _ = ((-1 : ℤ) ^ K.card * (-1) ^ K.card) *
        (insertionSign T b * insertionSign T b) *
        (shuffleSign K T * insertionSign (K ∪ T) b) := by rw [hpar, hsT, one_mul, one_mul]
    _ = (shuffleSign K T * (-1 : ℤ) ^ K.card * insertionSign T b) *
        ((-1 : ℤ) ^ K.card * insertionSign (K ∪ T) b * insertionSign T b) := by ring
    _ = _ := by
      rw [← hR]
      calc
        _ = (insertionSign (K ∪ T) b * insertionSign (K ∪ T) b) *
          ((-1 : ℤ) ^ K.card * shuffleSign K S * insertionSign T b) := by ring
        _ = _ := by rw [hs, one_mul]


private lemma aggregate_potential {M : Matroid V} {E : Finset V} {P : Set V}
    (hE : M.E = (E : Set V)) (hr : M✶.eRank = 2) (hn : ∀ a ∈ E, M✶.IsNonloop a)
    (hP : P ∈ dualClasses M E) (q : Set V → ℤ) :
    let S := classVertices M E P
    let K := E \ S
    let p : V → ℤ := fun a => q (M✶.closure {a})
    aggregateRestrict M K (potentialChain E p) =
      ((∑ a ∈ E, p a) - (E.card : ℤ) * q P) • contractionGenerator K S := by
  classical
  intro S K p
  have hSE : S ⊆ E := filter_subset _ _
  have hKS : Disjoint K S := disjoint_sdiff.symm
  have hpart : K ∪ S = E := sdiff_union_of_subset hSE
  have hC := (isCircuit_iff_exists_class hE hr hn).2 ⟨P, hP, rfl⟩
  have hKpos : 0 < K.card := card_pos.mpr hC.nonempty
  have hpar : (-1 : ℤ) ^ K.card = -((-1 : ℤ) ^ (K.card - 1)) := by
    conv_lhs => rw [show K.card = K.card - 1 + 1 by omega, pow_succ]
    ring
  have hp (a : V) (ha : a ∈ S) : p a = q P := congrArg q (mem_filter.mp ha).2
  funext T
  by_cases hT : (M ／ (K : Set V)).IsBase (T : Set V)
  · obtain ⟨b, hb, rfl⟩ := (contract_bases hE hr hn hP T).1 hT
    have hsum : (∑ a ∈ K, (p a - q P)) = (∑ a ∈ E, p a) - (E.card : ℤ) * q P := by
      calc
        _ = ∑ a ∈ E, (p a - q P) := by
          rw [← hpart, sum_union hKS]
          rw [sum_eq_zero (fun a ha => sub_eq_zero.mpr (hp a ha)), add_zero]
        _ = _ := by simp [sum_sub_distrib]
    change b ∈ S at hb
    change (M ／ (K : Set V)).IsBase (↑(S.erase b) : Set V) at hT
    change (aggregateRestrict M K (potentialChain E p)) (S.erase b) =
      ((∑ a ∈ E, p a) - (E.card : ℤ) * q P) • contractionGenerator K S (S.erase b)
    simp only [aggregateRestrict, Finset.sum_apply, restrictChain, ite_eq_left hT,
      contractionGenerator, Pi.smul_apply, smul_eq_mul, simplexBoundary_erase hb]
    rw [← hsum, sum_mul]
    apply sum_congr rfl
    intro a ha
    have hface := erase_pair_face hKS hpart ha hb
    have hab : a ≠ b := fun h => disjoint_left.mp hKS ha (h.symm ▸ hb)
    rw [hface, potentialChain_pair p (mem_sdiff.mp ha).1 (hSE hb) hab, ← hface, ← mul_assoc,
      simplex_sign_on_pair hKS hpart ha hb, hp b hb, hpar]
    ring
  · have hvan : simplexBoundary S T = 0 := by
      by_contra h
      exact hT ((contract_bases hE hr hn hP T).2 (simplexBoundary_support.mp h))
    simp [aggregateRestrict, Finset.sum_apply, restrictChain, hT, contractionGenerator, hvan]

omit [Fintype V] in
private lemma contractionGenerator_ne_zero {M : Matroid V} {E : Finset V} {P : Set V}
    (hP : P ∈ dualClasses M E) :
    contractionGenerator (E \ classVertices M E P) (classVertices M E P) ≠ 0 := by
  classical
  obtain ⟨b, hb, hbP⟩ := mem_image.mp hP
  let S := classVertices M E P
  have hbS : b ∈ S := mem_filter.mpr ⟨hb, hbP⟩
  intro h
  have hval := congrFun h (S.erase b)
  change contractionGenerator (E \ S) S (S.erase b) = 0 at hval
  simp only [contractionGenerator, Pi.smul_apply, smul_eq_mul,
    simplexBoundary_erase hbS] at hval
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num) : shuffleSign (E \ S) S ≠ 0))
    (insertionSign_ne_zero _ _)) hval

omit [Fintype V] [LinearOrder V] in
private lemma e_nonempty {M : Matroid V} {E : Finset V} (hE : M.E = (E : Set V))
    (hr : M✶.eRank = 2) : E.Nonempty := by
  obtain ⟨B, hB⟩ := M✶.exists_isBase
  obtain ⟨a, b, _, rfl⟩ := Set.encard_eq_two.mp (hB.encard_eq_eRank.trans hr)
  exact ⟨a, show a ∈ (E : Set V) from hE ▸ hB.subset_ground (by simp)⟩

/-- All circuit aggregates of one chain, indexed by dual singleton closures. -/
noncomputable def jointRestrict (M : Matroid V) (E : Finset V) (z : Chain V) (P : Set V) :
    Chain V :=
  aggregateRestrict M (E \ classVertices M E P) z

/-- One integral top cycle realizes all signed circuit aggregates precisely when the
class-size-weighted sum is zero and all labels are congruent modulo the ground size. -/
theorem exists_topCycle_joint_aggregateRestrict_iff
    (M : Matroid V) (E : Finset V) (hE : M.E = (E : Set V)) (hr : M✶.eRank = 2)
    (hn : ∀ a ∈ E, M✶.IsNonloop a) (y : Set V → ℤ) :
    (∃ z : Chain V, TopCycle M z ∧ ∀ P ∈ dualClasses M E,
      jointRestrict M E z P =
        y P • contractionGenerator (E \ classVertices M E P) (classVertices M E P)) ↔
      (∑ P ∈ dualClasses M E, ((classVertices M E P).card : ℤ) * y P) = 0 ∧
        ∀ P ∈ dualClasses M E, ∀ Q ∈ dualClasses M E, (E.card : ℤ) ∣ y P - y Q := by
  classical
  let cl (a : V) := M✶.closure {a}
  have hlabel (a : V) (ha : a ∈ E) : cl a ∈ dualClasses M E := mem_image_of_mem cl ha
  obtain ⟨x, hx⟩ := e_nonempty hE hr
  have hnE : (E.card : ℤ) ≠ 0 := by exact_mod_cast (card_ne_zero.mpr ⟨x, hx⟩)
  have hweights : (∑ P ∈ dualClasses M E, ((classVertices M E P).card : ℤ) * y P) =
      ∑ a ∈ E, y (cl a) := (CircuitRestrictionImage.sum_fibers (S := E) cl y).symm
  constructor
  · rintro ⟨z, hz, hread⟩
    obtain ⟨p, rfl⟩ := recover_potential hE hr hx hz
    have hconst := (potential_iff_topCycle hE hr hn p).1 hz
    let q (P : Set V) : ℤ := if h : ∃ a ∈ E, cl a = P then p h.choose else 0
    have hq (a : V) (ha : a ∈ E) : p a = q (cl a) := by
      have h : ∃ b ∈ E, cl b = cl a := ⟨a, ha, rfl⟩
      simp only [q, dite_eq_left h]
      exact hconst a ha h.choose h.choose_spec.1 h.choose_spec.2.symm
    have hpchain : potentialChain E p = potentialChain E (fun a => q (cl a)) := by
      apply cycle_eq_of_away (x := x) (potentialChain_cycle _ _) (potentialChain_cycle _ _)
      intro F _
      by_cases h : ∃ a ∈ E, ∃ b ∈ E, a ≠ b ∧ F = E \ {a, b}
      · obtain ⟨a, ha, b, hb, hab, rfl⟩ := h
        rw [potentialChain_pair p ha hb hab, potentialChain_pair _ ha hb hab, hq a ha, hq b hb]
      · rw [not_ne_iff.mp (mt potentialChain_support h),
          not_ne_iff.mp (mt potentialChain_support h)]
    let total := ∑ a ∈ E, q (cl a)
    have hy (P : Set V) (hP : P ∈ dualClasses M E) :
        y P = total - (E.card : ℤ) * q P := by
      have he := hread P hP
      rw [jointRestrict, hpchain, aggregate_potential hE hr hn hP q] at he
      obtain ⟨T, hT⟩ := Function.ne_iff.mp (contractionGenerator_ne_zero hP)
      have hcoef := congrFun he T
      exact (mul_right_cancel₀ hT hcoef).symm
    refine ⟨?_, ?_⟩
    · rw [hweights]
      calc
        _ = ∑ a ∈ E, (total - (E.card : ℤ) * q (cl a)) :=
          sum_congr rfl fun a ha => hy _ (hlabel a ha)
        _ = 0 := by simp [sum_sub_distrib, ← mul_sum, total]
    · intro P hP Q hQ
      refine ⟨q Q - q P, ?_⟩
      rw [hy P hP, hy Q hQ]
      ring
  · rintro ⟨hbalance, hdiv⟩
    rw [hweights] at hbalance
    let ref := cl x
    let q (P : Set V) : ℤ :=
      if h : (E.card : ℤ) ∣ y ref - y P then Classical.choose h else 0
    have hq (P : Set V) (hP : P ∈ dualClasses M E) :
        y ref - y P = (E.card : ℤ) * q P := by
      have h := hdiv ref (hlabel x hx) P hP
      simpa only [q, dite_eq_left h] using h.choose_spec
    let p (a : V) : ℤ := q (cl a)
    have htotal : (∑ a ∈ E, p a) = y ref := by
      apply mul_left_cancel₀ hnE
      calc
        _ = ∑ a ∈ E, (E.card : ℤ) * p a := mul_sum _ _ _
        _ = ∑ a ∈ E, (y ref - y (cl a)) := sum_congr rfl fun a ha => (hq _ (hlabel a ha)).symm
        _ = _ := by simp [sum_sub_distrib, hbalance]
    refine ⟨potentialChain E p, (potential_iff_topCycle hE hr hn p).2 ?_, ?_⟩
    · intro a _ b _ hab
      exact congrArg q hab
    · intro P hP
      rw [jointRestrict, aggregate_potential hE hr hn hP q]
      change ((∑ a ∈ E, p a) - (E.card : ℤ) * q P) • _ = _
      rw [htotal, ← hq P hP]
      congr 1
      ring

end D5.S3.Combinatorics.Matroids.JointCircuitRestrictionImage
