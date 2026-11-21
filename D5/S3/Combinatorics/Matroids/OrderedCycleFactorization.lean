/- GID: D5/S3/Combinatorics/Matroids/OrderedCycleFactorization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/OrderedCycleFactorization
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Signed circuit factorization of normalized ordered matroid cycles. -/

module

public import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Combinatorics.Colex
import Mathlib.Tactic.Ring

/-! Ordered augmented chain coordinates and circuit contraction. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.OrderedCycleFactorization

variable {V : Type*} [LinearOrder V]

/-- Integral coefficients in ambient ordered face coordinates. -/
abbrev Chain (V : Type*) := Finset V → ℤ

/-- The sign for inserting a vertex into an ordered ridge. -/
def insertionSign (R : Finset V) (x : V) : ℤ :=
  (-1) ^ (R.filter (· < x)).card

/-- Boundary, summing insertions from the specified vertex set. -/
def boundaryOn (U : Finset V) (z : Chain V) (R : Finset V) : ℤ :=
  ∑ x ∈ U \ R, insertionSign R x * z (insert x R)

/-- The orientation sign for concatenating two ordered faces. -/
def shuffleSign (A D : Finset V) : ℤ :=
  (-1) ^ (∑ a ∈ A, (D.filter (· < a)).card)

/-- Coordinate join along the partition into a circuit and its complement. -/
def signedJoin (C : Finset V) (u v : Chain V) (F : Finset V) : ℤ :=
  shuffleSign (F ∩ C) (F \ C) * (u (F ∩ C) * v (F \ C))

/-- The single oriented simplex in ambient coordinates, including the empty face. -/
def simplex (C F : Finset V) : ℤ :=
  if F = C then 1 else 0

/-- The oriented augmented boundary of the simplex on the circuit. -/
def simplexBoundary (C : Finset V) : Chain V :=
  boundaryOn C (simplex C)

private lemma sign_sq (n : ℕ) : ((-1 : ℤ) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow]
  norm_num

private lemma insertionSign_ne_zero (R : Finset V) (x : V) : insertionSign R x ≠ 0 :=
  pow_ne_zero _ (by norm_num)

private lemma shuffleSign_ne_zero (A D : Finset V) : shuffleSign A D ≠ 0 :=
  pow_ne_zero _ (by norm_num)

private lemma card_filter_partition (R C : Finset V) (x : V) :
    (R.filter (· < x)).card =
      ((R ∩ C).filter (· < x)).card + ((R \ C).filter (· < x)).card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext a
    simp only [mem_filter, mem_union, mem_inter, mem_sdiff]
    tauto
  · rw [disjoint_left]
    simp only [mem_filter, mem_inter, mem_sdiff]
    tauto

private lemma left_insertion_sign (R C : Finset V) {x : V}
    (hx : x ∉ R) :
    insertionSign R x * shuffleSign (insert x (R ∩ C)) (R \ C) =
      shuffleSign (R ∩ C) (R \ C) * insertionSign (R ∩ C) x := by
  unfold insertionSign shuffleSign
  rw [card_filter_partition R C x, sum_insert (fun h => hx (mem_inter.mp h).1), pow_add,
    pow_add]
  calc
    _ = ((-1 : ℤ) ^ (((R \ C).filter (· < x)).card) *
          (-1) ^ (((R \ C).filter (· < x)).card)) *
        ((-1) ^ (∑ a ∈ R ∩ C, ((R \ C).filter (· < a)).card) *
          (-1) ^ (((R ∩ C).filter (· < x)).card)) := by ring
    _ = _ := by rw [sign_sq, one_mul]

private lemma right_insertion_sign (R C : Finset V) {x : V}
    (hx : x ∉ R) :
    insertionSign R x * shuffleSign (R ∩ C) (insert x (R \ C)) =
      shuffleSign (R ∩ C) (R \ C) * (-1) ^ (R ∩ C).card *
        insertionSign (R \ C) x := by
  have hxd : x ∉ R \ C := fun h => hx (mem_sdiff.mp h).1
  have hsum :
      (∑ a ∈ R ∩ C, ((insert x (R \ C)).filter (· < a)).card) =
        (∑ a ∈ R ∩ C, ((R \ C).filter (· < a)).card) +
          ((R ∩ C).filter (x < ·)).card := by
    rw [card_eq_sum_ones, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    by_cases hxa : x < a
    · rw [filter_insert, ite_eq_left hxa, card_insert_of_notMem
        (fun h => hxd (mem_filter.mp h).1), ite_eq_left hxa]
    · simp [filter_insert, hxa]
  have hcard : ((R ∩ C).filter (· < x)).card + ((R ∩ C).filter (x < ·)).card =
      (R ∩ C).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext a
      by_cases ha : a ∈ R ∩ C
      · have hne : a ≠ x := fun h => hx (h ▸ (mem_inter.mp ha).1)
        rcases lt_or_gt_of_ne hne with h | h <;> simp [ha, h, h.not_gt]
      · simp [ha]
    · exact disjoint_left.mpr fun a ha hb => (mem_filter.mp ha).2.not_gt (mem_filter.mp hb).2
  unfold insertionSign shuffleSign
  rw [card_filter_partition R C x, hsum, ← hcard]
  simp only [pow_add]
  ring

/-- The augmented Leibniz rule in each ordered ridge coordinate. -/
theorem boundaryOn_signedJoin [Fintype V] (C R : Finset V) (u v : Chain V) :
    boundaryOn univ (signedJoin C u v) R =
      shuffleSign (R ∩ C) (R \ C) *
        (boundaryOn C u (R ∩ C) * v (R \ C) +
          (-1) ^ (R ∩ C).card * (u (R ∩ C) * boundaryOn (univ \ C) v (R \ C))) := by
  classical
  have hleft : (univ \ R).filter (· ∈ C) = C \ (R ∩ C) := by
    ext x
    simp only [mem_filter, mem_sdiff, mem_univ, true_and, mem_inter]
    tauto
  have hright : (univ \ R).filter (· ∉ C) = (univ \ C) \ (R \ C) := by
    ext x
    simp only [mem_filter, mem_sdiff, mem_univ, true_and]
    tauto
  unfold boundaryOn
  rw [← sum_filter_add_sum_filter_not _ (· ∈ C), hleft, hright, mul_add]
  congr 1
  · rw [sum_mul, mul_sum]
    apply sum_congr rfl
    intro x hx
    have hxC := (mem_sdiff.mp hx).1
    have hxR : x ∉ R := fun hr => (mem_sdiff.mp hx).2 (mem_inter.mpr ⟨hr, hxC⟩)
    have hA : insert x R ∩ C = insert x (R ∩ C) := by
      ext a
      simp only [mem_inter, mem_insert]
      aesop
    have hD : insert x R \ C = R \ C := by
      ext a
      simp only [mem_sdiff, mem_insert]
      aesop
    rw [signedJoin, hA, hD, ← mul_assoc, left_insertion_sign R C hxR]
    ring
  · rw [mul_sum, mul_sum, mul_sum]
    apply sum_congr rfl
    intro x hx
    have hxC := (mem_sdiff.mp (mem_sdiff.mp hx).1).2
    have hxR : x ∉ R := fun hr => (mem_sdiff.mp hx).2 (mem_sdiff.mpr ⟨hr, hxC⟩)
    have hA : insert x R ∩ C = R ∩ C := by
      ext a
      simp only [mem_inter, mem_insert]
      aesop
    have hD : insert x R \ C = insert x (R \ C) := by
      ext a
      simp only [mem_sdiff, mem_insert]
      aesop
    rw [signedJoin, hA, hD, ← mul_assoc, right_insertion_sign R C hxR]
    ring

private lemma insertion_pair (R : Finset V) {x y : V}
    (hx : x ∉ R) (hy : y ∉ R) (hxy : x ≠ y) :
    insertionSign R x * insertionSign (insert x R) y =
      -(insertionSign R y * insertionSign (insert y R) x) := by
  unfold insertionSign
  rcases lt_or_gt_of_ne hxy with h | h
  · rw [filter_insert, ite_eq_left h, card_insert_of_notMem (fun hm => hx (mem_filter.mp hm).1),
      pow_succ, filter_insert, ite_eq_right h.not_gt]
    ring
  · rw [filter_insert, ite_eq_right h.not_gt, filter_insert, ite_eq_left h,
      card_insert_of_notMem (fun hm => hy (mem_filter.mp hm).1), pow_succ]
    ring

private lemma boundaryOn_squared (U : Finset V) (z : Chain V) (R : Finset V) :
    boundaryOn U (boundaryOn U z) R = 0 := by
  classical
  let f (x y : V) := if y ∈ U \ insert x R then
    insertionSign R x * (insertionSign (insert x R) y * z (insert y (insert x R))) else 0
  have hsum : boundaryOn U (boundaryOn U z) R = ∑ x ∈ U \ R, ∑ y ∈ U \ R, f x y := by
    unfold boundaryOn
    apply sum_congr rfl
    intro x _
    rw [mul_sum]
    unfold f
    have hfilter : (U \ R).filter (· ∈ U \ insert x R) = U \ insert x R :=
      by
        ext y
        simp only [mem_filter, mem_sdiff, mem_insert]
        tauto
    rw [← sum_filter, hfilter]
  have hneg (x : V) (hx : x ∈ U \ R) (y : V) (hy : y ∈ U \ R) :
      f x y = -f y x := by
    by_cases he : x = y
    · subst y
      simp [f]
    have hxR := (mem_sdiff.mp hx).2
    have hyR := (mem_sdiff.mp hy).2
    have hyx : y ∈ U \ insert x R := mem_sdiff.mpr
      ⟨(mem_sdiff.mp hy).1, by simp [Ne.symm he, hyR]⟩
    have hxy : x ∈ U \ insert y R := mem_sdiff.mpr
      ⟨(mem_sdiff.mp hx).1, by simp [he, hxR]⟩
    simp only [f, hyx, hxy, ite_true, ← mul_assoc]
    rw [insertion_pair R hxR hyR he, insert_comm y x]
    ring
  have hs : (∑ x ∈ U \ R, ∑ y ∈ U \ R, f x y) =
      -(∑ x ∈ U \ R, ∑ y ∈ U \ R, f x y) := by
    calc
      _ = ∑ x ∈ U \ R, ∑ y ∈ U \ R, -f y x :=
        sum_congr rfl fun x hx => sum_congr rfl (hneg x hx)
      _ = ∑ y ∈ U \ R, ∑ x ∈ U \ R, -f y x := sum_comm
      _ = _ := by simp only [sum_neg_distrib]
  omega

private lemma simplexBoundary_erase {C : Finset V} {x : V} (hx : x ∈ C) :
    simplexBoundary C (C.erase x) = insertionSign (C.erase x) x := by
  have hd : C \ C.erase x = {x} := by
    ext a
    simp only [mem_sdiff, mem_erase, mem_singleton]
    constructor
    · tauto
    · rintro rfl
      simp [hx]
  simp [simplexBoundary, boundaryOn, hd, simplex, insert_erase hx]

private lemma simplexBoundary_support {C A : Finset V} :
    simplexBoundary C A ≠ 0 ↔ ∃ x ∈ C, A = C.erase x := by
  constructor
  · intro hn
    by_contra h
    apply hn
    apply sum_eq_zero
    intro x hx
    have hne : insert x A ≠ C := by
      intro he
      apply h
      exact ⟨x, (mem_sdiff.mp hx).1, by
        rw [← he, erase_insert (mem_sdiff.mp hx).2]⟩
    simp [simplex, hne]
  · rintro ⟨x, hx, rfl⟩
    rw [simplexBoundary_erase hx]
    exact insertionSign_ne_zero _ _

/-- Each vertex of an internally passive base admits a strictly smaller exchange. -/
def PassiveBase (M : Matroid V) (B : Finset V) : Prop :=
  M.IsBase (B : Set V) ∧
    ∀ a ∈ B, ∃ x ∉ B, x < a ∧ M.IsBase (↑(insert x (B.erase a)) : Set V)

/-- Top augmented cycles vanish on nonbases and have zero boundary at every ridge. -/
structure TopCycle [Fintype V] (M : Matroid V) (z : Chain V) : Prop where
  vanishes : ∀ F : Finset V, ¬ M.IsBase (F : Set V) → z F = 0
  cycle : ∀ R, boundaryOn univ z R = 0

/-- Kronecker-delta normalization on the internally passive bases. -/
structure Normalized [Fintype V] (M : Matroid V) (B : Finset V) (z : Chain V)
    : Prop extends TopCycle M z where
  coordinate : ∀ F, PassiveBase M F → z F = if F = B then 1 else 0

private lemma topCycle_ext [Fintype V] {M : Matroid V} {z w : Chain V}
    (hz : TopCycle M z) (hw : TopCycle M w)
    (hn : ∀ F, PassiveBase M F → z F = w F) : z = w := by
  classical
  by_contra hne
  let bad := univ.filter fun F : Finset V => z F ≠ w F
  have hb : bad.Nonempty := by
    obtain ⟨F, hF⟩ : ∃ F, z F ≠ w F := not_forall.mp (fun h => hne (funext h))
    exact ⟨F, mem_filter.mpr ⟨mem_univ _, hF⟩⟩
  obtain ⟨F, hF, hmax⟩ := exists_max_image bad toColex hb
  have hFne := (mem_filter.mp hF).2
  have hbase : M.IsBase (F : Set V) := by
    by_contra h
    exact hFne ((hz.vanishes F h).trans (hw.vanishes F h).symm)
  have hp : ¬ ∀ a ∈ F, ∃ x ∉ F, x < a ∧
      M.IsBase (↑(insert x (F.erase a)) : Set V) :=
    fun h => hFne (hn F ⟨hbase, h⟩)
  push Not at hp
  obtain ⟨a, ha, hactive⟩ := hp
  let R := F.erase a
  have haR : a ∉ R := notMem_erase _ _
  have heq : insert a R = F := insert_erase ha
  have hterms (x : V) (hx : x ∈ univ \ R) (hxa : x ≠ a) :
      z (insert x R) = w (insert x R) := by
    by_cases hxB : M.IsBase (↑(insert x R) : Set V)
    · have hxR := (mem_sdiff.mp hx).2
      have hxF : x ∉ F := fun h => hxR (mem_erase.mpr ⟨hxa, h⟩)
      have hax : a < x := lt_of_le_of_ne
        (le_of_not_gt fun h => hactive x hxF h hxB) (Ne.symm hxa)
      have hlt : toColex F < toColex (insert x R) := by
        rw [← heq]
        exact (Colex.insert_lt_insert haR hxR).2 hax
      by_contra hxne
      exact (not_le_of_gt hlt) (hmax _ (mem_filter.mpr ⟨mem_univ _, hxne⟩))
    · exact (hz.vanishes _ hxB).trans (hw.vanishes _ hxB).symm
  have hsum :
      ∑ x ∈ univ \ R, insertionSign R x * (z (insert x R) - w (insert x R)) = 0 := by
    calc
      _ = boundaryOn univ z R - boundaryOn univ w R := by
        simp only [boundaryOn, ← sum_sub_distrib, mul_sub]
      _ = _ := by rw [hz.cycle, hw.cycle, sub_zero]
  rw [sum_eq_single a] at hsum
  · rw [heq] at hsum
    exact hFne (sub_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left
      (insertionSign_ne_zero _ _)))
  · intro x hx hxa
    rw [hterms x hx hxa, sub_self, mul_zero]
  · exact fun h => (h (mem_sdiff.mpr ⟨mem_univ _, haR⟩)).elim

/-- A least nonloop of the matroid, in the ambient order. -/
def LeastNonloop (M : Matroid V) (e : V) : Prop :=
  M.IsNonloop e ∧ ∀ x, M.IsNonloop x → e ≤ x

private lemma not_passiveBase_of_mem_least {M : Matroid V} {F : Finset V} {e : V}
    (he : LeastNonloop M e) (hm : e ∈ F) : ¬ PassiveBase M F := by
  intro hF
  obtain ⟨x, _, hxe, hX⟩ := hF.2 e hm
  exact (not_lt_of_ge (he.2 x (hX.indep.isNonloop_of_mem
    (by simp : x ∈ (↑(insert x (F.erase e)) : Set V))))) hxe

private lemma contract_base_iff {M : Matroid V} {A G C : Finset V}
    (hA : M.IsBasis (A : Set V) (C : Set V)) (hd : Disjoint G C) :
    (M ／ (C : Set V)).IsBase (G : Set V) ↔ M.IsBase (↑(G ∪ A) : Set V) := by
  have hdis : Disjoint (G : Set V) (C : Set V) := by exact_mod_cast hd
  have hloops : (M ／ (A : Set V)).Coindep ((C : Set V) \ (A : Set V)) := by
    rw [Matroid.coindep_def]
    apply (Matroid.coloops_indep _).subset
    simpa only [Matroid.dual_coloops] using hA.sdiff_subset_loops_contract
  rw [Finset.coe_union, hA.contract_eq_contract_delete, hloops.delete_isBase_iff,
    hA.indep.contract_isBase_iff]
  exact ⟨fun h => h.1.1, fun h => ⟨⟨h, hdis.mono_right hA.subset⟩,
    hdis.mono_right Set.sdiff_subset⟩⟩

private lemma circuit_erase_basis {M : Matroid V} {C : Finset V} {x : V}
    (hC : M.IsCircuit (C : Set V)) (hx : x ∈ C) :
    M.IsBasis (↑(C.erase x) : Set V) (C : Set V) := by
  simpa using hC.sdiff_singleton_isBasis (show x ∈ (C : Set V) from hx)

private lemma erase_union_split {A G : Finset V} {a : V} (ha : a ∉ A) :
    (G ∪ A).erase a = G.erase a ∪ A := by
  ext x
  simp only [mem_erase, mem_union]
  by_cases h : x = a
  · subst x
    simp [ha]
  · simp [h]

private lemma passive_lift_iff {M : Matroid V} {C G : Finset V} {e : V}
    (hC : M.IsCircuit (C : Set V)) (heC : e ∈ C) (he : LeastNonloop M e)
    (hG : (M ／ (C : Set V)).IsBase (G : Set V)) :
    PassiveBase M (G ∪ C.erase e) ↔ PassiveBase (M ／ (C : Set V)) G := by
  classical
  let S := C.erase e
  have hS : M.IsBasis (S : Set V) (C : Set V) := circuit_erase_basis hC heC
  have hGC : Disjoint G C := by
    rw [disjoint_left]
    intro y hy hyC
    exact (hG.subset_ground (show y ∈ (G : Set V) from hy)).2 hyC
  have hGbase : M.IsBase (↑(G ∪ S) : Set V) := (contract_base_iff hS hGC).1 hG
  have heG : e ∉ G := fun hm => disjoint_left.mp hGC hm heC
  have heS : e ∉ S := notMem_erase _ _
  constructor
  · intro hP
    refine ⟨hG, fun a ha => ?_⟩
    have haS : a ∉ S := fun hm => disjoint_left.mp hGC ha (mem_of_mem_erase hm)
    obtain ⟨x, hx, hxa, hX⟩ := hP.2 a (mem_union_left _ ha)
    have hxG : x ∉ G := fun hm => hx (mem_union_left _ hm)
    have hxS : x ∉ S := fun hm => hx (mem_union_right _ hm)
    have hX' : M.IsBase (↑(insert x (G.erase a) ∪ S) : Set V) := by
      change M.IsBase (↑(insert x ((G ∪ S).erase a)) : Set V) at hX
      rwa [erase_union_split haS, ← insert_union] at hX
    have hxe : x ≠ e := by
      intro hxe
      subst x
      apply hC.not_indep
      apply hX'.indep.subset
      intro y hy
      by_cases h : y = e
      · subst y
        simp
      · exact mem_union_right _ (mem_erase.mpr ⟨h, hy⟩)
    have hxC : x ∉ C := fun hm => hxS (mem_erase.mpr ⟨hxe, hm⟩)
    refine ⟨x, hxG, hxa, (contract_base_iff hS ?_).2 hX'⟩
    rw [disjoint_left]
    intro y hy hyC
    rcases mem_insert.mp hy with rfl | hy
    · exact hxC hyC
    · exact disjoint_left.mp hGC (mem_of_mem_erase hy) hyC
  · intro hP
    refine ⟨hGbase, fun a ha => ?_⟩
    rcases mem_union.mp ha with haG | haS
    · obtain ⟨x, hx, hxa, hX⟩ := hP.2 a haG
      have hxC : x ∉ C := (hX.subset_ground (by simp)).2
      have haS : a ∉ S := fun hm => disjoint_left.mp hGC haG (mem_of_mem_erase hm)
      have hXC : Disjoint (insert x (G.erase a)) C := by
        rw [disjoint_left]
        intro y hy hyC
        exact (hX.subset_ground (show y ∈ (↑(insert x (G.erase a)) : Set V) from hy)).2 hyC
      refine ⟨x, fun hm => (mem_union.mp hm).elim hx
        (fun hs => hxC (mem_of_mem_erase hs)), hxa, ?_⟩
      rw [erase_union_split haS, ← insert_union]
      exact (contract_base_iff hS hXC).1 hX
    · have haC := mem_of_mem_erase haS
      have haNe := (mem_erase.mp haS).1
      have heLt : e < a :=
        lt_of_le_of_ne (he.2 a (hGbase.indep.isNonloop_of_mem
          (show a ∈ (↑(G ∪ S) : Set V) from mem_union_right _ haS))) (Ne.symm haNe)
      refine ⟨e, fun h => (mem_union.mp h).elim heG heS, heLt, ?_⟩
      have haG : a ∉ G := fun hm => disjoint_left.mp hGC hm haC
      have hswap : insert e ((G ∪ S).erase a) = G ∪ C.erase a := by
        ext y
        simp only [mem_insert, mem_erase, mem_union, S]
        by_cases hye : y = e
        · subst y
          simp [heC, Ne.symm haNe]
        · by_cases hya : y = a
          · subst y
            simp [haG, haNe]
          · simp [hye, hya]
      rw [hswap]
      exact (contract_base_iff (circuit_erase_basis hC haC) hGC).1 hG

/-- The fundamental circuit as a finite face in the same ordered carrier. -/
noncomputable def circuitAt [Fintype V] (M : Matroid V) (B : Finset V) (e : V) :
    Finset V :=
  (M.fundCircuit e (B : Set V)).toFinite.toFinset

private lemma circuit_decomposition [Fintype V] {M : Matroid V} {B : Finset V} {e : V}
    (hB : PassiveBase M B) (he : LeastNonloop M e) :
    let C := circuitAt M B e
    M.IsCircuit (C : Set V) ∧ e ∈ C ∧ B ∩ C = C.erase e ∧
      PassiveBase (M ／ (C : Set V)) (B \ C) ∧ (B \ C).card < B.card := by
  classical
  let C := circuitAt M B e
  change M.IsCircuit (C : Set V) ∧ e ∈ C ∧ B ∩ C = C.erase e ∧
    PassiveBase (M ／ (C : Set V)) (B \ C) ∧ (B \ C).card < B.card
  have hcoe : (C : Set V) = M.fundCircuit e (B : Set V) := Set.Finite.coe_toFinset _
  have heB : e ∉ B := fun h => not_passiveBase_of_mem_least he h hB
  have heC : e ∈ C := by
    change e ∈ (C : Set V)
    rw [hcoe]
    exact M.mem_fundCircuit _ _
  have hC : M.IsCircuit (C : Set V) := by
    rw [hcoe]
    exact hB.1.fundCircuit_isCircuit he.1.mem_ground heB
  have hS : B ∩ C = C.erase e := by
    ext a
    rw [mem_inter, mem_erase]
    refine ⟨fun ⟨ha, hc⟩ => ⟨fun h => heB (h ▸ ha), hc⟩, fun ⟨hne, hc⟩ => ⟨?_, hc⟩⟩
    change a ∈ (B : Set V)
    have haC : a ∈ M.fundCircuit e (B : Set V) := hcoe ▸ (show a ∈ (C : Set V) from hc)
    exact (Set.mem_insert_iff.mp (M.fundCircuit_subset_insert e (B : Set V) haC)).resolve_left hne
  have hdis : Disjoint (B \ C) C := disjoint_sdiff.symm
  have hU : B \ C ∪ C.erase e = B := by
    rw [← hS, sdiff_union_inter]
  have hD := (contract_base_iff (circuit_erase_basis hC heC) hdis).2
    (by simpa only [hU] using hB.1)
  have hP := (passive_lift_iff hC heC he hD).mp (hU.symm ▸ hB)
  refine ⟨hC, heC, hS, hP, ?_⟩
  have hnonempty : (C.erase e).Nonempty := by
    by_contra hn
    have hzero := not_nonempty_iff_eq_empty.mp hn
    have heq : C = {e} := by rw [← insert_erase heC, hzero]; rfl
    rw [heq, coe_singleton] at hC
    exact hC.not_indep he.1.indep
  have hcard := card_sdiff_add_card_inter B C
  rw [hS] at hcard
  have hpos := card_pos.mpr hnonempty
  omega

omit [LinearOrder V] in
private lemma contract_base_disjoint {M : Matroid V} {C G : Finset V}
    (hG : (M ／ (C : Set V)).IsBase (G : Set V)) : Disjoint G C := by
  rw [disjoint_left]
  intro x hx hxC
  exact (hG.subset_ground (show x ∈ (G : Set V) from hx)).2 hxC

private lemma boundaryOn_complement [Fintype V] {M : Matroid V} {C : Finset V}
    {w : Chain V} (hw : TopCycle (M ／ (C : Set V)) w) (D : Finset V) :
    boundaryOn (univ \ C) w D = 0 := by
  classical
  rw [← hw.cycle D]
  unfold boundaryOn
  apply sum_subset
  · intro x hx
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hx).2⟩
  · intro x hx hx'
    have hxC : x ∈ C := by simpa [(mem_sdiff.mp hx).2] using hx'
    rw [hw.vanishes _ (fun h => disjoint_left.mp (contract_base_disjoint h)
      (mem_insert_self _ _) hxC), mul_zero]

/-- The orientation unit making the joined cycle's B-coordinate equal to one. -/
def orientationSign (C : Finset V) (e : V) (B : Finset V) : ℤ :=
  shuffleSign (B ∩ C) (B \ C) * insertionSign (C.erase e) e

private lemma orientationSign_sq (C : Finset V) (e : V) (B : Finset V) :
    orientationSign C e B * orientationSign C e B = 1 := by
  unfold orientationSign shuffleSign insertionSign
  rw [← pow_add, sign_sq]

/-- The oriented circuit-boundary lift with normalization at B. -/
def circuitLift (C : Finset V) (e : V) (B : Finset V) (w : Chain V) : Chain V :=
  fun F => orientationSign C e B * signedJoin C (simplexBoundary C) w F

private lemma lift_normalized [Fintype V] {M : Matroid V} {C B : Finset V} {e : V}
    (hC : M.IsCircuit (C : Set V)) (heC : e ∈ C) (he : LeastNonloop M e)
    (hS : B ∩ C = C.erase e) {w : Chain V}
    (hw : Normalized (M ／ (C : Set V)) (B \ C) w) :
    Normalized M B (circuitLift C e B w) := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro F hF
    by_contra hn
    have hprod : simplexBoundary C (F ∩ C) * w (F \ C) ≠ 0 :=
      fun h => hn (by simp [circuitLift, signedJoin, h])
    have hA := left_ne_zero_of_mul hprod
    have hD := right_ne_zero_of_mul hprod
    obtain ⟨x, hx, heq⟩ := simplexBoundary_support.mp hA
    have hDbase : (M ／ (C : Set V)).IsBase (↑(F \ C) : Set V) := by
      by_contra hb
      exact hD (hw.vanishes _ hb)
    apply hF
    have hU : F \ C ∪ C.erase x = F := by rw [← heq, sdiff_union_inter]
    rw [← hU]
    exact (contract_base_iff (circuit_erase_basis hC hx) disjoint_sdiff.symm).1 hDbase
  · intro R
    have hb : boundaryOn univ (signedJoin C (simplexBoundary C) w) R = 0 := by
      rw [boundaryOn_signedJoin, boundaryOn_complement hw.toTopCycle,
        simplexBoundary, boundaryOn_squared]
      simp
    unfold boundaryOn circuitLift at *
    rw [← mul_zero (orientationSign C e B), ← hb, mul_sum]
    apply sum_congr rfl
    intro x _
    ring
  · intro F hF
    by_cases hFB : F = B
    · subst F
      have hB := (contract_base_iff (circuit_erase_basis hC heC)
        (disjoint_sdiff.symm : Disjoint (B \ C) C)).2
        (by simpa only [← hS, sdiff_union_inter] using hF.1)
      have hP := (passive_lift_iff hC heC he hB).mp
        (by simpa only [← hS, sdiff_union_inter] using hF)
      have hwB : w (B \ C) = 1 := by simpa using hw.coordinate _ hP
      rw [circuitLift, signedJoin, hwB, mul_one, hS, simplexBoundary_erase heC]
      change (shuffleSign (B ∩ C) (B \ C) * insertionSign (C.erase e) e) *
        (shuffleSign (C.erase e) (B \ C) * insertionSign (C.erase e) e) = _
      rw [hS]
      simpa [orientationSign, hS] using orientationSign_sq C e B
    · rw [ite_eq_right hFB]
      by_contra hne
      have hprod : simplexBoundary C (F ∩ C) * w (F \ C) ≠ 0 :=
        fun h => hne (by simp [circuitLift, signedJoin, h])
      obtain ⟨x, hx, hA⟩ := simplexBoundary_support.mp (left_ne_zero_of_mul hprod)
      have hxe : x = e := by
        by_contra h
        have heF : e ∈ F := (mem_inter.mp
          (hA.symm ▸ mem_erase.mpr ⟨Ne.symm h, heC⟩)).1
        exact not_passiveBase_of_mem_least he heF hF
      subst x
      have hU : F \ C ∪ C.erase e = F := by rw [← hA, sdiff_union_inter]
      have hDbase := (contract_base_iff (circuit_erase_basis hC heC)
        (disjoint_sdiff.symm : Disjoint (F \ C) C)).2 (hU.symm ▸ hF.1)
      have hDpass := (passive_lift_iff hC heC he hDbase).mp (hU.symm ▸ hF)
      have hDne : F \ C ≠ B \ C := by
        intro h
        apply hFB
        rw [← hU, h, ← hS, sdiff_union_inter]
      exact (right_ne_zero_of_mul hprod) (by simpa [hDne] using hw.coordinate _ hDpass)

private lemma rank_zero_normalized [Fintype V] {M : Matroid V}
    (hB : M.IsBase (∅ : Set V)) : Normalized M ∅ (simplex ∅) := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro F hF
    have hne : F ≠ ∅ := fun h => hF (h.symm ▸ (by simpa using hB :
      M.IsBase (↑(∅ : Finset V) : Set V)))
    simp [simplex, hne]
  · intro R
    apply sum_eq_zero
    intro x _
    simp [simplex]
  · intro F _
    rfl

/-- Every internally passive base has exactly one normalized top integral cycle. -/
private theorem existsUnique_normalized [Fintype V] (M : Matroid V) (B : Finset V)
    (hB : PassiveBase M B) : ∃! z, Normalized M B z := by
  classical
  suffices ∃ z, Normalized M B z by
    obtain ⟨z, hz⟩ := this
    exact ⟨z, hz, fun w hw => topCycle_ext hw.toTopCycle hz.toTopCycle
      (fun F h => (hw.coordinate F h).trans (hz.coordinate F h).symm)⟩
  induction B using (measure Finset.card).wf.induction generalizing M with
  | h B ih =>
    by_cases hzero : B = ∅
    · subst B
      exact ⟨simplex ∅, rank_zero_normalized (by simpa using hB.1)⟩
    let nonloops : Finset V := univ.filter M.IsNonloop
    have hn : nonloops.Nonempty := by
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hzero
      exact ⟨x, mem_filter.mpr ⟨mem_univ _, hB.1.indep.isNonloop_of_mem hx⟩⟩
    let e := nonloops.min' hn
    have he : LeastNonloop M e :=
      ⟨(mem_filter.mp (min'_mem nonloops hn)).2,
        fun x hx => min'_le nonloops x (mem_filter.mpr ⟨mem_univ _, hx⟩)⟩
    obtain ⟨hC, heC, hS, hD, hcard⟩ := circuit_decomposition hB he
    obtain ⟨w, hw⟩ := ih _ hcard _ hD
    exact ⟨_, lift_normalized hC heC he hS hw⟩

/-- The finite set of faces with nonzero coefficient. -/
noncomputable def cycleSupport [Fintype V] (z : Chain V) : Finset (Finset V) := by
  classical
  exact univ.filter fun F => z F ≠ 0

omit [LinearOrder V] in
private lemma mem_cycleSupport [Fintype V] {z : Chain V} {F : Finset V} :
    F ∈ cycleSupport z ↔ z F ≠ 0 := by
  classical
  simp [cycleSupport]

private lemma split_circuit_face {C D : Finset V} (hd : Disjoint D C) (x : V) :
    (D ∪ C.erase x) ∩ C = C.erase x ∧ (D ∪ C.erase x) \ C = D := by
  constructor <;> ext a <;>
    simp only [mem_sdiff, mem_inter, mem_union, mem_erase]
  all_goals
    have h (hm : a ∈ D) : a ∉ C := disjoint_left.mp hd hm
    tauto

/-- The support splits by the omitted circuit vertex. Each part is in bijection
with the support of the contracted cycle, with an explicit inverse on the two parts. -/
private theorem circuitLift_support [Fintype V] {M : Matroid V} {C B : Finset V} {e : V}
    {w : Chain V} (hw : TopCycle (M ／ (C : Set V)) w) :
    (∀ F, F ∈ cycleSupport (circuitLift C e B w) ↔
      ∃ x ∈ C, F ∩ C = C.erase x ∧ F \ C ∈ cycleSupport w) ∧
    (cycleSupport (circuitLift C e B w)).card = C.card * (cycleSupport w).card := by
  classical
  have hunit : orientationSign C e B ≠ 0 := by
    intro h
    simpa [h] using orientationSign_sq C e B
  have hmem (F : Finset V) : F ∈ cycleSupport (circuitLift C e B w) ↔
      ∃ x ∈ C, F ∩ C = C.erase x ∧ F \ C ∈ cycleSupport w := by
    rw [mem_cycleSupport]
    change orientationSign C e B * (shuffleSign (F ∩ C) (F \ C) *
      (simplexBoundary C (F ∩ C) * w (F \ C))) ≠ 0 ↔ _
    constructor
    · intro h
      have hp := right_ne_zero_of_mul (right_ne_zero_of_mul h)
      obtain ⟨x, hx, hA⟩ := simplexBoundary_support.mp (left_ne_zero_of_mul hp)
      exact ⟨x, hx, hA, mem_cycleSupport.mpr (right_ne_zero_of_mul hp)⟩
    · rintro ⟨x, hx, hA, hD⟩
      exact mul_ne_zero hunit (mul_ne_zero (shuffleSign_ne_zero _ _)
        (mul_ne_zero (simplexBoundary_support.mpr ⟨x, hx, hA⟩) (mem_cycleSupport.mp hD)))
  have hdis (D : Finset V) (hD : D ∈ cycleSupport w) : Disjoint D C := by
    apply contract_base_disjoint (M := M)
    by_contra h
    exact (mem_cycleSupport.mp hD) (hw.vanishes _ h)
  refine ⟨hmem, ?_⟩
  rw [← card_product]
  symm
  refine card_bij (fun p _ => p.2 ∪ C.erase p.1) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hx, hD⟩ := mem_product.mp hp
    have hs := split_circuit_face (hdis _ hD) p.1
    exact (hmem _).2 ⟨p.1, hx, hs.1, hs.2.symm ▸ hD⟩
  · intro p hp q hq heq
    obtain ⟨hx, hD⟩ := mem_product.mp hp
    obtain ⟨_, hE⟩ := mem_product.mp hq
    have hp' := split_circuit_face (hdis _ hD) p.1
    have hq' := split_circuit_face (hdis _ hE) q.1
    apply Prod.ext
    · have h := hp'.1.symm.trans ((congrArg (· ∩ C) heq).trans hq'.1)
      by_contra hne
      exact (notMem_erase p.1 C) (h.symm ▸ mem_erase.mpr ⟨hne, hx⟩)
    · exact hp'.2.symm.trans ((congrArg (· \ C) heq).trans hq'.2)
  · intro F hF
    obtain ⟨x, hx, hA, hD⟩ := (hmem F).1 hF
    exact ⟨(x, F \ C), mem_product.mpr ⟨hx, hD⟩, by rw [← hA, sdiff_union_inter]⟩

/-- The normalized top cycle exists uniquely. In positive rank the least nonloop
gives the oriented circuit product and the support recurrence. -/
theorem normalized_factorization [Fintype V] (M : Matroid V) (B : Finset V)
    (hB : PassiveBase M B) :
    (∃! z, Normalized M B z) ∧
    (∀ z, Normalized M B z → B = ∅ → z = simplex ∅) ∧
    ∀ e, LeastNonloop M e →
      let C := circuitAt M B e
      let D := B \ C
      PassiveBase (M ／ (C : Set V)) D ∧
      ∀ z w, Normalized M B z → Normalized (M ／ (C : Set V)) D w →
        z = circuitLift C e B w ∧
        (∀ F, F ∈ cycleSupport z ↔
          ∃ x ∈ C, F ∩ C = C.erase x ∧ F \ C ∈ cycleSupport w) ∧
        (cycleSupport z).card = C.card * (cycleSupport w).card := by
  classical
  refine ⟨existsUnique_normalized M B hB, ?_, ?_⟩
  · intro z hz heq
    subst B
    have hw := rank_zero_normalized (by simpa using hB.1)
    exact topCycle_ext hz.toTopCycle hw.toTopCycle
      (fun F hF => (hz.coordinate _ hF).trans (hw.coordinate _ hF).symm)
  · intro e he
    obtain ⟨hC, heC, hS, hD, _⟩ := circuit_decomposition hB he
    refine ⟨hD, fun z w hz hw => ?_⟩
    have hLift := lift_normalized hC heC he hS hw
    have heq := topCycle_ext hz.toTopCycle hLift.toTopCycle
      (fun F hF => (hz.coordinate _ hF).trans (hLift.coordinate _ hF).symm)
    exact ⟨heq, heq.symm ▸ circuitLift_support hw.toTopCycle⟩

end D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
