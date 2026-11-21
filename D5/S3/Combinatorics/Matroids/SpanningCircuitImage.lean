/- GID: D5/S3/Combinatorics/Matroids/SpanningCircuitImage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SpanningCircuitImage
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The exact integral restriction image of an arbitrary spanning circuit. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitRestrictionImage
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Ring

/-! The image of the signed readout on integral top cycles of a finite ordered matroid. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.SpanningCircuitImage

open CircuitRestrictionImage OrderedCycleFactorization
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

variable {V : Type*} [LinearOrder V] [Fintype V]

private def circuitCoordinate (K : Finset V) (z : Chain V) (a : V) : ℤ :=
  simplexBoundary K (K.erase a) * z (K.erase a)

omit [Fintype V] in
private lemma complement_star {E K : Finset V} {a : V} (hKE : K ⊆ E) :
    E \ insert a (E \ K) = K.erase a := by
  ext x
  simp only [mem_sdiff, mem_insert, mem_erase]
  by_cases hx : x ∈ K
  · simp [hx, hKE hx]
  · simp [hx]
    tauto

omit [Fintype V] in
private lemma dual_star {M : Matroid V} {E K : Finset V} {a : V}
    (hE : M.E = (E : Set V)) (hK : M.IsCircuit (K : Set V))
    (hspan : M.Spanning (K : Set V)) (ha : a ∈ K) :
    M✶.IsBase (↑(insert a (E \ K)) : Set V) := by
  have hKE : K ⊆ E := coe_subset.mp (hE ▸ hK.subset_ground)
  have hsub : insert a (E \ K) ⊆ E := insert_subset (hKE ha) sdiff_subset
  rw [Matroid.dual_isBase_iff (hE.symm ▸ coe_subset.mpr hsub), hE, ← coe_sdiff,
    complement_star hKE]
  exact (circuit_erase_basis hK ha).isBase_of_spanning hspan

omit [Fintype V] in
private lemma dual_nonloop {M : Matroid V} {E K : Finset V}
    (hE : M.E = (E : Set V)) (hK : M.IsCircuit (K : Set V))
    (hspan : M.Spanning (K : Set V)) {a : V} (ha : a ∈ E) :
    M✶.IsNonloop a := by
  by_cases haK : a ∈ K
  · exact (dual_star hE hK hspan haK).indep.isNonloop_of_mem (by simp)
  obtain ⟨p, hp⟩ := hK.nonempty
  exact (dual_star hE hK hspan (show p ∈ K from hp)).indep.isNonloop_of_mem
    (mem_insert_of_mem (mem_sdiff.mpr ⟨ha, haK⟩))

omit [Fintype V] in
private lemma boundary_pair {K U : Finset V} {a b : V} {z : Chain V}
    (hKU : K ⊆ U) (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (hzero : ∀ x ∈ U, x ∉ K → z (insert x (K \ {a, b})) = 0) :
    let R := K \ {a, b}
    boundaryOn U z R = insertionSign R a * z (K.erase b) +
      insertionSign R b * z (K.erase a) := by
  let R := K \ {a, b}
  have hsub : ({a, b} : Finset V) ⊆ U \ R := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [R, hKU ha]
    · simp [R, hKU hb]
  have hred : ∑ x ∈ ({a, b} : Finset V), insertionSign R x * z (insert x R) =
      boundaryOn U z R := by
    apply sum_subset hsub
    intro x hx hxab
    rw [hzero x (mem_sdiff.mp hx).1 (fun hxK =>
      (mem_sdiff.mp hx).2 (mem_sdiff.mpr ⟨hxK, hxab⟩)), mul_zero]
  have hleft : insert a R = K.erase b := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [ha, hab]
    · simp [R, hxa, and_comm]
  have hright : insert b R = K.erase a := by
    ext x
    by_cases hxb : x = b
    · subst x
      simp [hb, hab.symm]
    · simp [R, hxb, and_comm]
  change boundaryOn U z R = _
  rw [← hred, sum_insert (by simpa using hab), sum_singleton, hleft, hright]

private lemma circuitCoordinate_eq_of_closure {M : Matroid V} {E K : Finset V}
    (hE : M.E = (E : Set V)) (hK : M.IsCircuit (K : Set V))
    (hspan : M.Spanning (K : Set V)) {z : Chain V} (hz : TopCycle M z)
    {a b : V} (ha : a ∈ K) (hb : b ∈ K) (hcl : M✶.closure {a} = M✶.closure {b}) :
    circuitCoordinate K z a = circuitCoordinate K z b := by
  classical
  by_cases hab : a = b
  · rw [hab]
  let R := K \ {a, b}
  have hnonloop := (dual_star hE hK hspan ha).indep.isNonloop_of_mem (by simp : a ∈ _)
  have hdep := hnonloop.closure_eq_closure_iff_isCircuit_of_ne hab
  have hn := (hdep.mp hcl).not_indep
  have hvan (x : V) (_ : x ∈ (univ : Finset V)) (hx : x ∉ K) :
      z (insert x R) = 0 := by
    apply hz.vanishes
    intro hbase
    apply hn (hbase.compl_isBase_dual.indep.subset ?_)
    have hKE : K ⊆ E := coe_subset.mp (hE ▸ hK.subset_ground)
    have hax : a ≠ x := fun h => hx (h ▸ ha)
    have hbx : b ≠ x := fun h => hx (h ▸ hb)
    rw [hE]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h <;> subst y
    · exact ⟨hKE ha, by simp [R, hax]⟩
    · exact ⟨hKE hb, by simp [R, hbx]⟩
  have hchain := (boundary_pair (subset_univ K) ha hb hab hvan).symm.trans (hz.cycle R)
  let s := simplexBoundary K
  have hsign := (boundary_pair (z := s) (Subset.rfl) ha hb hab
    (fun x hx hxK => (hxK hx).elim)).symm.trans (boundaryOn_squared K (simplex K) R)
  have hopp : insertionSign R a * s (K.erase b) = -(insertionSign R b * s (K.erase a)) :=
    eq_neg_of_add_eq_zero_left hsign
  have hsa : s (K.erase a) * s (K.erase a) = 1 := by
    rw [show s (K.erase a) = insertionSign (K.erase a) a from simplexBoundary_erase ha]
    exact sign_sq _
  have hsb : s (K.erase b) * s (K.erase b) = 1 := by
    rw [show s (K.erase b) = insertionSign (K.erase b) b from simplexBoundary_erase hb]
    exact sign_sq _
  have hchain' : (insertionSign R a * s (K.erase b)) * (s (K.erase b) * z (K.erase b)) +
      (insertionSign R b * s (K.erase a)) * (s (K.erase a) * z (K.erase a)) = 0 := by
    calc
      _ = insertionSign R a * ((s (K.erase b) * s (K.erase b)) * z (K.erase b)) +
          insertionSign R b * ((s (K.erase a) * s (K.erase a)) * z (K.erase a)) := by ring
      _ = 0 := by rw [hsa, hsb, one_mul, one_mul]; exact hchain
  rw [hopp, neg_mul, ← sub_eq_neg_add, ← mul_sub] at hchain'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hchain').resolve_left
    (mul_ne_zero (insertionSign_ne_zero _ _) ((simplexBoundary_support).2 ⟨a, ha, rfl⟩)))

omit [Fintype V] in
private lemma boundaryOn_eq_of_support {U W : Finset V} {z : Chain V}
    (hUW : U ⊆ W) (hz : ∀ F, z F ≠ 0 → F ⊆ U) (R : Finset V) :
    boundaryOn U z R = boundaryOn W z R := by
  apply sum_subset (sdiff_subset_sdiff_left R hUW)
  intro a ha haU
  have hzero : z (insert a R) = 0 := by
    by_contra hn
    exact haU (mem_sdiff.mpr ⟨hz _ hn (mem_insert_self _ _), (mem_sdiff.mp ha).2⟩)
  rw [hzero, mul_zero]

omit [Fintype V] in
private lemma disjoint_erase_closure {N : Matroid V} {B P : Finset V} {p : V}
    (hB : N.IsBase (B : Set V)) (hp : p ∈ B) (hP : (P : Set V) = N.closure {p}) :
    Disjoint (B.erase p) P := by
  apply disjoint_left.mpr
  intro x hx hxP
  obtain ⟨hxp, hxB⟩ := mem_erase.mp hx
  apply hB.indep.notMem_closure_sdiff_of_mem (show x ∈ (B : Set V) from hxB)
  apply N.closure_subset_closure (Set.singleton_subset_iff.mpr
    (show p ∈ (B : Set V) \ {x} from ⟨hp, by simpa using hxp.symm⟩))
  exact hP ▸ (show x ∈ (P : Set V) from hxP)

/-- Successively contract the rank-one flats visited by the base, starting at the
chosen vertex. Joining their augmented boundaries gives a unit at the base complement. -/
private lemma exists_flag_cycle (E : Finset V) (N : Matroid V) (B : Finset V)
    (p : V) (hE : N.E = (E : Set V)) (hB : N.IsBase (B : Set V))
    (hloop : ∀ x ∈ E, N.IsNonloop x) (hp : B.Nonempty → p ∈ B) :
    ∃ w : Chain V, (∀ R, boundaryOn univ w R = 0) ∧
      (∀ F, w F ≠ 0 → F ⊆ E ∧ N.IsBase (↑(E \ F) : Set V)) ∧
      w (E \ B) * w (E \ B) = 1 ∧
      (p ∈ B → ∀ F : Finset V, N.closure {p} ⊆ (F : Set V) → w F = 0) := by
  classical
  induction E using Finset.strongInduction generalizing N B p with
  | H E ih =>
    by_cases hBn : B.Nonempty
    swap
    · rw [not_nonempty_iff_eq_empty.mp hBn] at hB ⊢
      have hEe : E = ∅ := by
        rw [← coe_eq_empty, ← hE]
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hcl : N.closure ∅ = N.E := by simpa only [coe_empty] using hB.closure_eq
        have hxcl : x ∈ N.closure ∅ := hcl.symm ▸ hx
        exact (hloop x (show x ∈ (E : Set V) from hE ▸ hx)).not_isLoop hxcl
      subst E
      refine ⟨simplex ∅, ?_, ?_, by simp [simplex], by simp⟩
      · intro R
        simp [boundaryOn, simplex]
      · intro F hF
        have hFe : F = ∅ := by simpa [simplex] using hF
        simpa only [hFe, sdiff_empty, empty_subset, true_and] using hB
    have hpB := hp hBn
    have hpN := hB.indep.isNonloop_of_mem (show p ∈ (B : Set V) from hpB)
    let P := (N.closure {p}).toFinite.toFinset
    have hP : (P : Set V) = N.closure {p} := Set.Finite.coe_toFinset _
    have hpP : p ∈ P := show p ∈ (P : Set V) from
      hP.symm ▸ N.mem_closure_self p hpN.mem_ground
    have hPE : P ⊆ E := coe_subset.mp (hE ▸ hP.symm ▸ N.closure_subset_ground {p})
    have hdis := disjoint_erase_closure hB hpB hP
    have hbasis (x : V) (hx : x ∈ P) : N.IsBasis (↑({x} : Finset V) : Set V) (P : Set V) := by
      have hxN := hloop x (hPE hx)
      have hcl := hxN.closure_eq_of_mem_closure (hP ▸ (show x ∈ (P : Set V) from hx))
      rw [coe_singleton, hP, ← hcl]
      exact hxN.indep.isBasis_closure
    let B' := B.erase p
    have hB' : (N ／ (P : Set V)).IsBase (B' : Set V) :=
      (contract_base_iff (hbasis p hpP) hdis).2 (by simpa [B', insert_erase hpB] using hB)
    have hE' : (N ／ (P : Set V)).E = (↑(E \ P) : Set V) := by
      rw [Matroid.contract_ground, hE, coe_sdiff]
    have hnonloop' (x : V) (hx : x ∈ E \ P) : (N ／ (P : Set V)).IsNonloop x := by
      apply Matroid.contract_isNonloop_iff.mpr
      rw [hE, hP, Matroid.closure_closure, ← hP, ← coe_sdiff]
      exact hx
    obtain ⟨q, hq⟩ : ∃ q : V, B'.Nonempty → q ∈ B' := by
      by_cases h : B'.Nonempty
      · obtain ⟨q, hq⟩ := h
        exact ⟨q, fun _ => hq⟩
      · exact ⟨p, fun h' => (h h').elim⟩
    obtain ⟨w, hw, hsupport, hunit, _⟩ :=
      ih (E \ P) (sdiff_ssubset hPE ⟨p, hpP⟩) (N ／ (P : Set V)) B' q hE' hB' hnonloop' hq
    refine ⟨signedJoin P (simplexBoundary P) w, ?_, ?_, ?_, ?_⟩
    · intro R
      have hs : boundaryOn (univ \ P) w (R \ P) = 0 :=
        (boundaryOn_eq_of_support (sdiff_subset_sdiff_left P (subset_univ E))
          (fun F hF => (hsupport F hF).1) _).symm.trans
          ((boundaryOn_eq_of_support (subset_univ (E \ P))
            (fun F hF => (hsupport F hF).1) _).trans (hw _))
      rw [boundaryOn_signedJoin, simplexBoundary, boundaryOn_squared, hs]
      simp
    · intro F hF
      have hterms := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hF).2
      obtain ⟨x, hx, hface⟩ := simplexBoundary_support.mp hterms.1
      obtain ⟨hsub, hbase⟩ := hsupport _ hterms.2
      have hFE : F ⊆ E := by
        intro y hy
        by_cases hyP : y ∈ P
        · exact hPE hyP
        · exact (mem_sdiff.mp (hsub (mem_sdiff.mpr ⟨hy, hyP⟩))).1
      refine ⟨hFE, ?_⟩
      have hrem : Disjoint ((E \ P) \ (F \ P)) P :=
        disjoint_sdiff.symm.mono_left sdiff_subset
      have hsplit : E \ F = ((E \ P) \ (F \ P)) ∪ {x} := by
        ext y
        by_cases hyP : y ∈ P
        · have hye : y ∈ F ↔ y ≠ x := by
            have h := Finset.ext_iff.mp hface y
            simpa [hyP] using h
          simp [hyP, hPE hyP, hye]
        · have hyx : y ≠ x := fun h => hyP (h ▸ hx)
          simp [hyP, hyx]
      rw [hsplit]
      exact (contract_base_iff (hbasis x hx) hrem).mp hbase
    · have hfirst : (E \ B) ∩ P = P.erase p := by
        ext x
        by_cases hxP : x ∈ P
        · have hxB : x ∈ B ↔ x = p := by
            refine ⟨fun hx => ?_, fun h => h ▸ hpB⟩
            by_contra h
            exact disjoint_left.mp hdis (mem_erase.mpr ⟨h, hx⟩) hxP
          simp [hxP, hPE hxP, hxB]
        · simp [hxP]
      have hrest : (E \ B) \ P = (E \ P) \ B' := by
        ext x
        have hxp : x ∉ P → x ≠ p := fun hn he => hn (he ▸ hpP)
        simp only [mem_sdiff, B', mem_erase]
        by_cases hxP : x ∈ P <;> simp [hxP, hxp]
      rw [signedJoin, hfirst, hrest, simplexBoundary_erase hpP]
      let F := P.erase p
      let G := (E \ P) \ B'
      calc
        _ = (shuffleSign F G * shuffleSign F G) *
            ((insertionSign F p * insertionSign F p) * (w G * w G)) := by ring
        _ = 1 := by rw [hunit, show shuffleSign F G * shuffleSign F G = 1 from sign_sq _,
            show insertionSign F p * insertionSign F p = 1 from sign_sq _]; norm_num
    · intro _ F hF
      have hi : F ∩ P = P := inter_eq_right.mpr (coe_subset.mp (hP.symm ▸ hF))
      simp [signedJoin, hi, simplexBoundary, boundaryOn]

/-- A single dual parallel class can be read out independently of all the others. -/
private lemma exists_class_cycle {M : Matroid V} {E K : Finset V}
    (hE : M.E = (E : Set V)) (hK : M.IsCircuit (K : Set V))
    (hspan : M.Spanning (K : Set V)) {p : V} (hp : p ∈ K) :
    ∃ z : Chain V, TopCycle M z ∧ ∀ a ∈ K,
      circuitCoordinate K z a = if M✶.closure {a} = M✶.closure {p} then 1 else 0 := by
  classical
  let B := insert p (E \ K)
  have hB := dual_star hE hK hspan hp
  have hpB : p ∈ B := mem_insert_self _ _
  have hEd : M✶.E = (E : Set V) := hE
  obtain ⟨w, hw, hsupport, hunit, hzero⟩ :=
    exists_flag_cycle E M✶ B p hEd hB (fun _ => dual_nonloop hE hK hspan) (fun _ => hpB)
  have hwTop : TopCycle M w := by
    refine ⟨?_, hw⟩
    intro F hF
    by_contra hn
    obtain ⟨hFE, hdual⟩ := hsupport F hn
    apply hF
    have hsub : (↑(E \ F) : Set V) ⊆ M.E := hE.symm ▸ coe_subset.mpr sdiff_subset
    rw [Matroid.dual_isBase_iff hsub, hE, ← coe_sdiff, Finset.sdiff_sdiff_eq_self hFE] at hdual
    exact hdual
  have hKE : K ⊆ E := coe_subset.mp (hE ▸ hK.subset_ground)
  have hclosure : M✶.closure {p} ⊆ (K : Set V) := by
    let P := (M✶.closure {p}).toFinite.toFinset
    have hP : (P : Set V) = M✶.closure {p} := Set.Finite.coe_toFinset _
    have hdis := disjoint_erase_closure hB hpB hP
    intro a ha
    by_contra haK
    have haE : a ∈ E := show a ∈ (E : Set V) from
      hE ▸ M✶.closure_subset_ground {p} ha
    have hap : a ≠ p := fun h => haK (h ▸ hp)
    exact disjoint_left.mp hdis
      (mem_erase.mpr ⟨hap, mem_insert_of_mem (mem_sdiff.mpr ⟨haE, haK⟩)⟩)
      (show a ∈ (P : Set V) from hP.symm ▸ ha)
  let u := circuitCoordinate K w p
  have hsq : u * u = 1 := by
    have hface : E \ B = K.erase p := complement_star hKE
    rw [hface] at hunit
    dsimp only [u, circuitCoordinate]
    rw [simplexBoundary_erase hp]
    calc
      _ = (insertionSign (K.erase p) p * insertionSign (K.erase p) p) *
          (w (K.erase p) * w (K.erase p)) := by ring
      _ = 1 := by rw [show insertionSign (K.erase p) p * insertionSign (K.erase p) p = 1
          from sign_sq _, hunit, one_mul]
  let z : Chain V := fun F => u * w F
  have hz : TopCycle M z := by
    refine ⟨fun F hF => by simp [z, hwTop.vanishes F hF], fun R => ?_⟩
    simp only [z, boundaryOn, mul_left_comm (insertionSign R _), ← mul_sum]
    change u * boundaryOn univ w R = 0
    rw [hw R, mul_zero]
  refine ⟨z, hz, fun a ha => ?_⟩
  by_cases hcl : M✶.closure {a} = M✶.closure {p}
  · rw [ite_eq_left hcl, circuitCoordinate_eq_of_closure hE hK hspan hz ha hp hcl]
    simpa only [z, u, circuitCoordinate, mul_left_comm] using hsq
  · rw [ite_eq_right hcl]
    have han := (dual_star hE hK hspan ha).indep.isNonloop_of_mem (by simp : a ∈ _)
    have haP : a ∉ M✶.closure {p} := fun h => hcl (han.closure_eq_of_mem_closure h)
    have hsub : M✶.closure {p} ⊆ (↑(K.erase a) : Set V) :=
      fun b hb => mem_erase.mpr ⟨fun h => haP (h ▸ hb), hclosure hb⟩
    simp [circuitCoordinate, z, hzero hpB _ hsub]

omit [Fintype V] [LinearOrder V] in
private lemma gcd_int_cast {ι : Type*} (S : Finset ι) (w : ι → ℕ) :
    ((S.gcd w : ℕ) : ℤ) = S.gcd (fun c => (w c : ℤ)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [gcd_insert, gcd_insert, ← ih, ← Int.coe_gcd, Int.gcd_eq_natAbs,
      Int.natAbs_natCast, Int.natAbs_natCast]
    rfl

/-- For any spanning circuit, the attainable signed restrictions of integral top
cycles are exactly the multiples of the gcd of its dual parallel-class sizes. -/
theorem exists_topCycle_signedRestriction_iff (M : Matroid V) (K : Finset V)
    (hK : M.IsCircuit (K : Set V)) (hspan : M.Spanning (K : Set V)) (n : ℤ) :
    (∃ z : Chain V, TopCycle M z ∧ signedRestriction K z = n) ↔
      (dualClassGcd M K : ℤ) ∣ n := by
  classical
  let E := M.E.toFinite.toFinset
  have hE : M.E = (E : Set V) := (Set.Finite.coe_toFinset _).symm
  let cl (a : V) := M✶.closure {a}
  let classes := K.image cl
  let size (P : Set V) := (K.filter fun a => cl a = P).card
  have hgroup (q : Set V → ℤ) :
      (∑ a ∈ K, q (cl a)) = ∑ P ∈ classes, (size P : ℤ) * q P := by
    simpa only [size, sum_const, nsmul_eq_mul] using
      (sum_fiberwise_of_maps_to' (fun _ h => mem_image_of_mem cl h) q).symm
  change (∃ z : Chain V, TopCycle M z ∧ signedRestriction K z = n) ↔
    ((classes.gcd size : ℕ) : ℤ) ∣ n
  constructor
  · rintro ⟨z, hz, rfl⟩
    let q (P : Set V) : ℤ :=
      if h : ∃ a ∈ K, cl a = P then circuitCoordinate K z h.choose else 0
    have hq (a : V) (ha : a ∈ K) : circuitCoordinate K z a = q (cl a) := by
      have h : ∃ b ∈ K, cl b = cl a := ⟨a, ha, rfl⟩
      simp only [q, dite_eq_left h]
      exact circuitCoordinate_eq_of_closure hE hK hspan hz ha h.choose_spec.1 h.choose_spec.2.symm
    have hread : signedRestriction K z = ∑ a ∈ K, q (cl a) := sum_congr rfl hq
    rw [hread, hgroup]
    apply Finset.dvd_sum
    intro P hP
    exact dvd_mul_of_dvd_left (by exact_mod_cast Finset.gcd_dvd (f := size) hP) _
  · rintro ⟨m, hm⟩
    rw [gcd_int_cast] at hm
    obtain ⟨q, hq⟩ := Finset.gcd_eq_sum_mul classes (fun P => (size P : ℤ))
    have hgens (P : Set V) : ∃ w : Chain V, TopCycle M w ∧ ∀ a ∈ K,
        circuitCoordinate K w a = if cl a = P then 1 else 0 := by
      by_cases hP : P ∈ classes
      · obtain ⟨p, hp, rfl⟩ := mem_image.mp hP
        exact exists_class_cycle hE hK hspan hp
      · refine ⟨fun _ => 0, ⟨by simp, by simp [boundaryOn]⟩, fun a ha => ?_⟩
        have hne : cl a ≠ P := fun h => hP (h ▸ mem_image_of_mem cl ha)
        simp [circuitCoordinate, hne]
    choose w hw hcoord using hgens
    let z : Chain V := fun F => ∑ P ∈ classes, (q P * m) * w P F
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · intro F hF
      simp [z, fun P => (hw P).vanishes F hF]
    · intro R
      unfold boundaryOn z
      simp only [mul_sum, mul_left_comm (insertionSign R _)]
      rw [sum_comm]
      simp only [← mul_sum]
      change (∑ P ∈ classes, (q P * m) * boundaryOn univ (w P) R) = 0
      simp only [(hw _).cycle, mul_zero, sum_const_zero]
    · have hread (a : V) (ha : a ∈ K) : circuitCoordinate K z a = q (cl a) * m := by
        unfold circuitCoordinate z
        rw [mul_sum, sum_eq_single_of_mem (cl a) (mem_image_of_mem cl ha)]
        · rw [mul_left_comm, ← circuitCoordinate, hcoord _ a ha, ite_eq_left rfl, mul_one]
        · intro P _ hP
          rw [mul_left_comm, ← circuitCoordinate, hcoord _ a ha, ite_eq_right (Ne.symm hP), mul_zero]
      calc
        _ = ∑ a ∈ K, q (cl a) * m := sum_congr rfl hread
        _ = n := by rw [← sum_mul, hgroup, hm, hq]

end D5.S3.Combinatorics.Matroids.SpanningCircuitImage
