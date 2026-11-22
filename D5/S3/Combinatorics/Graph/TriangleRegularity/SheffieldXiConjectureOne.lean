/- GID: D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.claim; result=D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.result; claim=D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.claim
   digest: The icosahedral pair (5,5) has no abelian Cayley realization. -/

import D5.S3.Combinatorics.Graph.Products.CayleyIndependence
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.Abel

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.TriangleRegularity.SheffieldXiConjectureOne

variable {A : Type*} [AddCommGroup A]

private theorem zeroNeighborSet (S : Set A) (hzero : (0 : A) ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S) :
    (SimpleGraph.addCayley S).neighborSet 0 = S := by
  ext x
  change (SimpleGraph.addCayley S).Adj 0 x ↔ x ∈ S
  simpa only [sub_zero] using CayleySquare.cayley_adj_iff S hzero hneg 0 x

private abbrev Triples (S : Set A) :=
  {t : S × S × S // (t.1 : A) + (t.2.1 : A) + (t.2.2 : A) = 0}

private def negIn {S : Set A} (hneg : ∀ x ∈ S, -x ∈ S) (x : S) : S :=
  ⟨-x.val, hneg _ x.property⟩

private def dartEquivTriples (S : Set A) (hzero : (0 : A) ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S) :
    ((SimpleGraph.addCayley S).induce ((SimpleGraph.addCayley S).neighborSet 0)).Dart ≃
      Triples S := by
  have hN := zeroNeighborSet S hzero hneg
  let toS (x : (SimpleGraph.addCayley S).neighborSet 0) : S :=
    ⟨x.val, (congrArg (fun U : Set A => x.val ∈ U) hN).mp x.property⟩
  let toN (x : S) : (SimpleGraph.addCayley S).neighborSet 0 :=
    ⟨x.val, (congrArg (fun U : Set A => x.val ∈ U) hN).mpr x.property⟩
  have reverseDiff (t : Triples S) : -t.val.2.2.val - t.val.1.val = t.val.2.1.val := by
    have ht : t.val.1.val + t.val.2.1.val = -t.val.2.2.val :=
      add_eq_zero_iff_eq_neg.mp t.property
    rw [← ht]
    abel
  refine
    { toFun := fun d => ?_
      invFun := fun t => ?_
      left_inv := fun d => ?_
      right_inv := fun t => ?_ }
  · have hadj := SimpleGraph.induce_adj.mp d.adj
    have hdiff := (CayleySquare.cayley_adj_iff S hzero hneg d.fst.val d.snd.val).mp hadj
    refine ⟨(toS d.fst, ⟨d.snd.val - d.fst.val, hdiff⟩, negIn hneg (toS d.snd)), ?_⟩
    change d.fst.val + (d.snd.val - d.fst.val) + -d.snd.val = 0
    abel
  · refine ⟨(toN t.val.1, toN (negIn hneg t.val.2.2)), SimpleGraph.induce_adj.mpr ?_⟩
    apply (CayleySquare.cayley_adj_iff S hzero hneg _ _).mpr
    change -t.val.2.2.val - t.val.1.val ∈ S
    rw [reverseDiff]
    exact t.val.2.1.property
  · apply SimpleGraph.Dart.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact neg_neg _
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        exact reverseDiff t
      · apply Subtype.ext
        exact neg_neg _

private theorem cardTriples (S : Set A) [Finite S] (hzero : (0 : A) ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S) :
    Nat.card (Triples S) =
      2 * Nat.card
        ((SimpleGraph.addCayley S).induce ((SimpleGraph.addCayley S).neighborSet 0)).edgeSet := by
  classical
  let G := SimpleGraph.addCayley S
  let N := G.neighborSet 0
  let H := G.induce N
  have hN : N = S := zeroNeighborSet S hzero hneg
  let : Finite N := hN.symm ▸ (inferInstance : Finite S)
  let : Fintype N := Fintype.ofFinite N
  let : Fintype S := Fintype.ofFinite S
  let : DecidableRel H.Adj := Classical.decRel H.Adj
  let : Fintype H.Dart := SimpleGraph.Dart.fintype (G := H)
  let : Fintype H.edgeSet := inferInstance
  let : Fintype (Triples S) := inferInstanceAs (Fintype
    {t : S × S × S // (t.1 : A) + (t.2.1 : A) + (t.2.2 : A) = 0})
  change Nat.card (Triples S) = 2 * Nat.card H.edgeSet
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, H.card_edgeSet,
    ← H.dart_card_eq_twice_card_edges]
  exact Fintype.card_congr (dartEquivTriples S hzero hneg).symm

private abbrev Three (S : Set A) := {x : S // 3 • x.val = 0}

private def negThree {S : Set A} (hneg : ∀ x ∈ S, -x ∈ S)
    (x : Three S) : Three S :=
  ⟨negIn hneg x.val, by
    change 3 • (-x.val.val) = 0
    rw [smul_neg, x.property, neg_zero]⟩

private theorem negThreeNe {S : Set A} (hzero : (0 : A) ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S) (x : Three S) : negThree hneg x ≠ x := by
  intro h
  have hn : -x.val.val = x.val.val :=
    congrArg (fun y : Three S => y.val.val) h
  have htwo : x.val.val + x.val.val = 0 := by
    rw [← neg_eq_iff_add_eq_zero]
    exact hn
  have hthree : x.val.val + x.val.val + x.val.val = 0 := by
    simpa only [three_nsmul, add_assoc] using x.property
  rw [htwo, zero_add] at hthree
  exact hzero (hthree ▸ x.val.property)

private def rotate {S : Set A} (t : Triples S) : Triples S :=
  ⟨(t.val.2.1, t.val.2.2, t.val.1), by
    change t.val.2.1.val + t.val.2.2.val + t.val.1.val = 0
    simpa only [add_assoc, add_comm, add_left_comm] using t.property⟩

private def diagonal {S : Set A} (x : Three S) : Triples S :=
  ⟨(x.val, x.val, x.val), by
    change x.val.val + x.val.val + x.val.val = 0
    simpa only [three_nsmul, add_assoc] using x.property⟩

private theorem rotationMod (S : Set A) [Finite S] :
    Nat.ModEq 3 (Nat.card (Triples S)) (Nat.card (Three S)) := by
  classical
  let : Fintype S := Fintype.ofFinite S
  let f : Function.End (Triples S) := rotate
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : f ^ (3 ^ 1) = 1 := by
    funext t
    apply Subtype.ext
    rfl
  have sameCoordinates (t : f.fixedPoints) :
      t.val.val.2.1 = t.val.val.1 ∧ t.val.val.2.2 = t.val.val.2.1 :=
    ⟨congrArg (fun u : Triples S => u.val.1) t.property,
      congrArg (fun u : Triples S => u.val.2.1) t.property⟩
  let equiv : f.fixedPoints ≃ Three S :=
    { toFun := fun t => by
        obtain ⟨hx, hy⟩ := sameCoordinates t
        refine ⟨t.val.val.1, ?_⟩
        have hsum := t.val.property
        rw [hy, hx] at hsum
        simpa only [three_nsmul, add_assoc] using hsum
      invFun := fun x => ⟨diagonal x, Subtype.ext rfl⟩
      left_inv := fun t => by
        apply Subtype.ext
        apply Subtype.ext
        obtain ⟨hx, hy⟩ := sameCoordinates t
        change (t.val.val.1, t.val.val.1, t.val.val.1) = t.val.val
        exact Prod.ext rfl (Prod.ext hx.symm (hy.trans hx).symm)
      right_inv := fun _ => rfl }
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hpow
  rw [Fintype.card_congr equiv] at hmod
  simpa only [Fintype.card_eq_nat_card] using hmod

private theorem negationMod (S : Set A) [Finite S] (hzero : (0 : A) ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S) : Nat.ModEq 2 (Nat.card (Three S)) 0 := by
  classical
  let : Fintype S := Fintype.ofFinite S
  let f : Function.End (Three S) := negThree hneg
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : f ^ (2 ^ 1) = 1 := by
    funext x
    apply Subtype.ext
    apply Subtype.ext
    exact neg_neg _
  let : IsEmpty f.fixedPoints := ⟨fun x => negThreeNe hzero hneg x.val x.property⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hpow
  simpa only [Fintype.card_of_isEmpty, Fintype.card_eq_nat_card] using hmod

private theorem tripleUsesThree {S : Set A} (hzero : (0 : A) ∉ S)
    (e : S) (he : ¬ 3 • e.val = 0) (htwo : e.val + e.val = 0)
    (onlyE : ∀ x : S, ¬ 3 • x.val = 0 → x = e)
    (a b c : S) (hsum : a.val + b.val + c.val = 0) : 3 • a.val = 0 := by
  by_contra ha
  have hae := onlyE a ha
  subst a
  by_cases hb : 3 • b.val = 0
  · by_cases hc : 3 • c.val = 0
    · apply he
      have scaled := congrArg (fun x : A => (3 : ℕ) • x) hsum
      change 3 • (e.val + b.val + c.val) = 3 • (0 : A) at scaled
      rwa [nsmul_add, nsmul_add, hb, hc, add_zero, add_zero, nsmul_zero] at scaled
    · have hce := onlyE c hc
      subst c
      have h : b.val = 0 := by
        have h' : e.val + e.val + b.val = 0 := by
          simpa only [add_assoc, add_comm, add_left_comm] using hsum
        rwa [htwo, zero_add] at h'
      exact hzero (h ▸ b.property)
  · have hbe := onlyE b hb
    subst b
    rw [htwo, zero_add] at hsum
    exact hzero (hsum ▸ c.property)

private theorem tripleOfThreeDiagonal {S : Set A} [Finite S]
    (hzero : (0 : A) ∉ S) (hneg : ∀ x ∈ S, -x ∈ S)
    (hcard : Nat.card (Three S) = 4)
    (a b c : Three S) (hsum : a.val.val + b.val.val + c.val.val = 0) :
    a = b ∧ a = c := by
  classical
  have same (x y : Three S) (h : x.val.val + x.val.val + y.val.val = 0) : x = y := by
    have hx : x.val.val + x.val.val + x.val.val = 0 := by
      simpa only [three_nsmul, add_assoc] using x.property
    exact Subtype.ext (Subtype.ext (add_left_cancel (hx.trans h.symm)))
  by_cases hab : a = b
  · subst b
    exact ⟨rfl, same a c hsum⟩
  by_cases hac : a = c
  · subst c
    exact ⟨same a b (by simpa only [add_assoc, add_comm, add_left_comm] using hsum), rfl⟩
  by_cases hbc : b = c
  · subst c
    have hba := same b a (by simpa only [add_assoc, add_comm, add_left_comm] using hsum)
    exact ⟨hba.symm, hba.symm⟩
  have noOpposite (x y z : Three S)
      (h : x.val.val + y.val.val + z.val.val = 0) : negThree hneg x ≠ y := by
    intro hxy
    have hxy' : -x.val.val = y.val.val := congrArg (fun x : Three S => x.val.val) hxy
    rw [← hxy', add_neg_cancel, zero_add] at h
    exact hzero (h ▸ z.val.property)
  have hna_b := noOpposite a b c hsum
  have hna_c : negThree hneg a ≠ c :=
    noOpposite a c b (by simpa only [add_assoc, add_comm, add_left_comm] using hsum)
  have hnb_a : negThree hneg b ≠ a :=
    noOpposite b a c (by simpa only [add_assoc, add_comm, add_left_comm] using hsum)
  have hnb_c : negThree hneg b ≠ c :=
    noOpposite b c a (by simpa only [add_assoc, add_comm, add_left_comm] using hsum)
  have hnab : negThree hneg a ≠ negThree hneg b := by
    intro h
    apply hab
    apply Subtype.ext
    apply Subtype.ext
    exact neg_injective (congrArg (fun x : Three S => x.val.val) h)
  let : Fintype S := Fintype.ofFinite S
  let five : Finset (Three S) := {a, b, c, negThree hneg a, negThree hneg b}
  have hfive : five.card = 5 := by
    simp [five, Finset.card_insert_of_notMem, hab, hac, hbc, hnab, hna_b.symm, hna_c.symm,
      hnb_a.symm, hnb_c.symm, (negThreeNe hzero hneg a).symm, (negThreeNe hzero hneg b).symm]
  have hle := Finset.card_le_univ five
  rw [hfive, Fintype.card_eq_nat_card, hcard] at hle
  omega

private theorem noCayleyFive (S : Set A) [Finite S] (hzero : (0 : A) ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S)
    (hsize : Nat.card ((SimpleGraph.addCayley S).neighborSet 0) = 5)
    (hedges :
      Nat.card ((SimpleGraph.addCayley S).induce ((SimpleGraph.addCayley S).neighborSet 0)).edgeSet
        = 5) : False := by
  classical
  rw [zeroNeighborSet S hzero hneg] at hsize
  have htrip : Nat.card (Triples S) = 10 := by rw [cardTriples S hzero hneg, hedges]
  let : Fintype S := Fintype.ofFinite S
  let : Fintype (Three S) := inferInstanceAs (Fintype {x : S // 3 • x.val = 0})
  have hle : Nat.card (Three S) ≤ Nat.card S := by
    simpa only [Fintype.card_eq_nat_card] using Fintype.card_subtype_le (fun x : S => 3 • x.val = 0)
  have hmod3 := rotationMod S
  have hmod2 := negationMod S hzero hneg
  rw [htrip] at hmod3
  rw [hsize] at hle
  have hfour : Nat.card (Three S) = 4 := by
    change 10 % 3 = Nat.card (Three S) % 3 at hmod3
    change Nat.card (Three S) % 2 = 0 % 2 at hmod2
    omega
  let Other := {x : S // ¬ 3 • x.val = 0}
  let : Fintype Other := inferInstanceAs (Fintype {x : S // ¬ 3 • x.val = 0})
  have hone : Fintype.card Other = 1 := by
    rw [show Fintype.card Other = Fintype.card S - Fintype.card (Three S) from
      Fintype.card_subtype_compl (fun x : S => 3 • x.val = 0)]
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hsize, hfour]
  obtain ⟨e, he⟩ := Fintype.card_eq_one_iff.mp hone
  have onlyE (x : S) (hx : ¬ 3 • x.val = 0) : x = e.val :=
    congrArg Subtype.val (he ⟨x, hx⟩)
  have hne : ¬ 3 • (negIn hneg e.val).val = 0 := by
    change ¬ 3 • (-e.val.val) = 0
    rw [smul_neg, neg_eq_zero]
    exact e.property
  have heNeg : -e.val.val = e.val.val :=
    congrArg Subtype.val (onlyE _ hne)
  have heTwo : e.val.val + e.val.val = 0 := by
    rw [← neg_eq_iff_add_eq_zero]
    exact heNeg
  have hm (a b c : S) (h : a.val + b.val + c.val = 0) : 3 • a.val = 0 :=
    tripleUsesThree hzero e.val e.property heTwo onlyE a b c h
  have everyDiagonal (t : Triples S) :
      t.val.1 = t.val.2.1 ∧ t.val.1 = t.val.2.2 := by
    have hsum := t.property
    let a : Three S := ⟨t.val.1, hm _ _ _ hsum⟩
    let b : Three S := ⟨t.val.2.1, hm t.val.2.1 t.val.1 t.val.2.2
      (by simpa only [add_assoc, add_comm, add_left_comm] using hsum)⟩
    let c : Three S := ⟨t.val.2.2, hm t.val.2.2 t.val.1 t.val.2.1
      (by simpa only [add_assoc, add_comm, add_left_comm] using hsum)⟩
    obtain ⟨hab, hac⟩ := tripleOfThreeDiagonal hzero hneg hfour a b c hsum
    exact ⟨congrArg Subtype.val hab, congrArg Subtype.val hac⟩
  let equiv : Triples S ≃ Three S :=
    { toFun := fun t => ⟨t.val.1, hm _ _ _ t.property⟩
      invFun := diagonal
      left_inv := fun t => by
        obtain ⟨hab, hac⟩ := everyDiagonal t
        apply Subtype.ext
        exact Prod.ext rfl (Prod.ext hab hac)
      right_inv := fun _ => rfl }
  have hcards := Nat.card_congr equiv
  omega

/-- Every open neighborhood has r vertices and induces c unordered edges. -/
def triangleRegular {V : Type} (G : SimpleGraph V) (r c : ℕ) : Prop :=
  ∀ v : V, Nat.card (G.neighborSet v) = r ∧
    Nat.card (G.induce (G.neighborSet v)).edgeSet = c

/-- Sheffield–Xi Conjecture 1. -/
def claim : Prop :=
  ∀ r c : ℕ,
    (∃ (V : Type) (_ : Finite V) (_ : Nonempty V) (G : SimpleGraph V),
      triangleRegular G r c) →
    ∃ (B : Type) (_ : Finite B) (instB : AddCommGroup B),
      letI : AddCommGroup B := instB
      ∃ S : Set B, 0 ∉ S ∧ (∀ x ∈ S, -x ∈ S) ∧
        triangleRegular (SimpleGraph.addCayley S) r c

/-- Two poles and two cyclic rings of five vertices. False is the upper ring. -/
private abbrev IcoVertex := Bool ⊕ (Bool × Fin 5)

private def icoRel : IcoVertex → IcoVertex → Prop
  | .inl p, .inr v => p = v.1
  | .inr v, .inr w =>
      (v.1 = w.1 ∧ w.2 = v.2 + 1) ∨
      (v.1 = false ∧ w.1 = true ∧ (w.2 = v.2 ∨ w.2 = v.2 - 1))
  | _, _ => False

private instance icoRelDecidable : DecidableRel icoRel := by
  intro v w
  cases v <;> cases w <;> unfold icoRel <;> infer_instance

private abbrev icosahedron : SimpleGraph IcoVertex := SimpleGraph.fromRel icoRel

private theorem icosahedronWitness : triangleRegular icosahedron 5 5 := by
  have localCounts : ∀ v : IcoVertex,
      Fintype.card (icosahedron.neighborSet v) = 5 ∧
        Fintype.card (icosahedron.induce (icosahedron.neighborSet v)).Dart = 10 := by
    decide
  intro v
  let H := icosahedron.induce (icosahedron.neighborSet v)
  obtain ⟨hn, hd⟩ := localCounts v
  refine ⟨?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]
    exact hn
  · have h := H.dart_card_eq_twice_card_edges
    change Fintype.card H.Dart = 10 at hd
    rw [hd, ← H.card_edgeSet, Fintype.card_eq_nat_card] at h
    change Nat.card H.edgeSet = 5
    omega

theorem result : ¬ claim := by
  intro conjecture
  obtain ⟨B, hB, instB, S, hzero, hneg, hlocal⟩ := conjecture 5 5
    ⟨IcoVertex, inferInstance, inferInstance, icosahedron, icosahedronWitness⟩
  let : AddCommGroup B := instB
  let : Finite B := hB
  exact noCayleyFive S hzero hneg (hlocal 0).1 (hlocal 0).2

end D5.S3.Combinatorics.Graph.TriangleRegularity.SheffieldXiConjectureOne
