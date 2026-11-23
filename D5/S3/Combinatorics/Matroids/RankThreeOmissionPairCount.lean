/- GID: D5/S3/Combinatorics/Matroids/RankThreeOmissionPairCount
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeOmissionPairCount
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Pairs from distinct ternary potential fibers give a lower bound on the number of omitted triples. -/

import D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentialFibers

namespace D5.S3.Combinatorics.Matroids.RankThreeOmissionPairCount

open Finset
open RankThreeOmissionPotentialFibers (potentialSpace point_potential_evaluations)
open RankThreeOmissionPotentials (IsOmissionPotential covers)

private theorem mixed_pair_card
    {I V : Type*} [Fintype I] (value : I → V) (s : ℕ)
    (fibers : ∀ x, Nat.card {i : I // value i = x} = s) :
    Nat.card {p : I × I // value p.1 ≠ value p.2} =
      Fintype.card I * (Fintype.card I - s) := by
  classical
  let e : (Σ i : I, {j : I // value j ≠ value i}) ≃
      {p : I × I // value p.1 ≠ value p.2} :=
    { toFun := fun p => ⟨(p.1, p.2.val), Ne.symm p.2.prop⟩
      invFun := fun p => ⟨p.val.1, ⟨p.val.2, Ne.symm p.prop⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have row (i : I) : Nat.card {j : I // value j ≠ value i} = Fintype.card I - s := by
    have same : Fintype.card {j : I // value j = value i} = s := by
      simpa only [Nat.card_eq_fintype_card] using fibers (value i)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun j : I => value j = value i), same]
  rw [← Nat.card_congr e, Nat.card_sigma]
  simp_rw [row]
  rw [sum_const, card_univ]
  exact nsmul_eq_mul _ _

private theorem mixed_pair_card_le_six_mul_triple_card
    {I T V : Type*} [Fintype I] [Fintype T]
    (points : T → Fin 3 → I) (value : I → V)
    (covered : ∀ i j, value i ≠ value j →
      ∃ t a b, points t a = i ∧ points t b = j) :
    Nat.card {p : I × I // value p.1 ≠ value p.2} ≤ 6 * Fintype.card T := by
  classical
  let index (p : {p : I × I // value p.1 ≠ value p.2}) :=
    covered p.val.1 p.val.2 p.prop
  let t p := (index p).choose
  let a p := (index p).choose_spec.choose
  let b p := (index p).choose_spec.choose_spec.choose
  have first p : points (t p) (a p) = p.val.1 := (index p).choose_spec.choose_spec.choose_spec.1
  have second p : points (t p) (b p) = p.val.2 := (index p).choose_spec.choose_spec.choose_spec.2
  have indices_ne p : a p ≠ b p := by
    intro equal
    exact p.prop (congrArg value ((first p).symm.trans (equal ▸ second p)))
  let assign (p : {p : I × I // value p.1 ≠ value p.2}) :
      T × {e : Fin 3 × Fin 3 // e.1 ≠ e.2} := (t p, ⟨(a p, b p), indices_ne p⟩)
  have injective : Function.Injective assign := by
    intro p r equal
    have edges := congrArg (fun w : T × {e : Fin 3 × Fin 3 // e.1 ≠ e.2} =>
      (points w.1 w.2.val.1, points w.1 w.2.val.2)) equal
    apply Subtype.ext
    change (points (t p) (a p), points (t p) (b p)) =
      (points (t r) (a r), points (t r) (b r)) at edges
    simpa only [first, second] using edges
  calc
    _ ≤ Nat.card (T × {e : Fin 3 × Fin 3 // e.1 ≠ e.2}) :=
      Nat.card_le_card_of_injective assign injective
    _ = _ := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := T)]
      have six : Nat.card {e : Fin 3 × Fin 3 // e.1 ≠ e.2} = 6 := by
        rw [Nat.card_eq_fintype_card]
        decide
      rw [six, Nat.mul_comm]

/-- Every mixed pair of point-potential fibers requires a listed triple.
There are six ordered pairs of positions available in each listed triple. -/
theorem potential_fiber_pair_count_le
    {I T : Type*} [Fintype I] [Fintype T]
    (points : T → Fin 3 → I) (anchor : I)
    (hinj : ∀ t, Function.Injective (points t))
    (hdis : ∀ t s i j, i ≠ j → covers (points t) i j → covers (points s) i j → t = s) :
    let d := Module.finrank (ZMod 3) (potentialSpace points anchor)
    let q := 3 ^ d
    ∀ b : Module.Basis (Fin d) (ZMod 3) (potentialSpace points anchor),
    let value : I → Fin d → ZMod 3 := fun i k => (b k).val i
    let s := Nat.card {i : I // value i = 0}
    q * (q - 1) * s ^ 2 ≤ 6 * Fintype.card T := by
  classical
  intro d q b value s
  obtain ⟨_, fibers, total, _, _⟩ := point_potential_evaluations points hinj hdis anchor b
  have size (x : Fin d → ZMod 3) : Nat.card {i : I // value i = x} = s :=
    Nat.card_congr (fibers x 0).some
  have covered (i j : I) (hne : value i ≠ value j) :
      ∃ t a b, points t a = i ∧ points t b = j := by
    by_contra missing
    apply hne
    funext k
    exact (show IsOmissionPotential points anchor (b k).val from (b k).prop).2.2.2.1 i j missing
  have bound := mixed_pair_card_le_six_mul_triple_card points value covered
  rw [mixed_pair_card value s size] at bound
  change Fintype.card I = q * s at total
  have diff : q * s - s = (q - 1) * s := by rw [Nat.sub_mul, Nat.one_mul]
  rw [total, diff] at bound
  convert bound using 1
  ring

private abbrev LiftPoint (d s : ℕ) := (Fin d → ZMod 3) × ZMod s

private def liftedTriple {d s : ℕ} (triangle : Finset (LiftPoint d s)) : Prop :=
  triangle.card = 3 ∧ Set.InjOn Prod.fst (triangle : Set (LiftPoint d s)) ∧ ∑ p ∈ triangle, p = 0

private theorem liftedTriple_existsUnique {d s : ℕ} (x y : LiftPoint d s)
    (different : x.1 ≠ y.1) :
    ∃! triangle : Finset (LiftPoint d s), liftedTriple triangle ∧ x ∈ triangle ∧ y ∈ triangle := by
  classical
  let z := -(x + y)
  have neg_add_ne (a b : Fin d → ZMod 3) (hne : a ≠ b) : -(a + b) ≠ a := by
    intro he
    have triple : (a + a) + a = 0 := by
      simpa only [three_nsmul, add_assoc] using ZModModule.char_nsmul_eq_zero 3 a
    have separate : (a + a) + b = 0 := by
      calc
        (a + a) + b = a + (a + b) := add_assoc _ _ _
        _ = -(a + b) + (a + b) := congrArg (· + (a + b)) he.symm
        _ = 0 := neg_add_cancel _
    exact hne (add_left_cancel (triple.trans separate.symm))
  have zx : z.1 ≠ x.1 := neg_add_ne x.1 y.1 different
  have zy : z.1 ≠ y.1 := by
    change -(x.1 + y.1) ≠ y.1
    rw [add_comm]
    exact neg_add_ne y.1 x.1 (Ne.symm different)
  have xy_ne : x ≠ y := fun h => different (congrArg Prod.fst h)
  have xz_ne : x ≠ z := fun h => zx (congrArg Prod.fst h.symm)
  have yz_ne : y ≠ z := fun h => zy (congrArg Prod.fst h.symm)
  have x_out : x ∉ ({y,z} : Finset (LiftPoint d s)) := by simp [xy_ne, xz_ne]
  have y_out : y ∉ ({z} : Finset (LiftPoint d s)) := by simp [yz_ne]
  refine ⟨{x,y,z}, ⟨⟨card_eq_three.mpr ⟨x,y,z,xy_ne,xz_ne,yz_ne,rfl⟩, ?_, ?_⟩,
    by simp, by simp⟩, ?_⟩
  · intro i hi j hj he
    simp only [mem_coe, mem_insert, mem_singleton] at hi hj
    rcases hi with (rfl | rfl | rfl) <;> rcases hj with (rfl | rfl | rfl) <;>
      first | rfl | exact (different he).elim | exact (different he.symm).elim |
        exact (zx he).elim | exact (zx he.symm).elim |
        exact (zy he).elim | exact (zy he.symm).elim
  · rw [sum_insert x_out, sum_insert y_out, sum_singleton]
    change x + (y + -(x + y)) = 0
    rw [← add_assoc, add_neg_cancel]
  · intro triangle h
    obtain ⟨⟨hcard, _, hsum⟩, hx, hy⟩ := h
    have hy' : y ∈ triangle.erase x := mem_erase.mpr ⟨Ne.symm xy_ne, hy⟩
    have singleton : ((triangle.erase x).erase y).card = 1 := by
      rw [card_erase_of_mem hy', card_erase_of_mem hx, hcard]
    obtain ⟨w, hw⟩ := card_eq_one.mp singleton
    have yw : y ≠ w := by
      have hwy : w ∈ (triangle.erase x).erase y := by rw [hw, mem_singleton]
      exact (mem_erase.mp hwy).1.symm
    have xw : x ≠ w := by
      have hwy : w ∈ (triangle.erase x).erase y := by rw [hw, mem_singleton]
      exact (mem_erase.mp (mem_erase.mp hwy).2).1.symm
    have restore_y : insert y ({w} : Finset (LiftPoint d s)) = triangle.erase x := by
      rw [← hw, insert_erase hy']
    have restore : triangle = {x,y,w} := calc
      triangle = insert x (triangle.erase x) := (insert_erase hx).symm
      _ = _ := by rw [← restore_y]
    rw [restore, sum_insert (by simp [xy_ne,xw]), sum_insert (by simp [yw]), sum_singleton] at hsum
    have hwz : w = z := by
      change w = -(x + y)
      exact eq_neg_of_add_eq_zero_right (by simpa only [add_assoc] using hsum)
    rw [restore, hwz]

end D5.S3.Combinatorics.Matroids.RankThreeOmissionPairCount
