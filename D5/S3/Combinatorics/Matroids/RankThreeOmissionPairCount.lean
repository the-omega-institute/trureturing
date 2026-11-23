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

private abbrev LiftTriangle (d s : ℕ) :=
  {triangle : Finset (LiftPoint d s) // liftedTriple triangle}

private noncomputable def liftedPoints {d s : ℕ} (t : LiftTriangle d s) (k : Fin 3) :
    LiftPoint d s := ((Finset.equivFinOfCardEq t.prop.1).symm k).val

private theorem liftedPoints_injective {d s : ℕ} (t : LiftTriangle d s) :
    Function.Injective (liftedPoints t) := by
  intro i j h
  exact (Finset.equivFinOfCardEq t.prop.1).symm.injective (Subtype.ext h)

private theorem liftedPoints_range {d s : ℕ} (t : LiftTriangle d s) (p : LiftPoint d s) :
    (∃ k, liftedPoints t k = p) ↔ p ∈ t.val := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ((Finset.equivFinOfCardEq t.prop.1).symm k).prop
  · intro hp
    use (Finset.equivFinOfCardEq t.prop.1) ⟨p, hp⟩
    simp [liftedPoints]

private theorem liftedPoints_coverage {d s : ℕ} (x y : LiftPoint d s)
    (hne : x ≠ y) :
    (∃ t : LiftTriangle d s, covers (liftedPoints t) x y) ↔ x.1 ≠ y.1 := by
  constructor
  · rintro ⟨t, a, b, ha, hb⟩ h
    exact hne (t.prop.2.1 ((liftedPoints_range t x).mp ⟨a, ha⟩)
      ((liftedPoints_range t y).mp ⟨b, hb⟩) h)
  · intro different
    obtain ⟨S, ⟨admissible, hx, hy⟩, _⟩ := liftedTriple_existsUnique x y different
    let t : LiftTriangle d s := ⟨S, admissible⟩
    obtain ⟨a, ha⟩ := (liftedPoints_range t x).mpr hx
    obtain ⟨b, hb⟩ := (liftedPoints_range t y).mpr hy
    exact ⟨t, a, b, ha, hb⟩

private theorem liftedPoints_pair_unique {d s : ℕ} (t u : LiftTriangle d s)
    (x y : LiftPoint d s) (hne : x ≠ y)
    (ht : covers (liftedPoints t) x y) (hu : covers (liftedPoints u) x y) : t = u := by
  have distinct := (liftedPoints_coverage x y hne).mp ⟨t, ht⟩
  obtain ⟨S, _, unique⟩ := liftedTriple_existsUnique x y distinct
  have member_pair (a : LiftTriangle d s) (h : covers (liftedPoints a) x y) :
      liftedTriple a.val ∧ x ∈ a.val ∧ y ∈ a.val := by
    obtain ⟨i, j, hi, hj⟩ := h
    exact ⟨a.prop, (liftedPoints_range a x).mp ⟨i, hi⟩, (liftedPoints_range a y).mp ⟨j, hj⟩⟩
  exact Subtype.ext ((unique t.val (member_pair t ht)).trans (unique u.val (member_pair u hu)).symm)

private theorem liftedPoints_sum {d s : ℕ} {A : Type*} [AddCommMonoid A]
    (t : LiftTriangle d s) (f : LiftPoint d s → A) :
    (∑ k, f (liftedPoints t k)) = ∑ p ∈ t.val, f p := by
  classical
  let e := (Finset.equivFinOfCardEq t.prop.1).symm
  calc
    _ = ∑ p : {p // p ∈ t.val}, f p.val :=
      Equiv.sum_comp e (fun p => f p.val)
    _ = _ := Finset.sum_attach _ _

private theorem liftedPotential_constant {d s : ℕ} [NeZero s]
    {u : LiftPoint d s → ZMod 3} (hu : IsOmissionPotential liftedPoints 0 u)
    (p : LiftPoint d s) : u p = u (p.1, 0) := by
  by_cases same : p = (p.1, 0)
  · rw [same]
  · apply hu.2.2.2.1
    intro covered
    exact ((liftedPoints_coverage p (p.1, 0) same).mp covered) rfl

private theorem liftedCoordinate_isPotential {d s : ℕ} [NeZero s] (k : Fin d) :
    IsOmissionPotential (liftedPoints (d := d) (s := s)) 0 (fun p => p.1 k) := by
  classical
  refine ⟨rfl, ?_, fun p => ZModModule.char_nsmul_eq_zero 3 (p.1 k), ?_, ?_⟩
  · have h := Equiv.sum_comp (Equiv.neg (LiftPoint d s)) (fun p : LiftPoint d s => p.1 k)
    simp only [Equiv.neg_apply, Prod.fst_neg, Pi.neg_apply, sum_neg_distrib] at h
    let total : ZMod 3 := ∑ p : LiftPoint d s, p.1 k
    change -total = total at h
    change total = 0
    have twice : total + total = 0 :=
      (congrArg (· + total) h.symm).trans (neg_add_cancel total)
    have thrice : (total + total) + total = 0 := by
      simpa only [three_nsmul, add_assoc] using ZModModule.char_nsmul_eq_zero 3 total
    simpa only [twice, zero_add] using thrice
  · intro p q missing
    by_contra h
    have different : p.1 ≠ q.1 := fun eq => h (congrArg (fun a => a k) eq)
    have distinct : p ≠ q := fun eq => different (congrArg Prod.fst eq)
    exact missing ((liftedPoints_coverage p q distinct).mpr different)
  · intro t
    have line := liftedPoints_sum t id
    have zero : (∑ j, liftedPoints t j) = 0 := line.trans t.prop.2.2
    let coord : LiftPoint d s →+ ZMod 3 :=
      { toFun := fun p => p.1 k, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have h := congrArg coord zero
    rw [map_sum, map_zero] at h
    simpa only [coord, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.sum_univ_three] using h

private theorem liftedPotential_finrank (d s : ℕ) [NeZero s] :
    Module.finrank (ZMod 3) (potentialSpace (liftedPoints (d := d) (s := s)) 0) = d := by
  classical
  let P := potentialSpace (liftedPoints (d := d) (s := s)) 0
  let e := Module.finrank (ZMod 3) P
  let b := Module.finBasis (ZMod 3) P
  have ev := point_potential_evaluations liftedPoints liftedPoints_injective
    liftedPoints_pair_unique (0 : LiftPoint d s) b
  let rowValue (x : Fin d → ZMod 3) (k : Fin e) := (b k).val (x, 0)
  have onto : Function.Surjective rowValue := by
    intro z
    obtain ⟨p, hp⟩ := ev.1 z
    refine ⟨p.1, funext fun k => ?_⟩
    exact (liftedPotential_constant (b k).prop p).symm.trans (congrFun hp k)
  have upper := Fintype.card_le_of_surjective rowValue onto
  have upper' : 3 ^ e ≤ 3 ^ d := by
    simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using upper
  let coord (k : Fin d) : P := ⟨fun p => p.1 k, liftedCoordinate_isPotential k⟩
  have independent : LinearIndependent (ZMod 3) coord := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc k
    have hk := congrArg (fun u : P => u.val (Pi.single k 1, 0)) hc
    simpa [coord, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
      mul_ite, eq_comm] using hk
  exact le_antisymm ((Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp upper')
    (by simpa only [Fintype.card_fin] using independent.fintype_card_le_finrank)

private theorem liftedTriangle_count (d s : ℕ) [NeZero s] :
    6 * Nat.card (LiftTriangle d s) = 3 ^ d * (3 ^ d - 1) * s ^ 2 := by
  classical
  let slots := {e : Fin 3 × Fin 3 // e.1 ≠ e.2}
  let mixed := {p : LiftPoint d s × LiftPoint d s // p.1.1 ≠ p.2.1}
  have different (t : LiftTriangle d s) (a : slots) :
      (liftedPoints t a.val.1).1 ≠ (liftedPoints t a.val.2).1 := by
    intro eq
    exact a.prop (liftedPoints_injective t (t.prop.2.1
      ((liftedPoints_range t _).mp ⟨a.val.1, rfl⟩)
      ((liftedPoints_range t _).mp ⟨a.val.2, rfl⟩) eq))
  let toPair (w : LiftTriangle d s × slots) : mixed :=
    ⟨(liftedPoints w.1 w.2.val.1, liftedPoints w.1 w.2.val.2), different w.1 w.2⟩
  have inj : Function.Injective toPair := by
    rintro ⟨t, a⟩ ⟨u, b⟩ eq
    have first := congrArg (fun p : mixed => p.val.1) eq
    have second := congrArg (fun p : mixed => p.val.2) eq
    change liftedPoints t a.val.1 = liftedPoints u b.val.1 at first
    change liftedPoints t a.val.2 = liftedPoints u b.val.2 at second
    have distinct := (liftedPoints_injective t).ne a.prop
    have tu := liftedPoints_pair_unique t u _ _ distinct ⟨a.val.1, a.val.2, rfl, rfl⟩
      ⟨b.val.1, b.val.2, first.symm, second.symm⟩
    subst u
    exact congrArg (Prod.mk t) (Subtype.ext (Prod.ext
      (liftedPoints_injective t first) (liftedPoints_injective t second)))
  have onto : Function.Surjective toPair := by
    rintro ⟨⟨x,y⟩, different⟩
    have distinct : x ≠ y := fun eq => different (congrArg Prod.fst eq)
    obtain ⟨t, i, j, hi, hj⟩ := (liftedPoints_coverage x y distinct).mpr different
    have ij : i ≠ j := fun eq => distinct (hi.symm.trans (eq ▸ hj))
    exact ⟨(t, ⟨(i,j), ij⟩), Subtype.ext (Prod.ext hi hj)⟩
  have hcount := Nat.card_congr (Equiv.ofBijective toPair ⟨inj, onto⟩)
  have six : Nat.card slots = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [Nat.card_prod, six, Nat.mul_comm] at hcount
  have row_size (x : Fin d → ZMod 3) :
      Nat.card {p : LiftPoint d s // p.1 = x} = s := by
    let e : {p : LiftPoint d s // p.1 = x} ≃ ZMod s :=
      { toFun := fun p => p.val.2
        invFun := fun y => ⟨(x, y), rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext p.prop.symm rfl)
        right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans (Nat.card_zmod s)
  have total : Fintype.card (LiftPoint d s) = 3 ^ d * s := by
    simp [LiftPoint, Fintype.card_prod, ZMod.card]
  change 6 * Nat.card (LiftTriangle d s) =
    Nat.card {p : LiftPoint d s × LiftPoint d s // p.1.1 ≠ p.2.1} at hcount
  rw [hcount, mixed_pair_card Prod.fst s row_size, total]
  have diff : 3 ^ d * s - s = (3 ^ d - 1) * s := by rw [Nat.sub_mul, Nat.one_mul]
  rw [diff]
  ring

/-- Lift every ternary affine line by cyclic coordinates with zero sum.
The resulting family has the prescribed potential dimension and attains the pair count. -/
theorem exists_lifted_omission_family (d s : ℕ) [NeZero s] :
    ∃ (T : Type) (points : T → Fin 3 → (Fin d → ZMod 3) × ZMod s),
      Finite T ∧ (∀ t, Function.Injective (points t)) ∧
      (∀ t u x y, x ≠ y → covers (points t) x y → covers (points u) x y → t = u) ∧
      Module.finrank (ZMod 3) (potentialSpace points 0) = d ∧
      6 * Nat.card T = 3 ^ d * (3 ^ d - 1) * s ^ 2 := by
  classical
  exact ⟨LiftTriangle d s, liftedPoints, inferInstance, liftedPoints_injective,
    liftedPoints_pair_unique, liftedPotential_finrank d s, liftedTriangle_count d s⟩

end D5.S3.Combinatorics.Matroids.RankThreeOmissionPairCount
