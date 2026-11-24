/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFaceDefect
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFaceDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.ToLinearEquiv]
   utility: none
   digest: Classify rank loss on a signed three-cube block and bound the four-face exterior. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

/-!
# Four-face capacity from a three-axis defect

The axis is arbitrary. Projected parity is the parity of the three retained coordinates.
The exterior is the complement of the closed neighborhood in the four-face.
-/


namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q4FaceCapacity

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj)
open BalancedCubeGirth (adjacent_exists_flip)
open BalancedCubeComponentBoundary (directions mem_directions)
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

abbrev project (a : Fin 4) (z : Q 4) : Q 3 :=
  Fin.removeNth (α := fun _ => Bool) a z

abbrev lift (a : Fin 4) (v : Bool) (x : Q 3) : Q 4 :=
  Fin.insertNth (α := fun _ => Bool) a v x

def antipode (x : Q 3) : Q 3 := fun j => !x j

def parityClass (b : Bool) : Finset (Q 3) :=
  Finset.univ.filter fun x => cubeParity x = b

def doubleColumns (A : Finset (Q 4)) (a : Fin 4) (b : Bool) : Finset (Q 3) :=
  (parityClass b).filter fun x => lift a false x ∈ A ∧ lift a true x ∈ A

def emptyRows (A : Finset (Q 4)) (a : Fin 4) (b : Bool) : Finset (Q 3) :=
  (parityClass (!b)).filter fun x => lift a false x ∉ A ∧ lift a true x ∉ A

open Classical in
noncomputable def exterior (A : Finset (Q 4)) : Finset (Q 4) :=
  Finset.univ.filter fun z => z ∉ A ∧ ∀ w ∈ A, ¬ (hypercube 4).Adj z w

/-- The three configurations from the defect test. -/
def DeficiencyWitness (A : Finset (Q 4)) (a : Fin 4) (b : Bool) : Prop :=
  let P := doubleColumns A a b
  let T := emptyRows A a b
  T.card < P.card ∨
    (P.card = 1 ∧ T.card = 1 ∧ ∃ x ∈ P, antipode x ∈ T) ∨
    (P.card = 3 ∧ T.card = 3 ∧
      ∃ x ∈ parityClass b \ P, antipode x ∈ parityClass (!b) \ T)

/-- The entries on the domain of `DeficiencyWitness`, in terms of the two cardinalities. -/
private def capacity (p t : ℕ) : ℕ :=
  if p = 1 then
    if t = 0 then 1 else 3
  else if p = 3 ∧ t = 3 then 2
  else 4 - p

@[simp] private theorem mem_parityClass {b : Bool} {x : Q 3} :
    x ∈ parityClass b ↔ cubeParity x = b := by
  simp [parityClass]

private theorem mem_doubleColumns {A : Finset (Q 4)} {a : Fin 4} {b : Bool} {x : Q 3} :
    x ∈ doubleColumns A a b ↔
      cubeParity x = b ∧ lift a false x ∈ A ∧ lift a true x ∈ A := by
  rw [doubleColumns, Finset.mem_filter, mem_parityClass]

private theorem mem_emptyRows {A : Finset (Q 4)} {a : Fin 4} {b : Bool} {x : Q 3} :
    x ∈ emptyRows A a b ↔
      cubeParity x = !b ∧ lift a false x ∉ A ∧ lift a true x ∉ A := by
  rw [emptyRows, Finset.mem_filter, mem_parityClass]

@[simp] theorem mem_exterior {A : Finset (Q 4)} {z : Q 4} :
    z ∈ exterior A ↔ z ∉ A ∧ ∀ w ∈ A, ¬ (hypercube 4).Adj z w := by
  simp [exterior]

private theorem parityClass_card (b : Bool) : (parityClass b).card = 4 := by
  cases b <;> decide +kernel

private theorem antipode_injective : Function.Injective antipode := by
  intro x y h
  funext j
  have hj := congrArg Bool.not (congrFun h j)
  simpa only [antipode, Bool.not_not] using hj

private theorem parity_antipode : ∀ x : Q 3, cubeParity (antipode x) = !cubeParity x := by
  decide +kernel

-- The only cube adjacency table in the Lean proof has eight vertices.
private theorem q3_matching :
    ∀ x y : Q 3, cubeParity y ≠ cubeParity x →
      ((hypercube 3).Adj x y ↔ y ≠ antipode x) := by
  change ∀ x y : Q 3, cubeParity y ≠ cubeParity x →
    (hammingDist x y = 1 ↔ y ≠ antipode x)
  decide +kernel

private theorem exists_adj_of_two {S : Finset (Q 3)} (x : Q 3)
    (hcard : 1 < S.card) (hpar : ∀ y ∈ S, cubeParity y ≠ cubeParity x) :
    ∃ y ∈ S, (hypercube 3).Adj x y := by
  obtain ⟨y, z, hy, hz, hne⟩ := Finset.one_lt_card_iff.mp hcard
  by_cases hya : y = antipode x
  · exact ⟨z, hz, (q3_matching x z (hpar z hz)).2 fun hza =>
      hne (hya.trans hza.symm)⟩
  · exact ⟨y, hy, (q3_matching x y (hpar y hy)).2 hya⟩

private theorem lift_self (a : Fin 4) (z : Q 4) :
    lift a (z a) (project a z) = z :=
  Fin.insertNth_self_removeNth (α := fun _ => Bool) a z

private theorem flip_axis (a : Fin 4) (v : Bool) (x : Q 3) :
    flip (lift a v x) a = lift a (!v) x := by
  simpa only [BalancedCriticalSpectrum.flip, lift, Fin.insertNth_apply_same] using
    Fin.update_insertNth (α := fun _ => Bool) a v (!v) x

private theorem flip_transverse (a : Fin 4) (v : Bool) (x : Q 3) (j : Fin 3) :
    flip (lift a v x) (a.succAbove j) = lift a v (flip x j) := by
  simpa only [BalancedCriticalSpectrum.flip, lift, Fin.insertNth_apply_succAbove] using
    (Fin.insertNth_update (α := fun _ => Bool) a v j (!x j) x).symm

private theorem lift_mem_of_double {A : Finset (Q 4)} {a : Fin 4} {b : Bool} {x : Q 3}
    (hx : x ∈ doubleColumns A a b) (v : Bool) : lift a v x ∈ A := by
  have h := (mem_doubleColumns.mp hx).2
  cases v
  · exact h.1
  · exact h.2

private theorem occupied_of_not_empty {A : Finset (Q 4)} {a : Fin 4} {b : Bool} {x : Q 3}
    (hx : cubeParity x = !b) (ht : x ∉ emptyRows A a b) :
    ∃ v, lift a v x ∈ A := by
  by_cases hf : lift a false x ∈ A
  · exact ⟨false, hf⟩
  by_cases hh : lift a true x ∈ A
  · exact ⟨true, hh⟩
  exact False.elim (ht (mem_emptyRows.mpr ⟨hx, hf, hh⟩))

private theorem exterior_has_no_occupied_endpoint {A : Finset (Q 4)} {a : Fin 4} {z : Q 4}
    (hz : z ∈ exterior A) (v : Bool) : lift a v (project a z) ∉ A := by
  intro hv
  have hz' := mem_exterior.mp hz
  by_cases h : v = z a
  · rw [h, lift_self] at hv
    exact hz'.1 hv
  · have hflip : flip z a = lift a (!z a) (project a z) := by
      simpa only [lift_self] using flip_axis a (z a) (project a z)
    rw [Bool.eq_not_of_ne h] at hv
    exact hz'.2 _ hv (hflip ▸ flip_adj z a)

private theorem exterior_has_no_adjacent_endpoint {A : Finset (Q 4)} {a : Fin 4}
    {z : Q 4} {x : Q 3} (hz : z ∈ exterior A)
    (h : (hypercube 3).Adj (project a z) x) : lift a (z a) x ∉ A := by
  obtain ⟨j, rfl⟩ := adjacent_exists_flip h
  rw [← flip_transverse, lift_self]
  exact fun hx => (mem_exterior.mp hz).2 _ hx (flip_adj z (a.succAbove j))

/-- Two double columns cover the entire opposite parity. Exterior vertices project
to the remaining fibres of the chosen parity. -/
private theorem exterior_projects_to_remaining_columns {A : Finset (Q 4)} {a : Fin 4}
    {b : Bool} (hp : 2 ≤ (doubleColumns A a b).card) {z : Q 4}
    (hz : z ∈ exterior A) : project a z ∈ parityClass b \ doubleColumns A a b := by
  have hpar : cubeParity (project a z) = b := by
    by_contra hne
    obtain ⟨x, hx, ha⟩ := exists_adj_of_two (project a z) hp (fun x hx => by
      rw [(mem_doubleColumns.mp hx).1]
      exact fun he => hne he.symm)
    exact exterior_has_no_adjacent_endpoint hz ha (lift_mem_of_double hx (z a))
  refine Finset.mem_sdiff.mpr ⟨mem_parityClass.mpr hpar, fun hx => ?_⟩
  exact exterior_has_no_occupied_endpoint hz false (lift_mem_of_double hx false)

private theorem remaining_card (A : Finset (Q 4)) (a : Fin 4) (b : Bool) :
    (parityClass b \ doubleColumns A a b).card = 4 - (doubleColumns A a b).card := by
  have hsub : doubleColumns A a b ⊆ parityClass b := by
    intro x hx
    exact mem_parityClass.mpr (mem_doubleColumns.mp hx).1
  rw [Finset.card_sdiff_of_subset hsub, parityClass_card]

private theorem exterior_card_le_twice_remaining {A : Finset (Q 4)} {a : Fin 4}
    {b : Bool} (hp : 2 ≤ (doubleColumns A a b).card) :
    (exterior A).card ≤ 2 * (4 - (doubleColumns A a b).card) := by
  let e := (Fin.insertNthEquiv (fun _ : Fin 4 => Bool) a).symm
  calc
    (exterior A).card ≤
        (Finset.univ.product (parityClass b \ doubleColumns A a b) :
          Finset (Bool × Q 3)).card := by
      refine Finset.card_le_card_of_injOn e ?_ e.injective.injOn
      intro z hz
      exact Finset.mem_product.mpr
        ⟨Finset.mem_univ _, exterior_projects_to_remaining_columns hp hz⟩
    _ = 2 * (4 - (doubleColumns A a b).card) := by
      simp [Finset.card_product, remaining_card]

/-- With at least two double columns and at least two occupied opposite-parity fibres,
each remaining fibre contains at most one exterior endpoint. -/
private theorem exterior_project_injective {A : Finset (Q 4)} {a : Fin 4} {b : Bool}
    (hp : 2 ≤ (doubleColumns A a b).card) (ht : (emptyRows A a b).card ≤ 2) :
    Set.InjOn (project a) (exterior A : Set (Q 4)) := by
  intro z hz w hw hzw
  let occ := parityClass (!b) \ emptyRows A a b
  have hsub : emptyRows A a b ⊆ parityClass (!b) := by
    intro x hx
    exact mem_parityClass.mpr (mem_emptyRows.mp hx).1
  have hocc : occ.card = 4 - (emptyRows A a b).card := by
    dsimp only [occ]
    rw [Finset.card_sdiff_of_subset hsub, parityClass_card]
  have hpar := mem_parityClass.mp (Finset.mem_sdiff.mp
    (exterior_projects_to_remaining_columns hp hz)).1
  obtain ⟨x, hx, ha⟩ := exists_adj_of_two (S := occ) (project a z) (by omega)
    (fun x hx => by
      rw [mem_parityClass.mp (Finset.mem_sdiff.mp hx).1, hpar]
      exact (Bool.not_eq_self b).mp)
  obtain ⟨v, hv⟩ := occupied_of_not_empty (mem_parityClass.mp (Finset.mem_sdiff.mp hx).1)
    (Finset.mem_sdiff.mp hx).2
  have hza : z a ≠ v := fun he =>
    exterior_has_no_adjacent_endpoint hz ha (he.symm ▸ hv)
  have hwa : w a ≠ v := fun he =>
    exterior_has_no_adjacent_endpoint hw (hzw ▸ ha) (he.symm ▸ hv)
  have he := (Bool.eq_not_of_ne hza).trans (Bool.eq_not_of_ne hwa).symm
  calc
    z = lift a (z a) (project a z) := (lift_self a z).symm
    _ = lift a (w a) (project a w) := by rw [he, hzw]
    _ = w := lift_self a w

private theorem exterior_card_le_remaining {A : Finset (Q 4)} {a : Fin 4} {b : Bool}
    (hp : 2 ≤ (doubleColumns A a b).card) (ht : (emptyRows A a b).card ≤ 2) :
    (exterior A).card ≤ 4 - (doubleColumns A a b).card := by
  rw [← remaining_card A a b]
  refine Finset.card_le_card_of_injOn (project a) ?_ (exterior_project_injective hp ht)
  intro z hz
  exact exterior_projects_to_remaining_columns hp hz

-- This only inspects the eight choices of axial bits in the three neighbouring fibres.
private theorem axial_choices :
    ∀ s : Fin 3 → Bool, (∃ v, ∀ j, s j = v) ∨
      ∃ j k l, j ≠ k ∧ s j = s k ∧ s l ≠ s j := by
  decide +kernel

/-- The axial edge and one endpoint in each of the three neighboring fibres form
the five-vertex template. The matching identifies the unique possible exterior
vertex on the center's projected parity. -/
private theorem template_capacity {A : Finset (Q 4)} {a : Fin 4} {b : Bool} {x : Q 3}
    (hdeg : ∀ z ∈ A, (directions A z).card ≤ 3) (hx : x ∈ doubleColumns A a b)
    (hnear : ∀ j : Fin 3, ∃ v, lift a v (flip x j) ∈ A) :
    (exterior A).card ≤ 3 ∧
      ((∃ v, lift a v (antipode x) ∈ A) → (exterior A).card ≤ 1) := by
  classical
  choose s hs using hnear
  have hmixed : ¬ ∃ v, ∀ j, s j = v := by
    rintro ⟨v, hv⟩
    have hall : directions A (lift a v x) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      rw [Fin.forall_iff_succAbove a]
      refine ⟨?_, ?_⟩
      · rw [mem_directions, flip_axis]
        exact lift_mem_of_double hx (!v)
      · intro j
        rw [mem_directions, flip_transverse, ← hv j]
        exact hs j
    have hd := hdeg _ (lift_mem_of_double hx v)
    rw [hall, Finset.card_univ, Fintype.card_fin] at hd
    omega
  obtain ⟨j, k, l, hjk, hsame, hdiff⟩ := (axial_choices s).resolve_left hmixed
  let candidate := lift a (s l) (antipode (flip x l))
  have hclassify {z : Q 4} (hz : z ∈ exterior A) :
      z = candidate ∨ project a z = antipode x := by
    by_cases hpar : cubeParity (project a z) = cubeParity x
    · left
      have hforce (i : Fin 3) (hbit : z a = s i) :
          project a z = antipode (flip x i) := by
        have hflip := cubeParity_ne_of_adj (flip_adj x i)
        by_contra hne
        have ha : (hypercube 3).Adj (flip x i) (project a z) :=
          (q3_matching _ _ (hpar.trans_ne hflip)).2 hne
        exact exterior_has_no_adjacent_endpoint hz ha.symm (hbit.symm ▸ hs i)
      have hmajor : z a ≠ s j := by
        intro he
        have h1 := hforce j he
        have h2 := hforce k (he.trans hsame)
        exact hjk (BalancedCubeComponentBoundary.flip_injective x
          (antipode_injective (h1.symm.trans h2)))
      have hbit := (Bool.eq_not_of_ne hmajor).trans (Bool.eq_not_of_ne hdiff).symm
      exact (Fin.eq_insertNth_iff.mpr ⟨hbit, hforce l hbit⟩)
    · right
      by_contra hne
      have ha : (hypercube 3).Adj x (project a z) := (q3_matching _ _ hpar).2 hne
      exact exterior_has_no_adjacent_endpoint hz ha.symm (lift_mem_of_double hx (z a))
  refine ⟨?_, ?_⟩
  · refine (Finset.card_le_card (t := {candidate, lift a false (antipode x),
        lift a true (antipode x)}) ?_).trans Finset.card_le_three
    intro z hz
    rcases hclassify hz with rfl | hproj
    · simp
    · have he : z = lift a (z a) (antipode x) := Fin.eq_insertNth_iff.mpr ⟨rfl, hproj⟩
      cases hv : z a <;> rw [hv] at he <;> rw [he] <;> simp
  · rintro ⟨v, hv⟩
    apply Finset.card_le_one_iff_subset_singleton.mpr
    refine ⟨candidate, ?_⟩
    intro z hz
    apply Finset.mem_singleton.mpr
    rcases hclassify hz with he | hproj
    · exact he
    · exact False.elim (exterior_has_no_occupied_endpoint (a := a) hz v (by rwa [hproj]))

/-- GPT-6 Pro's six case bounds on the full complement of the closed neighborhood.
The repository's `directions` counts the neighbours in the induced subgraph. -/
private theorem exterior_card_le_capacity (A : Finset (Q 4)) (a : Fin 4) (b : Bool)
    (hdeg : ∀ z ∈ A, (directions A z).card ≤ 3) (h : DeficiencyWitness A a b) :
    (exterior A).card ≤ capacity (doubleColumns A a b).card (emptyRows A a b).card := by
  classical
  let P := doubleColumns A a b
  let T := emptyRows A a b
  change (exterior A).card ≤ capacity P.card T.card
  have hsub : P ⊆ parityClass b := by
    intro x hx
    exact mem_parityClass.mpr (mem_doubleColumns.mp hx).1
  have hp4 : P.card ≤ 4 := by
    exact (Finset.card_le_card hsub).trans_eq (parityClass_card b)
  have near (x : Q 3) (hx : x ∈ P) (hT : ∀ y ∈ T, y = antipode x)
      (j : Fin 3) : ∃ v, lift a v (flip x j) ∈ A := by
    have hp := (mem_doubleColumns.mp hx).1
    have hne := cubeParity_ne_of_adj (flip_adj x j)
    have hf : cubeParity (flip x j) = !b := (Bool.eq_not_of_ne hne.symm).trans
      (congrArg Bool.not hp)
    refine occupied_of_not_empty hf (fun hy => ?_)
    exact ((q3_matching x (flip x j) hne.symm).1 (flip_adj x j)) (hT _ hy)
  unfold DeficiencyWitness at h
  rcases h with hsurplus | ⟨hp, ht, x, hx, hanti⟩ | ⟨hp, ht, _⟩
  · change T.card < P.card at hsurplus
    by_cases hp : P.card = 1
    · have ht : T.card = 0 := by omega
      obtain ⟨x, hxP⟩ := Finset.card_eq_one.mp hp
      have hx : x ∈ P := by simp [hxP]
      have hnone : T = ∅ := Finset.card_eq_zero.mp ht
      have hnear := near x hx (fun y hy => by simp [hnone] at hy)
      have hocc : ∃ v, lift a v (antipode x) ∈ A := by
        have hanti : cubeParity (antipode x) = !b := by
          rw [parity_antipode, (mem_doubleColumns.mp hx).1]
        exact occupied_of_not_empty hanti (show antipode x ∉ T by simp [hnone])
      have hbound := (template_capacity hdeg hx hnear).2 hocc
      simpa [capacity, hp, ht] using hbound
    · have htwo : 2 ≤ P.card := by omega
      by_cases ht : T.card ≤ 2
      · have hthree : T.card ≠ 3 := by omega
        simpa [capacity, hp, hthree] using exterior_card_le_remaining htwo ht
      · have hp' : P.card = 4 := by omega
        have hbound : (exterior A).card ≤ 2 * (4 - P.card) :=
          exterior_card_le_twice_remaining htwo
        simpa [capacity, hp'] using hbound
  · change P.card = 1 at hp
    change T.card = 1 at ht
    change antipode x ∈ T at hanti
    have hT : ∀ y ∈ T, y = antipode x := by
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp ht
      have hwa : antipode x = w := by simpa [hw] using hanti
      intro y hy
      exact (Finset.mem_singleton.mp (hw ▸ hy)).trans hwa.symm
    have hbound := (template_capacity hdeg hx (near x hx hT)).1
    simpa [capacity, hp, ht] using hbound
  · change P.card = 3 at hp
    change T.card = 3 at ht
    have htwo : 2 ≤ P.card := by omega
    have hbound : (exterior A).card ≤ 2 * (4 - P.card) :=
      exterior_card_le_twice_remaining htwo
    simpa [capacity, hp, ht] using hbound

/-- A witnessed defect leaves at most three vertices in the full exterior. -/
theorem exterior_card_le_three (A : Finset (Q 4)) (a : Fin 4) (b : Bool)
    (hdeg : ∀ z ∈ A, (directions A z).card ≤ 3) (h : DeficiencyWitness A a b) :
    (exterior A).card ≤ 3 := by
  refine (exterior_card_le_capacity A a b hdeg h).trans ?_
  have hp : 0 < (doubleColumns A a b).card := by
    unfold DeficiencyWitness at h
    rcases h with hs | ⟨hs, _, _⟩ | ⟨hs, _, _⟩ <;> omega
  unfold capacity
  split <;> split <;> omega

/-- Count both endpoints of each double fibre and one endpoint of each
occupied opposite-parity fibre. -/
private theorem occupancy_lower_bound (A : Finset (Q 4)) (a : Fin 4) (b : Bool) :
    2 * (doubleColumns A a b).card + (4 - (emptyRows A a b).card) ≤ A.card := by
  classical
  let low := A.filter fun z => cubeParity (project a z) = b
  let high := A.filter fun z => cubeParity (project a z) ≠ b
  let P := doubleColumns A a b
  let T := emptyRows A a b
  let occ := parityClass (!b) \ T
  let e := Fin.insertNthEquiv (fun _ : Fin 4 => Bool) a
  have hlow : 2 * P.card ≤ low.card := by
    calc
      2 * P.card = (Finset.univ.product P : Finset (Bool × Q 3)).card := by
        simp [Finset.card_product]
      _ ≤ _ := by
        apply Finset.card_le_card_of_injOn e _ e.injective.injOn
        intro y hy
        have hP := (mem_doubleColumns.mp (Finset.mem_product.mp hy).2)
        have hmem := lift_mem_of_double (Finset.mem_product.mp hy).2 y.1
        change lift a y.1 y.2 ∈ low
        exact Finset.mem_filter.mpr ⟨hmem, by simpa using hP.1⟩
  have hT : T ⊆ parityClass (!b) := by
    intro x hx
    exact mem_parityClass.mpr (mem_emptyRows.mp hx).1
  have hhigh : 4 - T.card ≤ high.card := by
    have hcard : occ.card = 4 - T.card := by
      dsimp only [occ]
      rw [Finset.card_sdiff_of_subset hT, parityClass_card]
    rw [← hcard]
    let insertOccupied (x : Q 3) := lift a (if lift a false x ∈ A then false else true) x
    apply Finset.card_le_card_of_injOn insertOccupied
    · intro x hx
      have ⟨hpar, hnot⟩ := Finset.mem_sdiff.mp hx
      have hb := mem_parityClass.mp hpar
      obtain ⟨v, hv⟩ := occupied_of_not_empty hb hnot
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · by_cases h : lift a false x ∈ A
        · simpa [insertOccupied, h] using h
        · cases v
          · exact False.elim (h hv)
          · simpa [insertOccupied, h] using hv
      · simpa [insertOccupied, hb] using (Bool.not_eq_self b).mp
    · intro x _ y _ hxy
      simpa [insertOccupied] using congrArg (project a) hxy
  exact (Nat.add_le_add hlow hhigh).trans_eq
    (Finset.card_filter_add_card_filter_not (s := A) (p := fun z => cubeParity (project a z) = b))

/-- A defect witness occupies at least five vertices. -/
theorem five_le_card_of_deficiencyWitness {A : Finset (Q 4)} {a : Fin 4} {b : Bool}
    (h : DeficiencyWitness A a b) : 5 ≤ A.card := by
  refine le_trans ?_ (occupancy_lower_bound A a b)
  unfold DeficiencyWitness at h
  rcases h with hs | ⟨hp, ht, _⟩ | ⟨hp, ht, _⟩ <;> omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q4FaceCapacity

/-!
# Local rank classification for a three-axis mask

The rows and columns of the full signed parity block are each indexed by
`Fin 4`. The permutation `σ` sends each column to its antipodal row.
For the Q3 application, use the paired fibres for `P` and the empty
opposite-parity fibres for `T`. The reindexing from the cube supplies
the zero matching and the Clifford identity `H * Hᵀ = q • 1`.

-/

open scoped BigOperators Matrix

namespace Q9ThreeAxisRank

private noncomputable def support (u : Fin 4 → ℝ) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter (fun j => u j ≠ 0)

@[simp] private theorem mem_support {u : Fin 4 → ℝ} {j : Fin 4} :
    j ∈ support u ↔ u j ≠ 0 := by
  classical
  simp [support]

private theorem card_support_pos {u : Fin 4 → ℝ} (hu : u ≠ 0) :
    0 < (support u).card := by
  classical
  apply Finset.card_pos.mpr
  by_contra h
  apply hu
  funext j
  change u j = 0
  by_contra hj
  exact h ⟨j, mem_support.mpr hj⟩

private theorem mulVec_apply_eq_sum (H : Matrix (Fin 4) (Fin 4) ℝ)
    (u : Fin 4 → ℝ) (S : Finset (Fin 4)) (hS : support u ⊆ S) (r : Fin 4) :
    (H *ᵥ u) r = ∑ j ∈ S, H r j * u j := by
  classical
  change (∑ j : Fin 4, H r j * u j) = _
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro j _ hj
  have hz : u j = 0 := by
    by_contra hn
    exact hj (hS (mem_support.mpr hn))
  rw [hz, mul_zero]

private theorem support_mulVec_singleton (H : Matrix (Fin 4) (Fin 4) ℝ)
    (σ : Fin 4 ≃ Fin 4) (hz : ∀ r c, H r c = 0 ↔ r = σ c)
    {u : Fin 4 → ℝ} {c : Fin 4} (hu : support u = {c}) :
    support (H *ᵥ u) = {σ c}ᶜ := by
  have hc : u c ≠ 0 := mem_support.mp (by simp [hu])
  ext r
  have hr : (H *ᵥ u) r = H r c * u c := by
    have hsub : support u ⊆ {c} := hu.symm ▸ Finset.Subset.refl {c}
    simpa only [Finset.sum_singleton] using mulVec_apply_eq_sum H u {c} hsub r
  simp only [mem_support, hr, Finset.mem_compl, Finset.mem_singleton]
  exact ⟨fun h hrc => h (by rw [(hz r c).2 hrc, zero_mul]),
    fun h => mul_ne_zero (fun hzero => h ((hz r c).1 hzero)) hc⟩

private theorem support_single (c : Fin 4) :
    support (Pi.single c (1 : ℝ)) = {c} := by
  ext j
  by_cases h : j = c <;> simp [Pi.single_apply, h]

-- In the two-column case both matched rows already carry nonzero outputs.
-- If they exhaust the output support, the inverse forces one entry to
-- exhaust the entire squared norm of its row.
private theorem support_two_two_impossible (H : Matrix (Fin 4) (Fin 4) ℝ)
    (σ : Fin 4 ≃ Fin 4) (hz : ∀ r c, H r c = 0 ↔ r = σ c)
    {q : ℝ} (hH : H * Hᵀ = q • 1) {u : Fin 4 → ℝ}
    (hback : Hᵀ *ᵥ (H *ᵥ u) = q • u)
    (hu : (support u).card = 2) (hv : (support (H *ᵥ u)).card = 2) : False := by
  classical
  obtain ⟨c, d, hcd, hU⟩ := Finset.card_eq_two.mp hu
  have hc : u c ≠ 0 := mem_support.mp (by simp [hU])
  have hd : u d ≠ 0 := mem_support.mp (by simp [hU])
  have hmatch : σ c ≠ σ d := fun h => hcd (σ.injective h)
  have hsub : support u ⊆ {c, d} :=
    hU.symm ▸ Finset.Subset.refl {c, d}
  have hv_apply (r : Fin 4) : (H *ᵥ u) r = H r c * u c + H r d * u d := by
    simpa [Finset.sum_insert, hcd] using mulVec_apply_eq_sum H u {c, d} hsub r
  have hv_c : (H *ᵥ u) (σ c) = H (σ c) d * u d := by
    rw [hv_apply, (hz (σ c) c).mpr rfl, zero_mul, zero_add]
  have hv_d : (H *ᵥ u) (σ d) = H (σ d) c * u c := by
    rw [hv_apply, (hz (σ d) d).mpr rfl, zero_mul, add_zero]
  have hV : support (H *ᵥ u) = {σ c, σ d} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · apply mem_support.mpr
        rw [hv_c]
        exact mul_ne_zero (fun h => hmatch ((hz (σ c) d).mp h)) hd
      · apply mem_support.mpr
        rw [hv_d]
        exact mul_ne_zero (fun h => hmatch.symm ((hz (σ d) c).mp h)) hc
    · rw [hv, Finset.card_pair hmatch]
  have hcu : q * u c = H (σ d) c * (H (σ d) c * u c) := by
    have hsubV : support (H *ᵥ u) ⊆ {σ c, σ d} :=
      hV.symm ▸ Finset.Subset.refl {σ c, σ d}
    have hs := mulVec_apply_eq_sum Hᵀ (H *ᵥ u) {σ c, σ d} hsubV c
    rw [hback] at hs
    simpa [Finset.sum_insert, hmatch, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul,
      (hz (σ c) c).mpr rfl, hv_d] using hs
  have hsq : H (σ d) c ^ 2 = q := by
    apply mul_right_cancel₀ hc
    calc
      _ = H (σ d) c * (H (σ d) c * u c) := by ring
      _ = _ := hcu.symm
  have hex : 0 < (({c, d} : Finset (Fin 4))ᶜ).card := by
    rw [Finset.card_compl, Finset.card_pair hcd]
    decide
  obtain ⟨e, he⟩ := Finset.card_pos.mp hex
  have hce : c ≠ e := fun h => (Finset.mem_compl.mp he) (by simp [← h])
  have hde : d ≠ e := fun h => (Finset.mem_compl.mp he) (by simp [← h])
  have hpos : 0 < H (σ d) e ^ 2 :=
    sq_pos_of_ne_zero (fun h => hde (σ.injective ((hz _ _).mp h)))
  have hnorm : (∑ j : Fin 4, H (σ d) j ^ 2) = q := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, pow_two] using congrFun (congrFun hH (σ d)) (σ d)
  have hle : H (σ d) c ^ 2 + H (σ d) e ^ 2 ≤ ∑ j : Fin 4, H (σ d) j ^ 2 := by
    simpa [Finset.sum_insert, hce] using
      (Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun j : Fin 4 => H (σ d) j ^ 2)
        (Finset.subset_univ ({c, e} : Finset (Fin 4))) (fun j _ _ => sq_nonneg (H (σ d) j)))
  rw [hsq, hnorm] at hle
  exact (not_lt_of_ge hle) (lt_add_of_pos_right q hpos)

private theorem submatrix_kernel_iff (H : Matrix (Fin 4) (Fin 4) ℝ)
    (P T : Finset (Fin 4)) :
    (∃ x : P → ℝ, x ≠ 0 ∧
        (H.submatrix (Subtype.val : T → Fin 4) (Subtype.val : P → Fin 4)) *ᵥ x = 0) ↔
      ∃ u : Fin 4 → ℝ, u ≠ 0 ∧ support u ⊆ P ∧ support (H *ᵥ u) ⊆ Tᶜ := by
  classical
  have hmul (u : Fin 4 → ℝ) (hU : support u ⊆ P) (r : T) :
      ((H.submatrix (Subtype.val : T → Fin 4) (Subtype.val : P → Fin 4)) *ᵥ
        (fun c : P => u c)) r = (H *ᵥ u) r := by
    rw [mulVec_apply_eq_sum H u P hU r]
    change (∑ c : P, H r c * u c) = ∑ c ∈ P, H r c * u c
    exact Finset.sum_coe_sort P (fun c : Fin 4 => H r c * u c)
  constructor
  · rintro ⟨x, hx, hker⟩
    let u : Fin 4 → ℝ := fun c => if hc : c ∈ P then x ⟨c, hc⟩ else 0
    have hU : support u ⊆ P := by
      intro c hc
      by_contra h
      exact (mem_support.mp hc) (by simp [u, h])
    have hrest : (fun c : P => u c) = x := by
      funext c
      simp [u, c.property]
    refine ⟨u, ?_, hU, ?_⟩
    · intro h
      apply hx
      rw [← hrest, h]
      rfl
    · intro r hr
      apply Finset.mem_compl.mpr
      intro hTr
      apply mem_support.mp hr
      simpa only [← hmul u hU ⟨r, hTr⟩, hrest, Pi.zero_apply] using
        congrFun hker (⟨r, hTr⟩ : T)
  · rintro ⟨u, hu, hU, hV⟩
    refine ⟨fun c : P => u c, ?_, ?_⟩
    · intro hzero
      apply hu
      funext c
      by_cases hc : c ∈ P
      · exact congrFun hzero ⟨c, hc⟩
      · change u c = 0
        by_contra h
        exact hc (hU (mem_support.mpr h))
    · funext r
      rw [hmul u hU r]
      change (H *ᵥ u) r = 0
      by_contra h
      exact (Finset.mem_compl.mp (hV (mem_support.mpr h))) r.property

/-- The paired-column and empty-row submatrix loses full column rank precisely
when there are more columns than rows, the retained row and column form a
matched singleton pair, or the omitted row and column form a matched pair. -/
theorem submatrix_has_nonzero_kernel_iff (H : Matrix (Fin 4) (Fin 4) ℝ)
    (σ : Fin 4 ≃ Fin 4) {q : ℝ} (hq : q ≠ 0) (hH : H * Hᵀ = q • 1)
    (hz : ∀ r c, H r c = 0 ↔ r = σ c) (P T : Finset (Fin 4)) :
    (∃ x : P → ℝ, x ≠ 0 ∧
        (H.submatrix (Subtype.val : T → Fin 4) (Subtype.val : P → Fin 4)) *ᵥ x = 0) ↔
      T.card < P.card ∨
        (∃ c, P = {c} ∧ T = {σ c}) ∨
        (∃ c, P = {c}ᶜ ∧ T = {σ c}ᶜ) := by
  classical
  by_cases hbig : T.card < P.card
  · let A : Matrix T P ℝ := H.submatrix Subtype.val Subtype.val
    have hdim : Module.finrank ℝ (T → ℝ) < Module.finrank ℝ (P → ℝ) := by
      simpa only [Module.finrank_pi, Fintype.card_coe] using hbig
    have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := A.mulVecLin) hdim
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    exact iff_of_true ⟨x, hx0, LinearMap.mem_ker.mp hx⟩ (Or.inl hbig)
  rw [submatrix_kernel_iff]
  let K : Matrix (Fin 4) (Fin 4) ℝ := q⁻¹ • Hᵀ
  have hHK : H * K = 1 := by
    change H * (q⁻¹ • Hᵀ) = 1
    rw [Matrix.mul_smul, hH, smul_smul, inv_mul_cancel₀ hq, one_smul]
  have hKH : K * H = 1 := mul_eq_one_comm.mp hHK
  have hback (u : Fin 4 → ℝ) : K *ᵥ (H *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, hKH, Matrix.one_mulVec]
  have hforward (v : Fin 4 → ℝ) : H *ᵥ (K *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hHK, Matrix.one_mulVec]
  have hkz (c r : Fin 4) : K c r = 0 ↔ c = σ.symm r := by
    change q⁻¹ * H r c = 0 ↔ c = σ.symm r
    simp only [mul_eq_zero, inv_ne_zero hq, false_or, hz]
    constructor
    · intro h
      rw [h, σ.symm_apply_apply]
    · intro h
      rw [h, σ.apply_symm_apply]
  have hTc : T.card + (Tᶜ).card = 4 := by
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl T
  constructor
  · rintro ⟨u, hu, hU, hV⟩
    let v := H *ᵥ u
    change support v ⊆ Tᶜ at hV
    have hv : v ≠ 0 := by
      intro h
      apply hu
      rw [← hback u, show H *ᵥ u = 0 from h, Matrix.mulVec_zero]
    have hUpos := card_support_pos hu
    have hVpos := card_support_pos hv
    have hUP := Finset.card_le_card hU
    have hVT : (support v).card ≤ (Tᶜ).card := Finset.card_le_card hV
    by_cases hU1 : (support u).card = 1
    · obtain ⟨c, hUc⟩ := Finset.card_eq_one.mp hU1
      have hVc : support v = {σ c}ᶜ := support_mulVec_singleton H σ hz hUc
      have hV3 : (support v).card = 3 := by simp [hVc, Finset.card_compl]
      have hp : support u = P := Finset.eq_of_subset_of_card_le hU (by omega)
      have ht : support v = Tᶜ := Finset.eq_of_subset_of_card_le hV (by omega)
      refine Or.inr (Or.inl ⟨c, hp.symm.trans hUc, ?_⟩)
      simpa only [compl_compl] using congrArg (fun s : Finset (Fin 4) => sᶜ) (ht.symm.trans hVc)
    by_cases hV1 : (support v).card = 1
    · obtain ⟨r, hVr⟩ := Finset.card_eq_one.mp hV1
      have hUr : support u = {σ.symm r}ᶜ :=
        (congrArg support (hback u)).symm.trans (support_mulVec_singleton K σ.symm hkz hVr)
      have hU3 : (support u).card = 3 := by simp [hUr, Finset.card_compl]
      have hp : support u = P := Finset.eq_of_subset_of_card_le hU (by omega)
      have ht : support v = Tᶜ := Finset.eq_of_subset_of_card_le hV (by omega)
      refine Or.inr (Or.inr ⟨σ.symm r, hp.symm.trans hUr, ?_⟩)
      rw [σ.apply_symm_apply]
      simpa only [compl_compl] using congrArg (fun s : Finset (Fin 4) => sᶜ) (ht.symm.trans hVr)
    have hU2 : (support u).card = 2 := by omega
    have hV2 : (support v).card = 2 := by omega
    have hscaled : Hᵀ *ᵥ (H *ᵥ u) = q • u := by
      have h := congrArg (fun f : Fin 4 → ℝ => q • f) (hback u)
      change q • ((q⁻¹ • Hᵀ) *ᵥ (H *ᵥ u)) = q • u at h
      rwa [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hq, one_smul] at h
    exact (support_two_two_impossible H σ hz hH hscaled hU2 hV2).elim
  · rintro (h | ⟨c, rfl, rfl⟩ | ⟨c, rfl, rfl⟩)
    · exact (hbig h).elim
    · let u : Fin 4 → ℝ := Pi.single c 1
      have hU : support u = {c} := support_single c
      have hV := support_mulVec_singleton H σ hz hU
      refine ⟨u, ?_, ?_, ?_⟩
      · intro h
        simpa [u, Pi.single_apply] using congrFun h c
      · simpa only [hU] using Finset.Subset.refl ({c} : Finset (Fin 4))
      · simpa only [hV] using Finset.Subset.refl ({σ c}ᶜ : Finset (Fin 4))
    · let v : Fin 4 → ℝ := Pi.single (σ c) 1
      let u := K *ᵥ v
      have hHu : H *ᵥ u = v := hforward v
      have hV : support v = {σ c} := support_single (σ c)
      have hU : support u = {c}ᶜ := by
        change support (K *ᵥ v) = _
        rw [support_mulVec_singleton K σ.symm hkz hV, σ.symm_apply_apply]
      refine ⟨u, ?_, ?_, ?_⟩
      · intro h
        have hv : v = 0 := by rw [← hHu, h, Matrix.mulVec_zero]
        simpa [v, Pi.single_apply] using congrFun hv (σ c)
      · simpa only [hU] using Finset.Subset.refl ({c}ᶜ : Finset (Fin 4))
      · simpa only [hHu, hV, compl_compl] using Finset.Subset.refl ({σ c} : Finset (Fin 4))

end Q9ThreeAxisRank
