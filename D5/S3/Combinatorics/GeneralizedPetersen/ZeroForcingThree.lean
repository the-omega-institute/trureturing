/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Basic]
   utility: none
   digest: Eight vertices are necessary and sufficient to zero-force P(n,3) for every n at least thirteen. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFortData1
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFortData2
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFortData3
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFortData4
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFortData5
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFortData6
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeTenBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeForts

open D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation (gp)
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite

/-- Every anchored seven-set has a kernel-checked disjoint fort. -/
private theorem anchoredMask_has_disjoint_fort (a : Anchor13) (m : Nat)
    (hm : candidateShapeOK a m = true) :
    ∃ f : Nat, IsFort (gp 13 3) (maskSet13 f) ∧
      Disjoint (maskSet13 m) (maskSet13 f) := by
  have hdisjoint {s f : Nat} (h : disjointOK s f = true) :
      Disjoint (maskSet13 s) (maskSet13 f) := by
    have hland : s &&& f = 0 := (of_decide_eq_true h).2.2
    rw [Finset.disjoint_left]
    intro v hsv hfv
    have hs : s.testBit (code13 v) = true := by simpa [maskSet13] using hsv
    have hf : f.testBit (code13 v) = true := by simpa [maskSet13] using hfv
    have hz := congrArg (fun z : Nat => z.testBit (code13 v)) hland
    simp [hs, hf] at hz
  cases a with
  | outerSpoke =>
      obtain ⟨rows, horder, hrows⟩ := ZeroForcingThreeFortData1.certifiedFamily
      obtain ⟨f, hf⟩ := orderedRows_complete horder
        (fun row hr => (hrows row hr).1) hm
      have hok := (hrows (m, f) hf).2
      rw [rowOK, Bool.and_eq_true] at hok
      refine ⟨f, fortOK_sound ?_, hdisjoint ?_⟩
      · exact hok.1
      · exact hok.2
  | outerNext =>
      obtain ⟨rows, horder, hrows⟩ := ZeroForcingThreeFortData2.certifiedFamily
      obtain ⟨f, hf⟩ := orderedRows_complete horder
        (fun row hr => (hrows row hr).1) hm
      have hok := (hrows (m, f) hf).2
      rw [rowOK, Bool.and_eq_true] at hok
      refine ⟨f, fortOK_sound ?_, hdisjoint ?_⟩
      · exact hok.1
      · exact hok.2
  | outerPrev =>
      obtain ⟨rows, horder, hrows⟩ := ZeroForcingThreeFortData3.certifiedFamily
      obtain ⟨f, hf⟩ := orderedRows_complete horder
        (fun row hr => (hrows row hr).1) hm
      have hok := (hrows (m, f) hf).2
      rw [rowOK, Bool.and_eq_true] at hok
      refine ⟨f, fortOK_sound ?_, hdisjoint ?_⟩
      · exact hok.1
      · exact hok.2
  | innerSpoke =>
      obtain ⟨rows, horder, hrows⟩ := ZeroForcingThreeFortData4.certifiedFamily
      obtain ⟨f, hf⟩ := orderedRows_complete horder
        (fun row hr => (hrows row hr).1) hm
      have hok := (hrows (m, f) hf).2
      rw [rowOK, Bool.and_eq_true] at hok
      refine ⟨f, fortOK_sound ?_, hdisjoint ?_⟩
      · exact hok.1
      · exact hok.2
  | innerNext =>
      obtain ⟨rows, horder, hrows⟩ := ZeroForcingThreeFortData5.certifiedFamily
      obtain ⟨f, hf⟩ := orderedRows_complete horder
        (fun row hr => (hrows row hr).1) hm
      have hok := (hrows (m, f) hf).2
      rw [rowOK, Bool.and_eq_true] at hok
      refine ⟨f, fortOK_sound ?_, hdisjoint ?_⟩
      · exact hok.1
      · exact hok.2
  | innerPrev =>
      obtain ⟨rows, horder, hrows⟩ := ZeroForcingThreeFortData6.certifiedFamily
      obtain ⟨f, hf⟩ := orderedRows_complete horder
        (fun row hr => (hrows row hr).1) hm
      have hok := (hrows (m, f) hf).2
      rw [rowOK, Bool.and_eq_true] at hok
      refine ⟨f, fortOK_sound ?_, hdisjoint ?_⟩
      · exact hok.1
      · exact hok.2

#print axioms anchoredMask_has_disjoint_fort

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeForts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree

open D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation (gp)
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeForts

/-- The closure `cl(S)` under the color change rule: a black vertex all of whose neighbours except `w`
    are black forces `w` black. `Black G S` is the least vertex set containing `S` and closed under the rule. -/
inductive Black {V : Type*} (G : SimpleGraph V) (S : Set V) : V → Prop
  | init {v : V} : v ∈ S → Black G S v
  | force {u w : V} : Black G S u → G.Adj u w →
      (∀ x : V, G.Adj u x → x ≠ w → Black G S x) → Black G S w

/-- `S` is a zero forcing set when `cl(S) = V`. -/
def IsZeroForcing {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop := ∀ v : V, Black G S v

/-- `Z(G)`, the minimum size of a zero forcing set. -/
noncomputable def zeroForcingNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset V, S.card = k ∧ IsZeroForcing G (S : Set V)}

/-- Conjecture 5. -/
def claim : Prop := ∀ n : ℕ, 13 ≤ n → zeroForcingNumber (gp n 3) = 8

/-- Adding initially black vertices preserves every forcing derivation. -/
theorem Black.mono {V : Type*} {G : SimpleGraph V} {S T : Set V} {v : V}
    (hST : S ⊆ T) (h : Black G S v) : Black G T v := by
  induction h with
  | init hv => exact .init (hST hv)
  | force hu huw hall ihu ihall =>
      exact .force ihu huw fun x hux hxw => ihall x hux hxw

/-- A non-initial black derivation contains a force whose source and other neighbours are initial. -/
theorem Black.exists_initial_force {V : Type*} {G : SimpleGraph V} {S : Set V} {v : V}
    (h : Black G S v) (hv : v ∉ S) :
    ∃ u w : V, u ∈ S ∧ w ∉ S ∧ G.Adj u w ∧
      ∀ x : V, G.Adj u x → x ≠ w → x ∈ S := by
  induction h with
  | init hvS => exact (hv hvS).elim
  | @force u w hu huw hall ihu ihall =>
      by_cases huS : u ∈ S
      · by_cases hrest : ∀ x : V, G.Adj u x → x ≠ w → x ∈ S
        · exact ⟨u, w, huS, hv, huw, hrest⟩
        · push Not at hrest
          obtain ⟨x, hux, hxw, hxS⟩ := hrest
          exact ihall x hux hxw hxS
      · exact ihu huS

/-- A graph automorphism transports an entire forcing derivation. -/
theorem Black.image_equiv {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (e : V ≃ V) (hadj : ∀ x y, G.Adj (e x) (e y) ↔ G.Adj x y)
    (S : Finset V) {v : V} (h : Black G (S : Set V) v) :
    Black G ((S.image e : Finset V) : Set V) (e v) := by
  induction h with
  | init hv =>
      exact .init (Finset.mem_image.mpr ⟨_, hv, rfl⟩)
  | @force u w hu huw hall ihu ihall =>
      apply Black.force ihu ((hadj u w).2 huw)
      intro x hux hxw
      let y := e.symm x
      have hey : e y = x := e.apply_symm_apply x
      have huy : G.Adj u y := (hadj u y).1 (by simpa [hey] using hux)
      have hyw : y ≠ w := by
        intro hyw
        apply hxw
        rw [← hey, hyw]
      simpa [hey] using ihall y huy hyw

/-- A forcing process starting outside a disjoint fort can never enter that fort. -/
theorem IsFort.not_black_of_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S F : Finset V)
    (hF : IsFort G F) (hSF : Disjoint S F) {v : V} (hvF : v ∈ F) :
    ¬ Black G (S : Set V) v := by
  intro hv
  induction hv with
  | init hvS => exact (Finset.disjoint_left.mp hSF) hvS hvF
  | @force u w hu huw hall ihu ihall =>
      by_cases huF : u ∈ F
      · exact ihu huF
      · apply hF.2 u huF
        have heq : finiteNeighbors G u ∩ F = {w} := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_singleton]
          constructor
          · intro hx
            by_contra hxw
            exact ihall x (by simpa [finiteNeighbors] using hx.1) hxw hx.2
          · rintro rfl
            exact ⟨by simp [finiteNeighbors, huw], hvF⟩
        rw [heq]
        simp

/-- Substitute derivations of every initial vertex into a forcing derivation. -/
theorem Black.bind {V : Type*} {G : SimpleGraph V} {S T : Set V} {v : V}
    (hT : ∀ x ∈ T, Black G S x) (h : Black G T v) : Black G S v := by
  induction h with
  | init hv => exact hT _ hv
  | force hu huw hall ihu ihall =>
      exact .force ihu huw fun x hux hxw => ihall x hux hxw

private def outer (n : Nat) [NeZero n] (i : Nat) : Bool × Fin n :=
  (false, Fin.ofNat n i)

private def inner (n : Nat) [NeZero n] (i : Nat) : Bool × Fin n :=
  (true, Fin.ofNat n i)

private def outerBlock8 (n : Nat) [NeZero n] : Finset (Bool × Fin n) :=
  Finset.univ.filter fun x => x.1 = false ∧ x.2.val < 8

private def shift (n : Nat) [NeZero n] (q : Nat) (v : Bool × Fin n) :
    Bool × Fin n :=
  (v.1, v.2 + Fin.ofNat n q)

/-- Simultaneous cyclic translation in both layers is a graph automorphism. -/
private theorem shift_adj (n q : Nat) [NeZero n] (v w : Bool × Fin n) :
    (gp n 3).Adj (shift n q v) (shift n q w) ↔ (gp n 3).Adj v w := by
  have hinj : Function.Injective (shift n q) := by
    rintro ⟨b, i⟩ ⟨c, j⟩ h
    simp only [shift, Prod.mk.injEq] at h
    exact Prod.ext h.1 (add_right_cancel h.2)
  have hshift (x y k : Fin n) :
      x + Fin.ofNat n q = (y + Fin.ofNat n q) + k ↔ x = y + k := by
    constructor <;> intro h
    · apply add_right_cancel (b := Fin.ofNat n q)
      simpa [add_assoc, add_comm, add_left_comm] using h
    · simpa [h, add_assoc, add_comm, add_left_comm]
  have heq (x y : Fin n) :
      x + Fin.ofNat n q = y + Fin.ofNat n q ↔ x = y := by
    constructor
    · exact add_right_cancel
    · intro h
      rw [h]
  have hadjShift (a b : Bool × Fin n) :
      (gp n 3).Adj a b ↔ a ≠ b ∧
        ((a.1 = false ∧ b.1 = false ∧ b.2 = a.2 + Fin.ofNat n 1) ∨
         (a.1 = true ∧ b.1 = true ∧ b.2 = a.2 + Fin.ofNat n 3) ∨
         (a.1 = false ∧ b.1 = true ∧ a.2 = b.2) ∨
         (b.1 = false ∧ a.1 = false ∧ a.2 = b.2 + Fin.ofNat n 1) ∨
         (b.1 = true ∧ a.1 = true ∧ a.2 = b.2 + Fin.ofNat n 3) ∨
         (b.1 = false ∧ a.1 = true ∧ b.2 = a.2)) := by
    simp only [gp, SimpleGraph.fromRel_adj]
    rw [and_congr_right_iff]
    intro _
    simp only [Fin.ext_iff, Fin.val_add, Fin.val_ofNat]
    simp only [Nat.add_mod_mod]
    tauto
  rw [hadjShift, hadjShift]
  simp only [shift, Prod.fst, Prod.snd]
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨fun hvw => hne (congrArg (shift n q) hvw), ?_⟩
    simpa only [hshift, heq] using h
  · rintro ⟨hne, h⟩
    refine ⟨fun hvw => hne (hinj hvw), ?_⟩
    simpa only [hshift, heq] using h

private theorem outer_other_neighbor_mem (n : Nat) [NeZero n] (hn : 9 ≤ n)
    (i : Nat) (hi1 : 1 ≤ i) (hi6 : i ≤ 6) (x : Bool × Fin n)
    (hx : (gp n 3).Adj (outer n i) x) (hne : x ≠ inner n i) :
    x ∈ outerBlock8 n := by
  have hiN : i < n := by omega
  have hiSucc : i + 1 < n := by omega
  rcases x with ⟨b, j⟩
  cases b
  · simp only [outerBlock8, Finset.mem_filter, Finset.mem_univ, true_and]
    change j.val < 8
    simp only [outer, gp, SimpleGraph.fromRel_adj, Prod.fst, Prod.snd,
      Bool.false_eq_true, false_and, false_or, true_and] at hx
    simp [Fin.val_ofNat, Nat.mod_eq_of_lt hiN, Nat.mod_eq_of_lt hiSucc] at hx
    rcases hx with ⟨_, hx | hx⟩
    · omega
    · by_cases hj : j.val + 1 < n
      · rw [Nat.mod_eq_of_lt hj] at hx
        omega
      · have hj_eq : j.val + 1 = n := by omega
        rw [hj_eq, Nat.mod_self] at hx
        omega
  · exfalso
    apply hne
    simp only [outer, gp, SimpleGraph.fromRel_adj, Prod.fst, Prod.snd,
      Bool.false_eq_true, false_and, false_or, true_and] at hx
    simp [Fin.val_ofNat, Nat.mod_eq_of_lt hiN, Nat.mod_eq_of_lt hiSucc] at hx
    simpa [inner] using congrArg (fun q : Fin n => (true, q)) hx.symm

/-- From the initial outer block, each of the six middle spokes can be forced. -/
private theorem block_forces_inner (n : Nat) [NeZero n] (hn : 9 ≤ n)
    (i : Nat) (hi1 : 1 ≤ i) (hi6 : i ≤ 6) :
    Black (gp n 3) (outerBlock8 n : Set (Bool × Fin n)) (inner n i) := by
  have hiN : i < n := by omega
  have hmem : outer n i ∈ outerBlock8 n := by
    simp [outerBlock8, outer, Fin.val_ofNat, Nat.mod_eq_of_lt hiN]
    omega
  apply Black.force (.init hmem)
  · unfold gp
    rw [SimpleGraph.fromRel_adj]
    constructor
    · intro h
      have := congrArg Prod.fst h
      simp [outer, inner] at this
    · exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  · intro x hx hne
    exact .init (outer_other_neighbor_mem n hn i hi1 hi6 x hx hne)

private theorem inner4_other_neighbor (n : Nat) [NeZero n] (hn : 9 ≤ n)
    (x : Bool × Fin n) (hx : (gp n 3).Adj (inner n 4) x)
    (hne : x ≠ inner n 7) : x = inner n 1 ∨ x = outer n 4 := by
  rcases x with ⟨b, j⟩
  cases b
  · right
    simp only [inner, gp, SimpleGraph.fromRel_adj, Prod.fst, Prod.snd,
      Bool.true_eq_false, false_and, false_or, true_and] at hx
    have h4n : 4 < n := by omega
    simp [Fin.val_ofNat, Nat.mod_eq_of_lt h4n] at hx
    simpa [outer] using congrArg (fun q : Fin n => (false, q)) hx
  · left
    simp only [inner, gp, SimpleGraph.fromRel_adj, Prod.fst, Prod.snd,
      Bool.true_eq_false, false_and, false_or, true_and] at hx
    have h4n : 4 < n := by omega
    have h7n : 7 < n := by omega
    simp [Fin.val_ofNat, Nat.mod_eq_of_lt h4n, Nat.mod_eq_of_lt h7n] at hx
    rcases hx with ⟨_, hx | hx⟩
    · exfalso
      apply hne
      have hj7 : j = Fin.ofNat n 7 := Fin.ext (by
        simpa [Fin.val_ofNat, Nat.mod_eq_of_lt h7n] using hx)
      simpa [inner] using congrArg (fun q : Fin n => (true, q)) hj7
    · by_cases hj : j.val + 3 < n
      · rw [Nat.mod_eq_of_lt hj] at hx
        have hj1 : j.val = 1 := by omega
        have hjfin : j = Fin.ofNat n 1 := Fin.ext (by
          simp [Fin.val_ofNat, Nat.mod_eq_of_lt (show 1 < n by omega), hj1])
        simpa [inner] using congrArg (fun q : Fin n => (true, q)) hjfin
      · have hlarge : n ≤ j.val + 3 := by omega
        rw [Nat.mod_eq_sub_mod hlarge,
          Nat.mod_eq_of_lt (by omega : j.val + 3 - n < n)] at hx
        omega

private theorem block_forces_inner7 (n : Nat) [NeZero n] (hn : 9 ≤ n) :
    Black (gp n 3) (outerBlock8 n : Set (Bool × Fin n)) (inner n 7) := by
  apply Black.force (block_forces_inner n hn 4 (by omega) (by omega))
  · unfold gp
    rw [SimpleGraph.fromRel_adj]
    constructor
    · intro h
      have := congrArg (fun x => x.2.val) h
      simp [inner, Fin.val_ofNat, Nat.mod_eq_of_lt (show 4 < n by omega),
        Nat.mod_eq_of_lt (show 7 < n by omega)] at this
    · exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl, by
        norm_num [inner, Fin.val_ofNat,
          Nat.mod_eq_of_lt (show 4 < n by omega),
          Nat.mod_eq_of_lt (show 7 < n by omega)]⟩))
  · intro x hx hne
    rcases inner4_other_neighbor n hn x hx hne with h | h
    · rw [h]
      exact block_forces_inner n hn 1 (by omega) (by omega)
    · rw [h]
      exact .init (by
        simp [outerBlock8, outer, Fin.val_ofNat,
          Nat.mod_eq_of_lt (show 4 < n by omega)])

private theorem outer7_other_neighbor (n : Nat) [NeZero n] (hn : 9 ≤ n)
    (x : Bool × Fin n) (hx : (gp n 3).Adj (outer n 7) x)
    (hne : x ≠ outer n 8) : x = outer n 6 ∨ x = inner n 7 := by
  rcases x with ⟨b, j⟩
  cases b
  · left
    simp only [outer, gp, SimpleGraph.fromRel_adj, Prod.fst, Prod.snd,
      Bool.false_eq_true, false_and, false_or, true_and] at hx
    have h7n : 7 < n := by omega
    have h8n : 8 < n := by omega
    simp [Fin.val_ofNat, Nat.mod_eq_of_lt h7n, Nat.mod_eq_of_lt h8n] at hx
    rcases hx with ⟨_, hx | hx⟩
    · exfalso
      apply hne
      have hj8 : j = Fin.ofNat n 8 := Fin.ext (by
        simpa [Fin.val_ofNat, Nat.mod_eq_of_lt h8n] using hx)
      simpa [outer] using congrArg (fun q : Fin n => (false, q)) hj8
    · by_cases hj : j.val + 1 < n
      · rw [Nat.mod_eq_of_lt hj] at hx
        have hj6 : j.val = 6 := by omega
        have hjfin : j = Fin.ofNat n 6 := Fin.ext (by
          simp [Fin.val_ofNat, Nat.mod_eq_of_lt (show 6 < n by omega), hj6])
        simpa [outer] using congrArg (fun q : Fin n => (false, q)) hjfin
      · have hj_eq : j.val + 1 = n := by omega
        rw [hj_eq, Nat.mod_self] at hx
        omega
  · right
    simp only [outer, gp, SimpleGraph.fromRel_adj, Prod.fst, Prod.snd,
      Bool.false_eq_true, false_and, false_or, true_and] at hx
    have h7n : 7 < n := by omega
    simp [Fin.val_ofNat, Nat.mod_eq_of_lt h7n] at hx
    simpa [inner] using congrArg (fun q : Fin n => (true, q)) hx.symm

/-- Proposition 4's first cascade forces the next outer vertex. -/
private theorem block_forces_outer8 (n : Nat) [NeZero n] (hn : 9 ≤ n) :
    Black (gp n 3) (outerBlock8 n : Set (Bool × Fin n)) (outer n 8) := by
  have hmem : outer n 7 ∈ outerBlock8 n := by
    simp [outerBlock8, outer, Fin.val_ofNat,
      Nat.mod_eq_of_lt (show 7 < n by omega)]
  apply Black.force (.init hmem)
  · unfold gp
    rw [SimpleGraph.fromRel_adj]
    constructor
    · intro h
      have := congrArg (fun x => x.2.val) h
      simp [outer, Fin.val_ofNat, Nat.mod_eq_of_lt (show 7 < n by omega),
        Nat.mod_eq_of_lt (show 8 < n by omega)] at this
    · exact Or.inl (Or.inl ⟨rfl, rfl, by
        norm_num [outer, Fin.val_ofNat,
          Nat.mod_eq_of_lt (show 7 < n by omega),
          Nat.mod_eq_of_lt (show 8 < n by omega)]⟩)
  · intro x hx hne
    rcases outer7_other_neighbor n hn x hx hne with h | h
    · rw [h]
      exact .init (by
        simp [outerBlock8, outer, Fin.val_ofNat,
          Nat.mod_eq_of_lt (show 6 < n by omega)])
    · rw [h]
      exact block_forces_inner7 n hn

/-- Repeating the translated cascade colors every outer vertex. -/
private theorem block_forces_all_outer (n : Nat) [NeZero n] (hn : 9 ≤ n)
    (i : Nat) :
    Black (gp n 3) (outerBlock8 n : Set (Bool × Fin n)) (outer n i) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      by_cases hi : i < 8
      · exact .init (by
          have hin : i < n := by omega
          simp [outerBlock8, outer, Fin.val_ofNat, Nat.mod_eq_of_lt hin, hi])
      · let q := i - 8
        have hinj : Function.Injective (shift n q) := by
          rintro ⟨b, j⟩ ⟨c, k⟩ h
          simp only [shift, Prod.mk.injEq] at h
          exact Prod.ext h.1 (add_right_cancel h.2)
        let e : (Bool × Fin n) ≃ (Bool × Fin n) :=
          Equiv.ofBijective (shift n q) ⟨hinj, Finite.surjective_of_injective hinj⟩
        have houter (j : Nat) : shift n q (outer n j) = outer n (q + j) := by
          apply Prod.ext
          · rfl
          · apply Fin.ext
            simp [shift, outer, Fin.val_add, Fin.val_ofNat, Nat.add_mod,
              Nat.add_comm]
        have htranslated :
            Black (gp n 3)
              (((outerBlock8 n).image e : Finset (Bool × Fin n)) :
                Set (Bool × Fin n))
              (e (outer n 8)) := by
          exact Black.image_equiv e (fun v w => shift_adj n q v w)
            (outerBlock8 n) (block_forces_outer8 n hn)
        have hbound : ∀ x ∈ ((outerBlock8 n).image e : Finset (Bool × Fin n)),
            Black (gp n 3) (outerBlock8 n : Set (Bool × Fin n)) x := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          have hyc : y.1 = false ∧ y.2.val < 8 := by
            simpa [outerBlock8] using hy
          have hyeq : y = outer n y.2.val := by
            rcases y with ⟨b, j⟩
            cases b
            · simp [outer, Fin.ext_iff, Fin.val_ofNat,
                Nat.mod_eq_of_lt j.isLt]
            · simp at hyc
          rw [hyeq]
          rw [show e (outer n y.2.val) = outer n (q + y.2.val) by
            change shift n q (outer n y.2.val) = outer n (q + y.2.val)
            exact houter y.2.val]
          apply ih (q + y.2.val)
          omega
        have hresult := Black.bind hbound htranslated
        have hqi : q + 8 = i := by simp [q]; omega
        change Black (gp n 3) (outerBlock8 n : Set (Bool × Fin n))
          (shift n q (outer n 8)) at hresult
        rw [houter, hqi] at hresult
        exact hresult

private theorem all_outer_force_inner (n : Nat) [NeZero n]
    (S : Set (Bool × Fin n))
    (hall : ∀ i : Nat, Black (gp n 3) S (outer n i))
    (i : Nat) : Black (gp n 3) S (inner n i) := by
  apply Black.force (hall i)
  · unfold gp
    rw [SimpleGraph.fromRel_adj]
    constructor
    · intro h
      have := congrArg Prod.fst h
      simp [outer, inner] at this
    · exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  · intro x hx hne
    rcases x with ⟨b, j⟩
    cases b
    · have heq : (false, j) = outer n j.val := by
        simp [outer, Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt j.isLt]
      rw [heq]
      exact hall j.val
    · exfalso
      apply hne
      simp only [outer, gp, SimpleGraph.fromRel_adj, Prod.fst, Prod.snd,
        Bool.false_eq_true, false_and, false_or, true_and] at hx
      have hij : Fin.ofNat n i = j := by simpa [outer] using hx
      simpa [inner] using congrArg (fun q : Fin n => (true, q)) hij.symm

/-- Eight consecutive outer vertices zero-force `P(n,3)` for every `n ≥ 9`. -/
theorem outerBlock8_zeroForcing (n : Nat) [NeZero n] (hn : 9 ≤ n) :
    IsZeroForcing (gp n 3) (outerBlock8 n : Set (Bool × Fin n)) := by
  intro v
  rcases v with ⟨b, i⟩
  cases b
  · have heq : (false, i) = outer n i.val := by
      simp [outer, Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt i.isLt]
    rw [heq]
    exact block_forces_all_outer n hn i.val
  · have heq : (true, i) = inner n i.val := by
      simp [inner, Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt i.isLt]
    rw [heq]
    exact all_outer_force_inner n (outerBlock8 n : Set (Bool × Fin n))
      (block_forces_all_outer n hn) i.val

def externalBoundary {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : Finset V :=
  Finset.univ.filter fun v => v ∉ X ∧ ∃ u ∈ X, G.Adj u v

/-- The first `p` distinct forcing sources have external boundary no larger than the initial set. -/
theorem firstForcers_boundary {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hzero : IsZeroForcing G (S : Set V)) (p : Nat)
    (hsize : S.card + p ≤ Fintype.card V) :
    ∃ X : Finset V, X.card = p ∧ (externalBoundary G X).card ≤ S.card := by
  classical
  have aux : ∀ q : Nat, S.card + q ≤ Fintype.card V →
      ∃ B X : Finset V,
        S ⊆ B ∧ X ⊆ B ∧ B.card = S.card + q ∧ X.card = q ∧
          ∀ u ∈ X, ∀ v, G.Adj u v → v ∈ B := by
    intro q
    induction q with
    | zero =>
        intro _
        exact ⟨S, ∅, Finset.Subset.rfl, Finset.empty_subset _, by simp⟩
    | succ q ih =>
        intro hq
        obtain ⟨B, X, hSB, hXB, hBcard, hXcard, hclosed⟩ := ih (by omega)
        have hBlt : B.card < Fintype.card V := by omega
        have houtside : ∃ w : V, w ∉ B := by
          by_contra h
          push Not at h
          have hBuniv : B = Finset.univ := Finset.eq_univ_of_forall h
          rw [hBuniv, Finset.card_univ] at hBlt
          omega
        obtain ⟨w, hwB⟩ := houtside
        have hblackB : Black G (B : Set V) w :=
          Black.mono (fun _ hv => hSB hv) (hzero w)
        obtain ⟨u, t, huB, htB, hut, hrest⟩ :=
          hblackB.exists_initial_force hwB
        have huX : u ∉ X := by
          intro huX
          exact htB (hclosed u huX t hut)
        refine ⟨insert t B, insert u X, ?_, ?_, ?_, ?_, ?_⟩
        · exact fun _ hv => Finset.mem_insert_of_mem (hSB hv)
        · intro x hx
          simp only [Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inr huB
          · exact Or.inr (hXB hx)
        · simp [Finset.card_insert_of_notMem htB, hBcard, Nat.add_assoc]
        · simp [Finset.card_insert_of_notMem huX, hXcard]
        · intro x hx v hxv
          simp only [Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · by_cases hvt : v = t
            · exact Or.inl hvt
            · exact Or.inr (hrest v hxv hvt)
          · exact Or.inr (hclosed x hx v hxv)
  obtain ⟨B, X, _, hXB, hBcard, hXcard, hclosed⟩ := aux p hsize
  refine ⟨X, hXcard, ?_⟩
  have hsub : externalBoundary G X ⊆ B \ X := by
    intro v hv
    rw [Finset.mem_sdiff]
    simp only [externalBoundary, Finset.mem_filter, Finset.mem_univ,
      true_and] at hv
    exact ⟨by
      obtain ⟨u, huX, huv⟩ := hv.2
      exact hclosed u huX v huv, hv.1⟩
  calc
    (externalBoundary G X).card ≤ (B \ X).card := Finset.card_le_card hsub
    _ = B.card - X.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hXB]
    _ = S.card := by omega

/-- The six anchored fort families rule out every seven-vertex zero-forcing set in `P(13,3)`. -/
private theorem no_seven_zeroForcing13_of_certificates
    (hcert : ∀ (a : Anchor13) (m : Nat), candidateShapeOK a m = true →
      ∃ f : Nat, IsFort (gp 13 3) (maskSet13 f) ∧
        Disjoint (maskSet13 m) (maskSet13 f))
    (S : Finset V13) (hcard : S.card = 7) :
    ¬ IsZeroForcing (gp 13 3) (S : Set V13) := by
  classical
  intro hzero
  have houtside : ∃ w : V13, w ∉ S := by
    by_contra h
    push Not at h
    have hSuniv : S = Finset.univ := Finset.eq_univ_of_forall h
    have hfull : S.card = 26 := by rw [hSuniv]; decide
    omega
  obtain ⟨w, hwS⟩ := houtside
  obtain ⟨u, t, huS, htS, hut, hrest⟩ := (hzero w).exists_initial_force hwS
  obtain ⟨a, hatarget, harequired⟩ := initialForce_anchor13 u t hut
  have hrot : Function.Bijective (rotate13 u.2) := by
    constructor
    · rintro ⟨b, i⟩ ⟨c, j⟩ h
      simp [rotate13] at h
      exact Prod.ext h.1 (by simpa using congrArg (fun x => x + u.2) h.2)
    · rintro ⟨b, i⟩
      exact ⟨(b, i + u.2), by simp [rotate13]⟩
  let R := rotateFinset13 u.2 S
  let m := setMask13 R
  have hmask : maskSet13 (setMask13 R) = R := by
    ext v
    simp [maskSet13, testBit_setMask13]
  have hshape : candidateShapeOK a m = true := by
    rw [candidateShapeOK]
    apply decide_eq_true
    refine ⟨setMask13_lt_two_pow R, ?_, ?_, ?_⟩
    · rw [bitCount26_eq_card_maskSet13, hmask]
      change (S.image (rotate13 u.2)).card = 7
      rw [Finset.card_image_of_injective _ hrot.injective, hcard]
    · intro v hv
      rw [harequired] at hv
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase] at hv
      apply testBit_setMask13 R v |>.2
      rcases hv with rfl | ⟨x, ⟨hxt, hux⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨u, huS, rfl⟩
      · exact Finset.mem_image.mpr ⟨x, hrest x
          (neighbors13_spec u x |>.1 hux) hxt, rfl⟩
    · rw [hatarget]
      intro hbit
      have hmem : rotate13 u.2 t ∈ R := testBit_setMask13 R _ |>.1 hbit
      obtain ⟨x, hxS, hxt⟩ := Finset.mem_image.mp hmem
      have hxt' : x = t := hrot.injective hxt
      exact htS (hxt' ▸ hxS)
  obtain ⟨f, hfort, hdisjoint⟩ := hcert a m hshape
  have hdisjoint' : Disjoint R (maskSet13 f) := by
    simpa [m, hmask] using hdisjoint
  let e : V13 ≃ V13 := Equiv.ofBijective (rotate13 u.2) hrot
  have headj (x y : V13) : (gp 13 3).Adj (e x) (e y) ↔ (gp 13 3).Adj x y := by
    exact rotate13_adj u.2 x y
  have hRzero : IsZeroForcing (gp 13 3) (R : Set V13) := by
    intro x
    obtain ⟨v, rfl⟩ := e.surjective x
    simpa [R, rotateFinset13, e] using
      (Black.image_equiv e headj S (hzero v))
  obtain ⟨z, hz⟩ := hfort.1
  exact IsFort.not_black_of_disjoint (gp 13 3) R (maskSet13 f)
    hfort hdisjoint' hz (hRzero z)

/-- No set of at most seven vertices zero-forces `P(13,3)`. -/
private theorem no_small_zeroForcing13 (S : Finset (Bool × Fin 13))
    (hcard : S.card ≤ 7) :
    ¬ IsZeroForcing (gp 13 3) (S : Set (Bool × Fin 13)) := by
  intro hzero
  obtain ⟨T, hST, hTcard⟩ := Finset.exists_superset_card_eq hcard
    (by decide : 7 ≤ Fintype.card (Bool × Fin 13))
  have hTzero : IsZeroForcing (gp 13 3) (T : Set (Bool × Fin 13)) := by
    intro v
    exact Black.mono (fun _ hv => hST hv) (hzero v)
  exact no_seven_zeroForcing13_of_certificates
    anchoredMask_has_disjoint_fort T hTcard hTzero

/-- The fort certificate and the explicit outer block give the exact value at `n = 13`. -/
theorem zeroForcingNumber13 : zeroForcingNumber (gp 13 3) = 8 := by
  have hblock : (outerBlock8 13).card = 8 := by decide
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨outerBlock8 13, hblock,
      outerBlock8_zeroForcing 13 (by omega)⟩
  · have hnonempty :
        {k : ℕ | ∃ S : Finset (Bool × Fin 13), S.card = k ∧
          IsZeroForcing (gp 13 3) (S : Set (Bool × Fin 13))}.Nonempty := by
      exact ⟨8, outerBlock8 13, hblock,
        outerBlock8_zeroForcing 13 (by omega)⟩
    change 8 ≤ sInf {k : ℕ | ∃ S : Finset (Bool × Fin 13),
      S.card = k ∧ IsZeroForcing (gp 13 3) (S : Set (Bool × Fin 13))}
    obtain ⟨S, hcard, hzero⟩ := Nat.sInf_mem hnonempty
    by_contra hlt
    have hsmall : S.card ≤ 7 := by omega
    exact no_small_zeroForcing13 S hsmall hzero

/-- Krishnan's Conjecture 5. -/
theorem result : claim := by
  intro n hn
  by_cases h13 : n = 13
  · subst n
    exact zeroForcingNumber13
  have hn14 : 14 ≤ n := by omega
  letI : NeZero n := ⟨by omega⟩
  have hblock : (outerBlock8 n).card = 8 := by
    let f : Fin 8 → Bool × Fin n := fun i => outer n i.val
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      have hn8 : 8 < n := by omega
      have hi : i.val < n := lt_trans i.isLt hn8
      have hj : j.val < n := lt_trans j.isLt hn8
      have := congrArg (fun x => x.2.val) hij
      simpa [f, outer, Fin.val_ofNat, Nat.mod_eq_of_lt hi,
        Nat.mod_eq_of_lt hj] using this
    have heq : outerBlock8 n = Finset.univ.image f := by
      ext x
      simp only [outerBlock8, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hx
        let i : Fin 8 := ⟨x.2.val, hx.2⟩
        refine ⟨i, ?_⟩
        have hxn : x.2.val < n := x.2.isLt
        apply Prod.ext hx.1.symm
        apply Fin.ext
        simp [f, outer, i, Fin.val_ofNat, Nat.mod_eq_of_lt hxn]
      · rintro ⟨i, rfl⟩
        have hn8 : 8 < n := by omega
        have hi : i.val < n := lt_trans i.isLt hn8
        simp [f, outer, Fin.val_ofNat, Nat.mod_eq_of_lt hi, i.isLt]
    rw [heq, Finset.card_image_of_injective _ hf]
    simp
  have hnosmall (S : Finset (Bool × Fin n)) (hcard : S.card ≤ 7) :
      ¬ IsZeroForcing (gp n 3) (S : Set (Bool × Fin n)) := by
    intro hzero
    have hsize : S.card + 10 ≤ Fintype.card (Bool × Fin n) := by
      simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
      omega
    obtain ⟨X, hX, hbound⟩ :=
      firstForcers_boundary (gp n 3) S hzero 10 hsize
    have hboundary :=
      D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeTenBoundary.p3_ten_boundary
        n hn14 X hX
    have heq : externalBoundary (gp n 3) X =
        D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary.externalBoundary
          n X := rfl
    rw [heq] at hbound
    omega
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨outerBlock8 n, hblock,
      outerBlock8_zeroForcing n (by omega)⟩
  · have hnonempty :
        {k : ℕ | ∃ S : Finset (Bool × Fin n), S.card = k ∧
          IsZeroForcing (gp n 3) (S : Set (Bool × Fin n))}.Nonempty := by
      exact ⟨8, outerBlock8 n, hblock,
        outerBlock8_zeroForcing n (by omega)⟩
    change 8 ≤ sInf {k : ℕ | ∃ S : Finset (Bool × Fin n),
      S.card = k ∧ IsZeroForcing (gp n 3) (S : Set (Bool × Fin n))}
    obtain ⟨S, hcard, hzero⟩ := Nat.sInf_mem hnonempty
    by_contra hlt
    exact hnosmall S (by omega) hzero

#print axioms result

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
