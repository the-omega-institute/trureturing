/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9K4TwelveSingletons
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9K4TwelveSingletons
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Twelve singleton cuts are excluded at order 72 with eight zero-cut even vertices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4ZeroCutArithmetic

/-! Edge counting for the twelve-singleton branch of the K4 projection. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4TwelveSingletons

open Finset
open scoped BigOperators
open Q5SmallParitySupport (bitParity neighborParity)

private instance : Fintype (BitVec 5) :=
  Fintype.ofEquiv (Fin (2 ^ 5)) (BitVec.equivFin (m := 5)).toEquiv.symm

private def toggle (x : BitVec 5) (d : Fin 5) : BitVec 5 :=
  x ^^^ BitVec.twoPow 5 d.val

/-- The two endpoints of each selected edge are both counted. -/
def inducedDegreeSum (S : Finset (BitVec 5)) : ℕ :=
  ∑ d : Fin 5, ∑ x : BitVec 5, if x ∈ S ∧ toggle x d ∈ S then 1 else 0

private def parityWord (p : Bool) (i : Fin 16) : BitVec 5 :=
  BitVec.cons (p ^^ bitParity ((BitVec.ofFin (w := 4) i).setWidth 5)) (BitVec.ofFin i)

private def parityEquiv : Bool × Fin 16 ≃ BitVec 5 where
  toFun x := parityWord x.1 x.2
  invFun x := (bitParity x, (x.setWidth 4).toFin)
  left_inv := by decide +kernel
  right_inv x := (show ∀ i : Fin 32, parityWord (bitParity (BitVec.ofFin i))
    (((BitVec.ofFin (w := 5) i).setWidth 4).toFin) = BitVec.ofFin i by decide +kernel) x.toFin

private def toggleIndex (i : Fin 16) (d : Fin 5) : Fin 16 :=
  ((BitVec.ofFin (w := 4) i) ^^^ BitVec.twoPow 4 d.val).toFin

private theorem toggle_parityWord : ∀ p i d,
    toggle (parityWord p i) d = parityWord (!p) (toggleIndex i d) := by
  decide +kernel

private def parityMask (S : Finset (BitVec 5)) (p : Bool) : BitVec 16 :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 16 => decide (parityWord p i ∈ S))).cast
    List.length_ofFn

private theorem parityMask_bit (S : Finset (BitVec 5)) (p : Bool) (i : Fin 16) :
    (parityMask S p).getLsbD i.val = decide (parityWord p i ∈ S) := by
  have hi : i.val < (List.ofFn fun j : Fin 16 => decide (parityWord p j ∈ S)).length := by
    simpa only [List.length_ofFn] using i.isLt
  simp only [parityMask, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_ofFn]

private def swapBits (m mask : BitVec 16) (n : ℕ) : BitVec 16 :=
  ((m &&& mask) <<< n) ||| ((m >>> n) &&& mask)

private def shuffle (m : BitVec 16) (d : Fin 5) : BitVec 16 :=
  if d = 0 then swapBits m 0x5555 1
  else if d = 1 then swapBits m 0x3333 2
  else if d = 2 then swapBits m 0x0f0f 4
  else if d = 3 then swapBits m 0x00ff 8
  else m

private theorem shuffle_bit (m : BitVec 16) (d : Fin 5) (i : Fin 16) :
    (shuffle m d).getLsbD i.val = m.getLsbD (toggleIndex i d).val := by
  fin_cases d <;> fin_cases i <;>
    simp [shuffle, swapBits, toggleIndex] <;> rfl

private def oppositeMask (m : BitVec 16) : BitVec 16 :=
  shuffle m 0 ^^^ shuffle m 1 ^^^ shuffle m 2 ^^^ shuffle m 3 ^^^ shuffle m 4

private theorem oppositeMask_eq (S : Finset (BitVec 5))
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) :
    parityMask S true = oppositeMask (parityMask S false) := by
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  let i : Fin 16 := ⟨n, hn⟩
  change (parityMask S true).getLsbD i.val = (oppositeMask (parityMask S false)).getLsbD i.val
  simp only [oppositeMask, BitVec.getLsbD_xor, shuffle_bit, parityMask_bit]
  rw [hpar (parityWord true i)]
  change (decide (toggle (parityWord true i) 0 ∈ S) ^^
    decide (toggle (parityWord true i) 1 ∈ S) ^^
    decide (toggle (parityWord true i) 2 ∈ S) ^^
    decide (toggle (parityWord true i) 3 ∈ S) ^^
    decide (toggle (parityWord true i) 4 ∈ S)) = _
  simp only [toggle_parityWord, Bool.not_true]

private theorem cpop_sum (m : BitVec 16) :
    m.cpop.toNat = ∑ i : Fin 16, (m.getLsbD i.val).toNat := by
  rw [BitVec.toNat_cpop]
  have h (n : ℕ) : m.cpopNatRec n 0 = ∑ i : Fin n, (m.getLsbD i.val).toNat := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_add, ih,
        Fin.sum_univ_castSucc]
      simp [Nat.add_comm]
  exact h 16

private def edgeBound (m : BitVec 16) : Prop :=
  m.cpop + (oppositeMask m).cpop = 12 →
  let o := oppositeMask m
  (o &&& shuffle m 0).cpop + (o &&& shuffle m 1).cpop +
    (o &&& shuffle m 2).cpop + (o &&& shuffle m 3).cpop + (o &&& shuffle m 4).cpop ≤ 16

private instance (m : BitVec 16) : Decidable (edgeBound m) := by
  unfold edgeBound
  infer_instance

-- Check all sixteen-bit masks, in blocks indexed by their highest four bits.
set_option maxHeartbeats 30000000 in
set_option maxRecDepth 4096 in
private theorem certificate_table (a : Fin 16) :
    ∀ b c d : Fin 16, edgeBound (BitVec.ofNat 16 (4096 * a.val + 256 * b.val + 16 * c.val + d.val)) := by
  fin_cases a <;> decide +kernel

private theorem certificate (m : BitVec 16) : edgeBound m := by
  let a : Fin 16 := ⟨m.toNat / 4096, by have := m.isLt; omega⟩
  let b : Fin 16 := ⟨m.toNat % 4096 / 256, by omega⟩
  let c : Fin 16 := ⟨m.toNat % 4096 % 256 / 16, by omega⟩
  let d : Fin 16 := ⟨m.toNat % 4096 % 256 % 16, by omega⟩
  have h : 4096 * a.val + 256 * b.val + 16 * c.val + d.val = m.toNat := by
    dsimp [a, b, c, d]
    omega
  simpa only [h, BitVec.ofNat_toNat, BitVec.setWidth_eq] using certificate_table a b c d

set_option maxHeartbeats 3000000 in
private theorem directed_sum (S : Finset (BitVec 5)) (d : Fin 5) :
    (∑ x : BitVec 5, if x ∈ S ∧ toggle x d ∈ S then (1 : ℕ) else 0) =
      2 * ((parityMask S true) &&& shuffle (parityMask S false) d).cpop.toNat := by
  let f (p : Bool) (i : Fin 16) : ℕ :=
    if parityWord p i ∈ S ∧ parityWord (!p) (toggleIndex i d) ∈ S then 1 else 0
  have ht : Function.Involutive (fun i => toggleIndex i d) := by
    exact (show ∀ (d : Fin 5) (i : Fin 16), toggleIndex (toggleIndex i d) d = i by
      decide +kernel) d
  rw [← Fintype.sum_equiv parityEquiv
    (fun x : Bool × Fin 16 => f x.1 x.2) _ (fun ⟨p, i⟩ => by
      change _ = if parityWord p i ∈ S ∧ toggle (parityWord p i) d ∈ S then 1 else 0
      rw [toggle_parityWord])]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have hs : (∑ i, f false i) = ∑ i, f true i := by
    apply Fintype.sum_equiv (ht.toPerm _) _ _
    intro i
    change (if parityWord false i ∈ S ∧ parityWord true (toggleIndex i d) ∈ S then 1 else 0) =
      (if parityWord true (toggleIndex i d) ∈ S ∧
        parityWord false (toggleIndex (toggleIndex i d) d) ∈ S then 1 else 0)
    rw [show toggleIndex (toggleIndex i d) d = i from ht i]
    simp only [and_comm]
  have hsum : (∑ i, f true i) =
      ((parityMask S true) &&& shuffle (parityMask S false) d).cpop.toNat := by
    rw [cpop_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [f, BitVec.getLsbD_and, shuffle_bit, parityMask_bit, Bool.not_true]
    by_cases h₁ : parityWord true i ∈ S <;>
      by_cases h₂ : parityWord false (toggleIndex i d) ∈ S <;> simp [h₁, h₂]
  rw [hs, hsum, two_mul]

/-- A twelve-vertex adjacency parity fixed point of the five-cube induces at
most sixteen edges. -/
theorem inducedDegreeSum_le_of_card_twelve (S : Finset (BitVec 5)) (hcard : S.card = 12)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) : inducedDegreeSum S ≤ 32 := by
  have hsize : (parityMask S false).cpop.toNat + (parityMask S true).cpop.toNat = S.card := by
    have hsum : (∑ x : BitVec 5, if x ∈ S then (1 : ℕ) else 0) = S.card := by
      rw [sum_boole (R := ℕ)]
      simp
    rw [← hsum, ← Fintype.sum_equiv parityEquiv
      (fun x : Bool × Fin 16 => if parityWord x.1 x.2 ∈ S then (1 : ℕ) else 0) _
      (fun _ => rfl), Fintype.sum_prod_type, Fintype.sum_bool]
    have hd (p : Prop) [Decidable p] : (decide p).toNat = if p then 1 else 0 := by
      by_cases h : p <;> simp [h]
    simp only [cpop_sum, parityMask_bit, hd, Nat.add_comm]
  let m := parityMask S false
  let o := oppositeMask m
  have ho : parityMask S true = o := oppositeMask_eq S hpar
  have hc := certificate m (by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, show m.cpop.toNat + o.cpop.toNat = 12 from by
      simpa only [ho, hcard] using hsize]
    decide)
  change _ ≤ (16 : BitVec 16) at hc
  rw [BitVec.le_def] at hc
  simp only [BitVec.toNat_add] at hc
  have hbound (d : Fin 5) : ((o &&& shuffle m d).cpop).toNat ≤ 16 :=
    BitVec.toNat_cpop_le _
  unfold inducedDegreeSum
  simp only [directed_sum, ho, ← mul_sum, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.reduceSucc, add_zero]
  change 2 * ((o &&& shuffle m 0).cpop.toNat + ((o &&& shuffle m 1).cpop.toNat +
    ((o &&& shuffle m 2).cpop.toNat + ((o &&& shuffle m 3).cpop.toNat +
      (o &&& shuffle m 4).cpop.toNat)))) ≤ 32
  have h₀ := hbound 0
  have h₁ := hbound 1
  have h₂ := hbound 2
  have h₃ := hbound 3
  have h₄ := hbound 4
  change (((((o &&& shuffle m 0).cpop.toNat + (o &&& shuffle m 1).cpop.toNat) % 65536 +
      (o &&& shuffle m 2).cpop.toNat) % 65536 + (o &&& shuffle m 3).cpop.toNat) % 65536 +
      (o &&& shuffle m 4).cpop.toNat) % 65536 ≤ 16 at hc
  omega

#print axioms inducedDegreeSum_le_of_card_twelve

private def indicator (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

private def arcs (f : BitVec 5 → BitVec 5 → ℤ) : ℤ :=
  ∑ x, ∑ d : Fin 5, f x (toggle x d)

private theorem arcs_swap (f : BitVec 5 → BitVec 5 → ℤ) :
    arcs (fun x y => f y x) = arcs f := by
  unfold arcs
  rw [Finset.sum_comm (s := (univ : Finset (BitVec 5))),
    Finset.sum_comm (s := (univ : Finset (BitVec 5)))]
  refine sum_congr rfl fun d _ => ?_
  have ht : Function.Involutive (fun x => toggle x d) := by
    intro x
    simp [toggle, BitVec.xor_assoc]
  apply Fintype.sum_equiv (ht.toPerm _) _ _
  intro x
  change f (toggle x d) x = f (toggle x d) (toggle (toggle x d) d)
  exact congrArg (f (toggle x d)) (ht x).symm

/-- The total odd-fiber overlap of a singleton with its five neighbors in the
presence of one balanced fiber. -/
def singletonDegree (S : Finset (BitVec 5)) (v : BitVec 5)
    (center : BitVec 5 → Fin 4) (x : BitVec 5) : ℤ :=
  ∑ d : Fin 5, (indicator (toggle x d ∈ S) +
    2 * indicator (toggle x d ∈ S ∧ center x = center (toggle x d)) +
    2 * indicator (toggle x d = v))

set_option maxHeartbeats 2000000 in
/-- Twelve singleton fibers with the parity fixed-point equation cannot have
one balanced fiber of even occupation zero, two or four and a total of
twenty-four even vertices on the nonzero cuts. -/
theorem twelve_singleton_incidence_impossible
    (S I : Finset (BitVec 5)) (v : BitVec 5) (center : BitVec 5 → Fin 4) (q : ℤ)
    (hcard : S.card = 12) (hsub : I ⊆ S) (hv : v ∉ S)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x)
    (hoc : q = 0 ∨ q = 2 ∨ q = 4) (hoccupation : q = 2 * (I.card : ℤ))
    (hbalanced : (∑ d : Fin 5, indicator (toggle v d ∈ S)) = 6 - q)
    (hrow : ∀ x ∈ S, singletonDegree S v center x = 5 + 4 * indicator (x ∈ I))
    (hcenter : ∀ (x : BitVec 5) (d : Fin 5), x ∈ S → toggle x d ∈ S →
      center x = center (toggle x d) → x ∈ I ∨ toggle x d ∈ I) : False := by
  let same (x y : BitVec 5) := indicator (x ∈ S ∧ y ∈ S ∧ center x = center y)
  let pair (x y : BitVec 5) := indicator (x ∈ S ∧ y ∈ S)
  let meet (x y : BitVec 5) := indicator (x ∈ S ∧ y = v)
  let hit (x y : BitVec 5) := if x ∈ I then same x y else 0
  have hnonneg (p : Prop) [Decidable p] : 0 ≤ indicator p := by
    unfold indicator
    split <;> decide
  have hind_le (p r : Prop) [Decidable p] [Decidable r] :
      indicator (p ∧ r) ≤ indicator p := by
    by_cases hp : p <;> by_cases hr : r <;> simp [indicator, hp, hr]
  have hpair : arcs pair = (inducedDegreeSum S : ℤ) := by
    simp only [arcs, inducedDegreeSum, Nat.cast_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => ?_
    simp only [pair, indicator, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hmeet : arcs meet = 6 - q := by
    rw [← arcs_swap meet]
    unfold arcs
    change (∑ x, ∑ d : Fin 5, indicator (toggle x d ∈ S ∧ x = v)) = _
    simp_rw [show ∀ (x y : BitVec 5), indicator (y ∈ S ∧ x = v) =
        if x = v then indicator (y ∈ S) else 0 by
      intro x y
      by_cases h : x = v <;> simp [h, indicator]]
    have hf (x : BitVec 5) :
        (∑ d : Fin 5, if x = v then indicator (toggle x d ∈ S) else 0) =
          if x = v then ∑ d : Fin 5, indicator (toggle x d ∈ S) else 0 := by
      split <;> simp [*]
    simp_rw [hf]
    simpa using hbalanced
  have hbalanced_le : (∑ d : Fin 5, indicator (toggle v d ∈ S)) ≤ 5 := by
    calc
      _ ≤ ∑ _d : Fin 5, (1 : ℤ) :=
        sum_le_sum fun d _ => by unfold indicator; split <;> decide
      _ = _ := by simp
  have htotal : arcs pair + 2 * arcs same + 2 * arcs meet = 60 + 4 * (I.card : ℤ) := by
    calc
      _ = ∑ x, ∑ d : Fin 5, if x ∈ S then
          indicator (toggle x d ∈ S) +
          2 * indicator (toggle x d ∈ S ∧ center x = center (toggle x d)) +
          2 * indicator (toggle x d = v) else 0 := by
        simp only [arcs, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun x _ => sum_congr rfl fun d _ => ?_
        by_cases hx : x ∈ S <;> simp [pair, same, meet, hx, indicator]
      _ = ∑ x ∈ S, singletonDegree S v center x := by
        rw [show S = univ.filter (· ∈ S) by ext; simp, sum_filter]
        refine sum_congr rfl fun x _ => ?_
        by_cases hx : x ∈ S <;> simp [singletonDegree, hx]
      _ = _ := by
        rw [sum_congr rfl (fun x hx => hrow x hx), sum_add_distrib, ← mul_sum, sum_const,
          nsmul_eq_mul, hcard]
        have hi : (∑ x ∈ S, indicator (x ∈ I)) = (I.card : ℤ) := by
          classical
          rw [show (∑ x ∈ S, indicator (x ∈ I)) = ∑ _x ∈ S.filter (· ∈ I), (1 : ℤ) by
            rw [sum_filter]
            rfl]
          rw [show S.filter (· ∈ I) = I by
            ext x
            exact mem_filter.trans ⟨And.right, fun hx => ⟨hsub hx, hx⟩⟩]
          simp
        rw [hi]
        norm_num
  have hhit : arcs hit ≤ 3 * (I.card : ℤ) := by
    have hlocal (x : BitVec 5) (hx : x ∈ I) : (∑ d : Fin 5, same x (toggle x d)) ≤ 3 := by
      have hs := hsub hx
      have hr := hrow x hs
      have hsum : (∑ d : Fin 5, 3 * same x (toggle x d)) ≤ singletonDegree S v center x := by
        unfold singletonDegree
        refine sum_le_sum fun d _ => ?_
        have hs' (y : BitVec 5) :
            same x y = indicator (y ∈ S ∧ center x = center y) := by simp [same, hs]
        rw [hs']
        have hle := hind_le (toggle x d ∈ S) (center x = center (toggle x d))
        have hn := hnonneg (toggle x d = v)
        omega
      rw [← mul_sum] at hsum
      simp [indicator, hx] at hr
      omega
    unfold arcs
    calc
      _ ≤ ∑ x : BitVec 5, if x ∈ I then (3 : ℤ) else 0 := by
        refine sum_le_sum fun x _ => ?_
        by_cases hx : x ∈ I
        · simpa [hit, hx] using hlocal x hx
        · simp [hit, hx]
      _ = _ := by
        rw [← sum_filter, show univ.filter (· ∈ I) = I by ext; simp]
        simp [mul_comm]
  have hsame : arcs same ≤ 2 * arcs hit := by
    have hlocal (x : BitVec 5) (d : Fin 5) :
        same x (toggle x d) ≤ hit x (toggle x d) + hit (toggle x d) x := by
      let y := toggle x d
      have he : same y x = same x y := by
        have hh : (y ∈ S ∧ x ∈ S ∧ center y = center x) ↔
            (x ∈ S ∧ y ∈ S ∧ center x = center y) :=
          ⟨fun ⟨hy, hx, h⟩ => ⟨hx, hy, h.symm⟩, fun ⟨hx, hy, h⟩ => ⟨hy, hx, h.symm⟩⟩
        simp only [same, hh]
      change same x y ≤ hit x y + hit y x
      simp only [hit, he]
      by_cases h : x ∈ S ∧ y ∈ S ∧ center x = center y
      · have hn : 0 ≤ same x y := hnonneg _
        rcases hcenter x d h.1 h.2.1 h.2.2 with hx | hy
        · rw [ite_eq_left hx]
          split <;> omega
        · rw [ite_eq_left hy]
          split <;> omega
      · simp only [same, indicator, ite_eq_right h, ite_self, add_zero, le_refl]
    calc
      _ ≤ arcs (fun x y => hit x y + hit y x) :=
        sum_le_sum fun x _ => sum_le_sum fun d _ => hlocal x d
      _ = _ := by
        have hh := arcs_swap hit
        unfold arcs at *
        simp only [sum_add_distrib, hh, two_mul]
  have hbound := inducedDegreeSum_le_of_card_twelve S hcard hpar
  have hbound' : (inducedDegreeSum S : ℤ) ≤ 32 := by exact_mod_cast hbound
  omega

#print axioms twelve_singleton_incidence_impossible

open scoped Matrix
open BalancedCriticalSpectrum (Q IsBalanced flip)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9FourFiberSpectrum (leftProjection fiber_and_signedRow_supported)
open Q9SignedProjection (join fiber signedRow q9_signed_row_split)
open Q9TenPatternIncidence (tenProjection midpointCode incidence potential midpoint_cut)
open Q9K4CutBalance (occupied evenLabel cScaled evenCount oddCount LocalType singletons
  singletonSupport singleton_parity_rows singleton_support_neighborParity)
open Q9K4ZeroCutArithmetic (zeroCutOccupation)
open private pattern from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private signed_row_blocks from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenPatternIncidence
open private flip_join_right sign_join_right from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
open private occupation_totals from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4ZeroCutArithmetic
open private label_values nonzero_iff_mem selected_term pattern_parities cutPotential crosses
  cutPotential_eq incidence_laplacian local_pairing even_degree
  active_singleton_count singletonSupport_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance

private theorem cube_toggle (x : BitVec 5) (d : Fin 5) :
    cubeBitVec 5 (toggle x d) = flip (cubeBitVec 5 x) d := by
  have ht : ∀ d : Fin 5, BitVec.twoPow 5 d.val = BitVec.ofNat 5 (2 ^ d.val) := by decide +kernel
  rw [toggle, ht, cubeBitVec_xor_single]
  rfl

private def cutSize (s : Fin 4 → Bool) : ℤ := ∑ e, crosses s e
private def overlap (s t : Fin 4 → Bool) : ℤ := ∑ e, crosses s e * crosses t e

private def cutCenter (s : Fin 4 → Bool) : Fin 4 :=
  if |cutPotential s 0| = 3 then 0
  else if |cutPotential s 1| = 3 then 1
  else if |cutPotential s 2| = 3 then 2
  else 3

private theorem cutCenter_spec : ∀ s : Fin 4 → Bool, ∀ i : Fin 4,
    cutSize s = 3 → |cutPotential s i| = 3 → cutCenter s = i := by
  decide +kernel

private theorem overlap_self_types : ∀ s t : Fin 4 → Bool,
    cutSize s = 3 → cutSize t = 3 →
    overlap s t = 1 + 2 * indicator (cutCenter s = cutCenter t) := by
  decide +kernel

private theorem overlap_mixed : ∀ s t : Fin 4 → Bool,
    cutSize s = 3 → cutSize t = 4 → overlap s t = 2 := by
  decide +kernel

private theorem overlap_zero : ∀ s t : Fin 4 → Bool, cutSize t = 0 → overlap s t = 0 := by
  decide +kernel

private theorem overlap_comm (s t : Fin 4 → Bool) : overlap s t = overlap t s := by
  exact sum_congr rfl (fun _ _ => mul_comm _ _)

private def mid (z : Q 9 → ℤ) (y : Q 5) (e : Fin 6) : ℤ :=
  fiber z y (pattern (midpointCode e))

open Classical in
private theorem odd_overlap_degree {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u) (y : Q 5)
    (hout : ∀ x ∉ tenProjection, fiber z y x = 0)
    (hm : (fun e => mid z y e) = incidence.transpose *ᵥ potential (fiber z y)) :
    (∑ d : Fin 5, ∑ e, occupied (mid z y e) * occupied (mid z (flip y d) e)) =
      3 * oddCount z y - ∑ i, evenLabel z i y * cScaled z i y := by
  have hedge (e : Fin 6) :
      (∑ d : Fin 5, occupied (mid z y e) * occupied (mid z (flip y d) e)) =
      3 * occupied (mid z y e) -
        mid z y e * (incidence.transpose *ᵥ (fun i => evenLabel z i y)) e := by
    by_cases he : mid z y e = 0
    · simp [he, occupied]
    let p := pattern (midpointCode e)
    let m (x : Q 5) := mid z x e
    have hmem : join p y ∈ C := (nonzero_iff_mem hu hz _).mp he
    have hvertical : (∑ d : Fin 5, occupied (mid z (flip y d) e)) = m y * (-signedRow m y) := by
      simp only [signedRow, ← sum_neg_distrib, mul_sum]
      refine sum_congr rfl fun d _ => ?_
      have h := selected_term hreg hu hz hrow hmem (d.natAdd 4)
      rw [flip_join_right, sign_join_right, show Q9SignedProjection.leftParitySign p = -1
        from pattern_parities.2 e, neg_one_mul] at h
      change m y * (-truePrefixSign y d * m (flip y d)) = _ at h
      rw [neg_mul] at h
      exact h.symm
    have hs := q9_signed_row_split hrow p y
    rw [show Q9SignedProjection.leftParitySign p = -1 from pattern_parities.2 e, neg_one_mul] at hs
    have hhor := congrFun (signed_row_blocks hout).2 e
    change 3 * m y = signedRow (fiber z y) p - signedRow m y at hs
    change signedRow (fiber z y) p = (incidence.transpose *ᵥ (fun i => evenLabel z i y)) e at hhor
    have hocc : occupied (mid z y e) = 1 := by simp [occupied, he]
    simp only [hocc, one_mul, mul_one]
    rw [hvertical, mul_neg, ← hhor]
    change -(m y * signedRow m y) = 3 - m y * signedRow (fiber z y) p
    have hsq : m y * m y = 1 := by
      rcases hu _ hmem with h | h <;> change m y = _ at h <;> simp [h]
    nlinarith [congrArg (m y * ·) hs]
  rw [Finset.sum_comm, sum_congr rfl (fun e _ => hedge e), sum_sub_distrib, ← mul_sum]
  change 3 * oddCount z y - _ = _
  congr 1
  have hi (i : Fin 4) : (∑ e, incidence i e * mid z y e) = cScaled z i y :=
    (congrArg (fun f => (incidence *ᵥ f) i) hm).trans
      (incidence_laplacian (potential (fiber z y)) i)
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← hi, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

open Classical in
/-- An order-72 balanced cubic support with the normalized K4 projection and
eight even vertices on zero cuts has a singleton count different from twelve. -/
theorem singletons_ne_twelve_of_zeroCutOccupation_eight
    {C : Finset (Q 9)} {z : Q 9 → ℤ} (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (hcoupled : ∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y ∧
      signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y)
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hzero : zeroCutOccupation z = 8) : singletons z ≠ 12 := by
  intro h12
  let y := cubeBitVec 5
  let O (x : BitVec 5) := oddCount z (y x)
  let A (x : BitVec 5) := evenCount fun i => evenLabel z i (y x)
  let S := singletonSupport z
  let B := (univ : Finset (BitVec 5)).filter (fun x => O x = 4)
  let I := S.filter (fun x => A x = 0)
  have hS (x : BitVec 5) : x ∈ S ↔ O x = 3 := by simp [S, singletonSupport, O, y]
  have hB (x : BitVec 5) : x ∈ B ↔ O x = 4 := by simp [B]
  have hI (x : BitVec 5) : x ∈ I ↔ x ∈ S ∧ A x = 0 := mem_filter
  have hcard : S.card = 12 := by
    have h := singletonSupport_card z
    rw [h12] at h
    exact_mod_cast h
  have hunit (i : Fin 4) (x : Q 5) : evenLabel z i x = 0 ∨
      evenLabel z i x = 1 ∨ evenLabel z i x = -1 := label_values hu hz _
  have hpar := singleton_support_neighborParity (singleton_parity_rows hunit hcoupled hlocal).2
  obtain ⟨_, hAt, hOt, _⟩ :=
    occupation_totals hsize hreg hb hP hu hz hrow (fun i x => (hcoupled i x).1) hlocal
  rw [hzero] at hAt hOt
  have hO (x : BitVec 5) : O x = 0 ∨ O x = 3 ∨ O x = 4 := by
    rcases hlocal (y x) with ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hBcard : B.card = 1 := by
    have hsum := Fintype.sum_equiv y O (oddCount z) (fun _ => rfl)
    rw [hOt] at hsum
    have hp (x : BitVec 5) : O x = 3 * indicator (x ∈ S) + 4 * indicator (x ∈ B) := by
      rcases hO x with h | h | h <;> simp [hS, hB, h, indicator]
    simp_rw [hp, sum_add_distrib, ← mul_sum, indicator, sum_boole] at hsum
    have hfilter (T : Finset (BitVec 5)) : univ.filter (· ∈ T) = T := by ext; simp
    rw [hfilter, hfilter, hcard] at hsum
    omega
  obtain ⟨v, hv⟩ := card_eq_one.mp hBcard
  have hvO : O v = 4 := (hB v).mp (by simp [hv])
  have hV (x : BitVec 5) : O x = 4 ↔ x = v := by rw [← hB, hv, mem_singleton]
  have hvS : v ∉ S := by simp [hS, hvO]
  let q := A v
  have hq : q = 0 ∨ q = 2 ∨ q = 4 := by
    rcases hlocal (y v) with ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h⟩
    · change O v = 0 at h
      omega
    · change O v = 3 at h
      omega
    · exact h
  have hsingle (x : BitVec 5) (hx : x ∈ S) :
      ∃ (i : Fin 4) (sign : Bool), let s : ℤ := if sign then 1 else -1
      (∀ j, cScaled z j (y x) = s * (if j = i then 3 else -1)) ∧
      ((∀ j, evenLabel z j (y x) = 0) ∨ ∃ k : Fin 4, k ≠ i ∧
        ∀ j, evenLabel z j (y x) = s * ((if j = i then 1 else 0) - (if j = k then 1 else 0))) := by
    have hx' := (hS x).mp hx
    rcases hlocal (y x) with ⟨_, h, _⟩ | ⟨i, sign, _, hc, ha⟩ | ⟨h, _⟩
    · change O x = 0 at h
      omega
    · exact ⟨i, sign, hc, ha⟩
    · change O x = 4 at h
      omega
  have hA (x : BitVec 5) (hx : x ∈ S) : A x = 0 ∨ A x = 2 := by
    obtain ⟨i, sign, _, ha | ⟨k, hik, ha⟩⟩ := hsingle x hx
    · exact Or.inl (by simp [A, evenCount, ha, occupied])
    · exact Or.inr (active_singleton_count sign hik ha)
  have hocc : q = 2 * (I.card : ℤ) := by
    have hsum := Fintype.sum_equiv y
      (fun x => if O x = 0 then 0 else A x)
      (fun u => if oddCount z u = 0 then 0 else evenCount fun i => evenLabel z i u)
      (fun _ => rfl)
    have hnonzero : (∑ u : Q 5, if oddCount z u = 0 then 0 else
        evenCount (fun i => evenLabel z i u)) = 24 := by
      have hterm (u : Q 5) :
          (if oddCount z u = 0 then 0 else evenCount (fun i => evenLabel z i u)) =
          evenCount (fun i => evenLabel z i u) -
            (if oddCount z u = 0 then evenCount (fun i => evenLabel z i u) else 0) := by
        split <;> simp
      simp_rw [hterm, sum_sub_distrib]
      change (∑ u, evenCount fun i => evenLabel z i u) - zeroCutOccupation z = 24
      rw [hAt, hzero]
      norm_num
    rw [hnonzero] at hsum
    have hp (x : BitVec 5) : (if O x = 0 then 0 else A x) =
        2 * indicator (x ∈ S) - 2 * indicator (x ∈ I) + (if x = v then q else 0) := by
      rcases hO x with h | h | h
      · have hvx : x ≠ v := fun he => by rw [he, hvO] at h; omega
        simp [hI, hS, h, hvx, indicator]
      · have hvx : x ≠ v := fun he => by rw [he, hvO] at h; omega
        rcases hA x ((hS x).mpr h) with ha | ha <;> simp [hI, hS, h, hvx, ha, indicator]
      · have he := (hV x).mp h
        subst x
        simp [hI, hS, hvO, q, indicator]
    simp_rw [hp, sum_add_distrib, sum_sub_distrib, ← mul_sum, indicator, sum_boole] at hsum
    have hfilter (T : Finset (BitVec 5)) : univ.filter (· ∈ T) = T := by ext; simp
    rw [hfilter, hfilter, hcard] at hsum
    simp at hsum
    omega
  have hout (x : BitVec 5) (p : Q 4) (hp : p ∉ tenProjection) :=
    fiber_and_signedRow_supported hz hrow (y x) (hP.symm ▸ hp)
  have hcut (x : BitVec 5) :
      ∃ (s : Fin 4 → Bool), (∀ i, cScaled z i (y x) = cutPotential s i) ∧
        (∀ e, occupied (mid z (y x) e) = crosses s e) ∧
        (fun e => mid z (y x) e) = incidence.transpose *ᵥ potential (fiber z (y x)) := by
    have hmid (e : Fin 6) : |mid z (y x) e| ≤ 1 := by
      rcases label_values hu hz (join (pattern (midpointCode e)) (y x)) with h | h | h <;>
        change mid z (y x) e = _ at h <;> norm_num [h]
    obtain ⟨hm, _, level, s, hl, he⟩ :=
      midpoint_cut (fun p hp => (hout x p hp).1) (fun p hp => (hout x p hp).2) hmid
    refine ⟨s, cutPotential_eq hl, fun e => ?_, hm⟩
    have hh := he e
    change mid z (y x) e ≠ 0 ↔ _ at hh
    unfold occupied crosses
    by_cases h : mid z (y x) e = 0 <;> simp_all
  choose s hpot hmid hmat using hcut
  let center (x : BitVec 5) := cutCenter (s x)
  have hcs (x : BitVec 5) : cutSize (s x) = O x := by
    simp only [O, oddCount, cutSize, ← hmid, mid]
  have hover (x : BitVec 5) :
      (∑ d : Fin 5, overlap (s x) (s (toggle x d))) =
      3 * O x - (if O x = 0 then 0 else 2 * A x) := by
    have h := odd_overlap_degree hreg hu hz hrow (y x) (fun p hp => (hout x p hp).1) (hmat x)
    rw [local_pairing (hlocal (y x))] at h
    exact (sum_congr rfl fun d _ => by simp only [overlap, ← hmid, y, cube_toggle]).trans h
  refine twelve_singleton_incidence_impossible S I v center q hcard (filter_subset _ _) hvS hpar
    hq hocc ?_ ?_ ?_
  · have hweight (d : Fin 5) : overlap (s v) (s (toggle v d)) =
        2 * indicator (toggle v d ∈ S) := by
      rcases hO (toggle v d) with h | h | h
      · simp [overlap_zero _ _ (by rwa [hcs]), hS, h, indicator]
      · rw [overlap_comm, overlap_mixed _ _ (by rwa [hcs]) (by rw [hcs, hvO])]
        simp [hS, h, indicator]
      · have hne : ∀ (i : Fin 32) (d : Fin 5), toggle (BitVec.ofFin i) d ≠ BitVec.ofFin i := by
          decide +kernel
        exact (hne v.toFin d ((hV (toggle v d)).mp h)).elim
    have h := hover v
    simp_rw [hweight, ← mul_sum, hvO] at h
    norm_num at h
    change _ = 12 - 2 * q at h
    omega
  · intro x hx
    have hxO := (hS x).mp hx
    have hweight (d : Fin 5) : overlap (s x) (s (toggle x d)) =
        indicator (toggle x d ∈ S) +
          2 * indicator (toggle x d ∈ S ∧ center x = center (toggle x d)) +
          2 * indicator (toggle x d = v) := by
      have hxC : cutSize (s x) = 3 := by rwa [hcs]
      rcases hO (toggle x d) with h | h | h
      · have hvx : toggle x d ≠ v := fun he => by rw [he, hvO] at h; omega
        simp [overlap_zero _ _ (by rwa [hcs]), hS, h, hvx, indicator]
      · have hvx : toggle x d ≠ v := fun he => by rw [he, hvO] at h; omega
        rw [overlap_self_types _ _ hxC (by rwa [hcs])]
        simp [hS, h, hvx, center, indicator]
      · rw [overlap_mixed _ _ hxC (by rwa [hcs])]
        simp [hS, (hV (toggle x d)).mp h, hvO, indicator]
    have h := hover x
    simp only [hweight, hxO] at h
    change singletonDegree S v center x = 3 * 3 - (if (3 : ℤ) = 0 then 0 else 2 * A x) at h
    rcases hA x hx with ha | ha <;> norm_num [hI, hx, ha, indicator] at h ⊢ <;> exact h
  · intro x d hx hw he
    by_contra! hn
    let w := toggle x d
    have hactive (u : BitVec 5) (hs : u ∈ S) (hi : u ∉ I) :
        evenLabel z (center u) (y u) ≠ 0 ∧
          evenLabel z (center u) (y u) * cScaled z (center u) (y u) = 3 := by
      obtain ⟨i, sign, hc, ha | ⟨k, hk, ha⟩⟩ := hsingle u hs
      · exact (hi ((hI u).mpr ⟨hs, by simp [A, evenCount, occupied, ha]⟩)).elim
      have hci := hc i
      have hi' : center u = i := by
        apply cutCenter_spec _ _ (by rw [hcs]; exact (hS u).mp hs)
        rw [← hpot, hci]
        cases sign <;> norm_num
      rw [hi']
      have hai := ha i
      have hik : i ≠ k := Ne.symm hk
      cases sign <;> simp_all
    obtain ⟨hxA, hxprod⟩ := hactive x hx hn.1
    obtain ⟨hwA, _⟩ := hactive w hw hn.2
    have h := even_degree hreg hu hz hrow (fun i u => (hcoupled i u).1) _ _ hxA
    rw [hxprod] at h
    have hm : occupied (evenLabel z (center x) (flip (y x) d)) ≤
        Q9K4CutBalance.evenVerticalDegree z (center x) (y x) :=
      single_le_sum (f := fun i => occupied (evenLabel z (center x) (flip (y x) i)))
        (fun _ _ => by unfold occupied; split <;> omega) (mem_univ d)
    rw [h, ← cube_toggle, he] at hm
    change occupied (evenLabel z (center w) (y w)) ≤ 3 - 3 at hm
    have hm' : occupied (evenLabel z (center w) (y w)) = 1 := by simp [occupied, hwA]
    rw [hm'] at hm
    omega

#print axioms singletons_ne_twelve_of_zeroCutOccupation_eight

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4TwelveSingletons
