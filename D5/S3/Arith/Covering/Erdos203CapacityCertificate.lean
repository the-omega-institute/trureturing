/- GID: D5/S3/Arith/Covering/Erdos203CapacityCertificate
   generality: I
   mirror-B: D5/B/S3/Arith/Covering/Erdos203CapacityCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas]
   utility: kind=checker; basis=consumer=D5/S3/Arith/Covering/Erdos203ConditionalCapacity.result; instance=D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate72
   digest: Sound cyclic packed certificates for actual original-residue capacities -/

import D5.S3.Arith.Covering.Erdos203SixCapacity
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Indexes
open scoped BigOperators
namespace D5.S3.Arith.Covering.Erdos203
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def packed (U : Finset SixRect) (i : Fin 252) : Nat :=
  ∑ q ∈ U, 16384 ^ originalResidue i q


def keep (c x y : Nat) : Bool :=
  (x+3*y)%4 != 0 && (2*x+y)%6 != 0 && (x+8*y)%10 != c/48 &&
  (x+4*y)%12 != c/24%2 && (14*x+y)%16 != c/6%4 && (x+13*y)%18 != c%6

def canonicalPhases (c : Fin 96) : Phases :=
  Fin.addCases (m := 7) (n := 245) (motive := fun _ => ℤ)
    ![0,0,c.val/48,c.val/24%2,c.val/6%4,c.val%6,0] (fun _ => 0)




def encodePolynomials (p : Fin 24 → Nat) (g a b : Nat) : Nat :=
  ((List.finRange 24).map fun y =>
    ((List.range g).map fun t =>
      (p y % (16384^g-1) / 16384^t % 16384) * 16384^((a*t+b*y.val)%g)).sum).sum


def key : Fin 129 → Nat × Nat × Nat := ![
(1,0,0),
(2,0,1),
(2,1,0),
(2,1,1),
(3,0,2),
(3,2,0),
(3,2,1),
(4,1,0),
(4,1,1),
(4,1,3),
(4,3,0),
(4,3,1),
(4,3,2),
(5,1,3),
(6,0,1),
(6,1,1),
(6,1,2),
(6,1,3),
(6,1,5),
(6,2,1),
(6,2,3),
(6,3,1),
(6,4,1),
(6,4,3),
(6,4,5),
(6,5,1),
(6,5,3),
(6,5,4),
(8,0,1),
(8,2,1),
(8,2,7),
(8,4,1),
(8,6,1),
(8,6,3),
(10,6,3),
(10,7,1),
(12,0,5),
(12,0,7),
(12,1,0),
(12,1,2),
(12,1,3),
(12,1,6),
(12,1,8),
(12,1,9),
(12,1,10),
(12,2,7),
(12,2,9),
(12,3,2),
(12,3,7),
(12,3,8),
(12,3,10),
(12,3,11),
(12,4,3),
(12,4,5),
(12,5,4),
(12,5,6),
(12,5,7),
(12,5,9),
(12,5,11),
(12,6,1),
(12,6,5),
(12,6,7),
(12,7,0),
(12,7,1),
(12,7,4),
(12,7,5),
(12,7,10),
(12,9,2),
(12,9,4),
(12,9,5),
(12,9,10),
(12,9,11),
(12,10,5),
(12,11,2),
(12,11,3),
(12,11,4),
(12,11,6),
(12,11,7),
(12,11,10),
(12,11,11),
(16,6,1),
(16,10,1),
(16,14,1),
(16,14,9),
(18,1,10),
(18,1,13),
(18,4,1),
(18,4,13),
(18,16,1),
(20,1,3),
(24,0,19),
(24,2,17),
(24,4,3),
(24,8,13),
(24,16,1),
(24,20,15),
(24,22,13),
(30,1,13),
(30,1,23),
(30,2,1),
(30,4,27),
(30,6,13),
(30,9,7),
(30,13,9),
(30,14,17),
(30,27,1),
(36,1,10),
(36,2,35),
(36,7,16),
(36,17,26),
(36,26,29),
(36,29,14),
(36,29,35),
(36,31,19),
(36,31,28),
(40,12,1),
(40,32,1),
(48,18,29),
(48,22,5),
(48,38,21),
(60,1,48),
(60,1,58),
(60,14,7),
(60,17,21),
(60,53,54),
(72,40,7),
(72,40,13),
(72,68,11),
(144,62,71)]


def tailIndex (j : Fin 245) : Fin 252 := Fin.natAdd 7 j

def rowKey : Fin 245 → Fin 129 := ![8,14,39,30,21,8,41,17,0,52,22,28,58,8,20,68,31,14,2,29,23,70,18,42,0,55,8,88,97,68,0,77,2,28,100,31,17,54,15,93,31,18,47,81,56,2,42,49,2,82,69,22,86,2,32,42,17,25,43,4,41,31,19,80,0,41,66,8,19,38,33,64,105,18,28,85,0,24,24,32,23,74,12,21,7,18,128,18,63,28,95,75,89,38,14,82,81,73,14,18,17,10,115,120,2,20,101,0,112,9,22,2,51,106,82,90,31,14,65,103,41,59,99,42,113,8,109,8,104,126,19,117,21,81,17,45,8,0,102,123,81,50,23,91,31,78,2,73,82,118,56,71,24,26,98,84,64,14,2,39,108,115,21,86,53,11,88,116,2,54,87,121,0,106,77,54,23,92,19,44,122,110,1,42,111,92,94,5,107,49,45,13,63,43,125,40,124,37,119,1,114,78,62,3,41,46,27,0,54,60,12,25,34,18,61,64,79,0,43,48,127,41,9,57,6,9,16,76,15,42,67,96,35,72,39,67,0,64,36,5,0,83,21,1,10]


def weight (j : Fin 245) : Nat :=
  (if (rows (tailIndex j)).p = 199 ∨ (rows (tailIndex j)).p = 2377 then 11 else 10) *
    restrictedGcd (tailIndex j) * (period / (rows (tailIndex j)).e)


/-- Small exact data, together with kernel checks of every arithmetic obligation. -/
structure CapacityCertificate (c : Fin 96) where
  polynomials : Fin 24 → Nat
  codes : Fin 129 → Nat
  caps : Fin 129 → Nat
  count : Nat
  polynomial_valid : ∀ y : Fin 24, polynomials y =
    (((List.range 360).filter (fun x => keep c.val x y.val)).map (16384^·)).sum
  code_valid : ∀ j : Fin 129,
    encodePolynomials polynomials (key j).1 (key j).2.1 (key j).2.2 = codes j
  maxima_valid : ∀ j : Fin 129, ∀ t : Fin (key j).1,
    codes j / 16384^t.val % 16384 ≤ caps j
  count_valid : codes 0 = count
  arithmetic : 41512904387 * (95040*period) + 2792167686000 *
      (∑ j : Fin 245, weight j * caps (rowKey j)) ≤
    2792167686000 * (10 * count * period)

/-- The certificate computes actual Finset histograms. Cyclic polynomial reduction and
bounded digits certify the counts, and the literal original rows determine every weight. -/
theorem certificate_bound (c : Fin 96) (cert : CapacityCertificate c) :
    41512904387 * (95040*period) + 2792167686000 *
      (∑ j : Fin 245, weight j * histogramMaximum (sixMissed (canonicalPhases c)) (tailIndex j)) ≤
    2792167686000 * (10 * (sixMissed (canonicalPhases c)).card * period) := by
  classical
  have digit_count {α : Type} [DecidableEq α] (U : Finset α) (f : α → Nat)
      (g : Nat) (hg : 0 < g) (hU : U.card ≤ 8640) (hf : ∀ q ∈ U, f q < g)
      (t : Nat) (ht : t < g) :
      (∑ q ∈ U, 16384^f q) / 16384^t % 16384 = (U.filter (f · = t)).card := by
    classical
    let ds : Fin g → Nat := fun s => (U.filter (f · = s.val)).card
    have hd : ∀ s : Fin g, ds s < 16384 := by
      intro s
      have h₁ := Finset.card_filter_le (s := U) (p := (f · = s.val))
      dsimp [ds]
      omega
    have enc : (∑ q ∈ U, 16384^f q) = Nat.ofDigits 16384 (List.ofFn ds) := by
      rw [Nat.ofDigits_eq_sum_mapIdx]
      simp only [List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn, List.sum_ofFn]
      change (∑ q ∈ U, 16384 ^ f q) =
        ∑ s : Fin g, ds s * 16384 ^ s.val
      symm
      calc
        (∑ s : Fin g, ds s * 16384 ^ s.val) =
            ∑ s : Fin g, ∑ q ∈ U.filter (f · = s.val),
              16384 ^ f q := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_congr rfl (fun q hq => by rw [(Finset.mem_filter.mp hq).2])]
          simp [ds]
        _ = ∑ q ∈ U, 16384 ^ f q := by
          rw [← Finset.sum_range (n := g) (fun s => ∑ q ∈ U.filter (f · = s), 16384^f q)]
          exact Finset.sum_fiberwise_of_maps_to (g := f)
            (s := U) (t := Finset.range g) (fun q hq => Finset.mem_range.mpr (hf q hq)) _
    rw [enc, Nat.ofDigits_div_pow_eq_ofDigits_drop t (by decide)
      (List.ofFn ds) (by simpa using hd), Nat.ofDigits_mod_eq_head!]
    have hh : (List.drop t (List.ofFn ds)).head! = ds ⟨t,ht⟩ := by
      simp [List.head!_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_drop, show t < g from ht]
    rw [hh, Nat.mod_eq_of_lt (hd ⟨t,ht⟩)]
  have keep_iff (c : Fin 96) (q : SixRect) : q ∈ sixMissed (canonicalPhases c) ↔
      keep c.val q.1.val q.2.val = true := by
    classical
    simp only [sixMissed, Finset.mem_filter, Finset.mem_univ, true_and]
    have eq (j : Fin 6) : originalMap (j.castLE (by decide : 6 ≤ 252)) (sixRepresentative q) =
        (canonicalPhases c (j.castLE (by decide : 6 ≤ 252)) : ZMod (rows (j.castLE (by decide : 6 ≤ 252))).e) ↔
        (rows (j.castLE (by decide : 6 ≤ 252))).hits
          (canonicalPhases c (j.castLE (by decide : 6 ≤ 252))) q.1.val q.2.val := by
      exact (original_six_fibers.2.2.2 _).1 _ _ _
    simp_rw [ne_eq, eq]
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
    change (¬ (1*(q.1.val:ℤ)+3*q.2.val)%4=0%4) ∧
      (¬ (2*(q.1.val:ℤ)+1*q.2.val)%6=0%6) ∧
      (¬ (1*(q.1.val:ℤ)+8*q.2.val)%10=(c.val:ℤ)/48%10) ∧
      (¬ (1*(q.1.val:ℤ)+4*q.2.val)%12=((c.val:ℤ)/24%2)%12) ∧
      (¬ (14*(q.1.val:ℤ)+1*q.2.val)%16=((c.val:ℤ)/6%4)%16) ∧
      (¬ (1*(q.1.val:ℤ)+13*q.2.val)%18=((c.val:ℤ)%6)%18) ∧ True ↔ _
    simp only [keep,Bool.and_eq_true, bne_iff_ne]
    have hc := c.isLt
    have h0 : (c.val:ℤ)/48%10 = c.val/48 := by omega
    have h1 : ((c.val:ℤ)/24%2)%12 = (c.val:ℤ)/24%2 := by omega
    have h2 : ((c.val:ℤ)/6%4)%16 = (c.val:ℤ)/6%4 := by omega
    have h3 : ((c.val:ℤ)%6)%18 = (c.val:ℤ)%6 := by omega
    rw [h0,h1,h2,h3]
    norm_cast
    simp only [one_mul, Nat.zero_mod, and_true, and_assoc]
  have cyclic_eq (S : Finset Nat) (hS : S.card ≤ 8640) (g : Nat) (hg : 0 < g) :
      (∑ x ∈ S, 16384^x) % (16384^g-1) = ∑ x ∈ S, 16384^(x%g) := by
    have hpow : 16384 ≤ 16384^g := by
      exact Nat.le_self_pow hg.ne' 16384
    have hm : 1 < 16384^g-1 := by omega
    have power : Nat.ModEq (16384^g-1) (16384^g) 1 := by
      change 16384^g % (16384^g-1) = 1 % (16384^g-1)
      conv_lhs => arg 1; rw [show 16384^g = (16384^g-1)+1 by omega]
      rw [Nat.add_mod_left]
    have each (x : Nat) : Nat.ModEq (16384^g-1) (16384^x) (16384^(x%g)) := by
      conv_lhs => rw [← Nat.mod_add_div x g, pow_add, pow_mul]
      simpa only [one_pow, mul_one] using (Nat.ModEq.refl (16384^(x%g))).mul (power.pow (x/g))
    have sum_eq : (∑ x ∈ S, 16384^x) % (16384^g-1) =
        (∑ x ∈ S, 16384^(x%g)) % (16384^g-1) := by
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a S ha ih =>
        simp only [Finset.sum_insert ha]
        exact (each a).add (ih (by simp only [Finset.card_insert_of_notMem ha] at hS; omega))
    rw [sum_eq]
    apply Nat.mod_eq_of_lt
    have hb : ∑ x ∈ S, 16384^(x%g) ≤ S.card * 16384^(g-1) := by
      calc
        _ ≤ ∑ _x ∈ S, 16384^(g-1) := by
          exact Finset.sum_le_sum (fun x hx => Nat.pow_le_pow_right (by decide) (by have := Nat.mod_lt x hg; omega))
        _ = _ := by simp
    have hp : 0 < 16384^(g-1) := by positivity
    have he : 16384^g = 16384^(g-1)*16384 := by
      conv_lhs => rw [show g=(g-1)+1 by omega, pow_succ]
    have hb2 : S.card * 16384^(g-1) ≤ 8640 * 16384^(g-1) := Nat.mul_le_mul_right _ hS
    omega
  have cyclic_projection (S : Finset Nat) (hS : S.card ≤ 8640)
      (g a b : Nat) (hg : 0 < g) :
      (∑ t ∈ Finset.range g,
        (((∑ x ∈ S, 16384^x) % (16384^g-1)) / 16384^t % 16384) *
          16384^((a*t+b)%g)) = ∑ x ∈ S, 16384^((a*x+b)%g) := by
    rw [cyclic_eq S hS g hg]
    calc
      _ = ∑ t ∈ Finset.range g, (S.filter (fun x => x%g=t)).card *
          16384^((a*t+b)%g) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [digit_count S (fun x => x%g) g hg hS (fun x hx => Nat.mod_lt x hg)
          t (Finset.mem_range.mp ht)]
      _ = ∑ t ∈ Finset.range g, ∑ x ∈ S.filter (fun x => x%g=t),
          16384^((a*x+b)%g) := by
        apply Finset.sum_congr rfl
        intro t ht
        symm
        have hs : ∀ x ∈ S.filter (fun x => x%g=t), (a*x+b)%g=(a*t+b)%g := by
          intro x hx
          calc
            _ = (a%g*(x%g)+b%g)%g := by simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
            _ = _ := by rw [(Finset.mem_filter.mp hx).2]; simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
        rw [Finset.sum_congr rfl (fun x hx => congrArg (16384^·) (hs x hx))]
        simp
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (g := fun x => x%g) (fun x hx => Finset.mem_range.mpr (Nat.mod_lt x hg)) _
  have encode_semantics (c : Fin 96) (p : Fin 24 → Nat)
      (hp : ∀ y : Fin 24, p y =
        (((List.range 360).filter (fun x => keep c.val x y.val)).map (16384^·)).sum)
      (g a b : Nat) (hg : 0 < g) :
      encodePolynomials p g a b =
        ∑ q ∈ sixMissed (canonicalPhases c), 16384^((a*q.1.val+b*q.2.val)%g) := by
    classical
    let S (y : Fin 24) := (Finset.range 360).filter (fun x => keep c.val x y.val = true)
    have hp' (y : Fin 24) : p y = ∑ x ∈ S y, 16384^x := by
      rw [hp y, ← List.sum_toFinset _ (List.nodup_range.filter _)]
      simp only [List.toFinset_filter,List.toFinset_range]
      rfl
    have hs (y : Fin 24) : (S y).card ≤ 8640 := by
      have h := Finset.card_filter_le (s := Finset.range 360)
        (p := fun x => keep c.val x y.val = true)
      simpa only [Finset.card_range] using h.trans (by decide : 360 ≤ 8640)
    have enc : encodePolynomials p g a b =
        ∑ y : Fin 24, ∑ x ∈ S y, 16384^((a*x+b*y.val)%g) := by
      unfold encodePolynomials
      rw [← Fin.sum_univ_def]
      apply Finset.sum_congr rfl
      intro y _
      rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, hp' y]
      exact cyclic_projection (S y) (hs y) g a (b*y.val) hg
    rw [enc]
    simp only [sixMissed, Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_filter, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro x _
    have hk := keep_iff c (x,y)
    simp only [sixMissed,Finset.mem_filter,Finset.mem_univ,true_and] at hk
    change (if keep c.val x.val y.val = true then _ else _) = _
    simp only [hk]
  have rows_valid : ∀ j : Fin 245,
      (key (rowKey j)).1 = restrictedGcd (tailIndex j) ∧
      (key (rowKey j)).2.1 = (rows (tailIndex j)).a % restrictedGcd (tailIndex j) ∧
      (key (rowKey j)).2.2 = (rows (tailIndex j)).b % restrictedGcd (tailIndex j) ∧
      0 < restrictedGcd (tailIndex j) := by decide +kernel

  let U := sixMissed (canonicalPhases c)
  have enc (j : Fin 245) : packed U (tailIndex j) = cert.codes (rowKey j) := by
    rw [← cert.code_valid]
    have h := encode_semantics c cert.polynomials cert.polynomial_valid
      (key (rowKey j)).1 (key (rowKey j)).2.1 (key (rowKey j)).2.2
      (by rw [(rows_valid j).1]; exact (rows_valid j).2.2.2)
    change packed U (tailIndex j) = encodePolynomials cert.polynomials _ _ _
    rw [h]
    apply Finset.sum_congr rfl
    intro q hq
    unfold originalResidue
    rw [(rows_valid j).1,(rows_valid j).2.1,(rows_valid j).2.2.1]
    have reduce (g a b x y : Nat) :
        (a*x+b*y)%g=((a%g)*x+(b%g)*y)%g := by
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    exact congrArg (16384^·) (reduce _ _ _ _ _)
  have bound (j : Fin 245) : histogramMaximum U (tailIndex j) ≤ cert.caps (rowKey j) := by
    apply Finset.sup_le
    intro t ht
    have dg := digit_count U (originalResidue (tailIndex j)) (restrictedGcd (tailIndex j))
      (rows_valid j).2.2.2 (by
        have hh := Finset.card_le_univ U
        simpa only [Fintype.card_prod,Fintype.card_fin] using hh)
      (fun q hq => Nat.mod_lt _ (rows_valid j).2.2.2) t (Finset.mem_range.mp ht)
    rw [← dg]
    change packed U (tailIndex j) / 16384^t % 16384 ≤ _
    rw [enc]
    exact cert.maxima_valid (rowKey j) ⟨t, by rw [(rows_valid j).1]; exact Finset.mem_range.mp ht⟩
  have hc : U.card = cert.count := by
    have eh := enc 8
    have zero (q : SixRect) : originalResidue (tailIndex 8) q = 0 := by
      change ((rows (tailIndex 8)).a*q.1.val + (rows (tailIndex 8)).b*q.2.val) % 1 = 0
      exact Nat.mod_one _
    simp only [packed,zero,pow_zero,Finset.sum_const,smul_eq_mul,mul_one] at eh
    exact eh.trans cert.count_valid
  have hcapa : (∑ j : Fin 245, weight j * histogramMaximum U (tailIndex j)) ≤
      ∑ j : Fin 245, weight j * cert.caps (rowKey j) :=
    Finset.sum_le_sum (fun j hj => Nat.mul_le_mul_left _ (bound j))
  change _ ≤ 2792167686000 * (10 * U.card * period)
  rw [hc]
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ hcapa) _).trans cert.arithmetic

end D5.S3.Arith.Covering.Erdos203
