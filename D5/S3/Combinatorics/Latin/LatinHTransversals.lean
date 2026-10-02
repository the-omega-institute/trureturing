/- GID: D5/S3/Combinatorics/Latin/LatinHTransversals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Latin/LatinHTransversals
   mirror-E: none(waiver:explicit-source-family-and-coordinate-certificates)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Literal H-family data and the distinguished-entry charge obstruction. -/

import D5.S3.Combinatorics.LatinEulerianDefs
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatinHTransversals

def order (k : ℕ) : ℕ := 4 * k

/-- The standard residue, including negative raw cap columns. -/
def residue (k : ℕ) (hk : 9 ≤ k) (x : ℤ) : Fin (order k) :=
  ⟨(x % (order k)).toNat, by
    have hp : (0 : ℤ) < order k := by dsimp [order]; omega
    have hlt := Int.emod_lt_of_pos x hp
    omega⟩

/-- Equation (7), evaluated on standard representatives in priority order. -/
def delta (k : ℕ) (a b : Fin (order k)) : ℤ :=
  let x : ℤ := a.val
  let y : ℤ := b.val
  if (a.val = 0 ∨ a.val = 5 ∨ a.val = 10) ∧ b.val % 4 = 1 ∧
      y - 4 * x / 5 ≠ 1 then 4
  else if (a.val = 1 ∧ b.val = 1) ∨ (a.val = 6 ∧ b.val = 5) ∨
      (a.val = 11 ∧ b.val = 9) then 3
  else if (a.val = 0 ∨ a.val = 5 ∨ a.val = 10) ∧
      1 ≤ y - 4 * x / 5 ∧ y - 4 * x / 5 ≤ 4 then 1
  else if (a.val = 1 ∨ a.val = 6 ∨ a.val = 11) ∧
      2 ≤ y - 4 * (x - 1) / 5 ∧ y - 4 * (x - 1) / 5 ≤ 4 then -1
  else if (a.val = 4 ∨ a.val = 9 ∨ a.val = 14) ∧ b.val % 4 = 1 then -4
  else if 15 ≤ a.val ∧ a.val < order k - 21 ∧ a.val % 4 = 3 ∧
      b.val % 2 = 0 then 2
  else if 15 ≤ a.val ∧ a.val < order k - 21 ∧ a.val % 4 = 1 ∧
      b.val % 2 = 0 then -2
  else 0

def square (k : ℕ) (hk : 9 ≤ k) (a b : Fin (order k)) : Fin (order k) :=
  residue k hk ((a.val : ℤ) + (b.val : ℤ) + delta k a b)

def shift (j : Fin 3) : ℤ := if j.val = 1 then -4 else 0

def bulkColumnRaw (k : ℕ) (j : Fin 3) (t r : ℕ) : ℤ :=
  match r with
  | 0 => 12 + shift j - 2 * (t : ℤ)
  | 1 => 2 * (k : ℤ) + 10 + shift j - 2 * (t : ℤ)
  | 2 => -1 + shift j - 2 * (t : ℤ)
  | _ => 2 * (k : ℤ) + 1 + shift j - 2 * (t : ℤ)

def bulkSymbolRaw (k : ℕ) (j : Fin 3) (t r : ℕ) : ℤ :=
  match r with
  | 0 => 29 + shift j + 2 * (t : ℤ)
  | 1 => 2 * (k : ℤ) + 26 + shift j + 2 * (t : ℤ)
  | 2 => 16 + shift j + 2 * (t : ℤ)
  | _ => 2 * (k : ℤ) + 19 + shift j + 2 * (t : ℤ)

/-- The literal cap columns, as affine pairs `(coefficient of k, constant)`. -/
def capTable : Array (Array (ℤ × ℤ)) := #[
  #[(0,13),(0,17),(0,5),(0,5),(0,9),(0,9)],
  #[(0,18),(0,18),(0,1),(0,1),(0,1),(0,1)],
  #[(0,3),(0,11),(0,13),(2,7),(0,7),(0,19)],
  #[(2,9),(0,7),(0,3),(0,3),(0,16),(0,16)],
  #[(2,16),(2,16),(2,12),(2,12),(2,16),(0,7)],
  #[(2,5),(2,3),(2,1),(2,-1),(2,5),(2,3)],
  #[(0,5),(0,5),(0,11),(0,11),(0,5),(0,5)],
  #[(2,3),(2,7),(0,14),(0,14),(0,18),(0,18)],
  #[(2,14),(2,14),(2,10),(0,7),(2,14),(2,14)],
  #[(0,16),(0,16),(0,10),(0,10),(0,14),(0,14)],
  #[(0,1),(0,1),(0,-3),(0,-3),(0,13),(0,13)],
  #[(0,9),(0,9),(0,9),(0,9),(2,7),(2,9)],
  #[(2,12),(2,12),(2,8),(2,8),(2,12),(2,12)],
  #[(0,14),(0,14),(2,-1),(2,1),(2,3),(2,5)],
  #[(0,7),(0,3),(0,-1),(0,-1),(0,3),(0,3)],
  #[(0,22),(0,22),(0,18),(0,18),(0,22),(0,22)],
  #[(2,24),(0,28),(2,18),(2,26),(2,24),(0,28)],
  #[(0,26),(0,24),(0,20),(0,20),(0,26),(0,26)],
  #[(2,26),(2,24),(0,22),(0,22),(2,26),(2,20)],
  #[(0,28),(0,26),(2,26),(0,24),(2,30),(2,28)],
  #[(2,22),(2,26),(2,20),(2,14),(0,24),(2,16)],
  #[(0,24),(2,30),(2,11),(2,11),(2,15),(2,13)],
  #[(2,30),(2,18),(0,24),(0,13),(2,20),(2,30)],
  #[(2,15),(0,20),(2,7),(0,16),(2,28),(2,26)],
  #[(0,20),(0,15),(0,15),(2,16),(2,22),(0,24)],
  #[(2,11),(2,9),(2,22),(2,5),(2,9),(2,15)],
  #[(2,28),(2,28),(2,24),(2,20),(0,20),(0,20)],
  #[(2,7),(2,11),(0,16),(2,22),(2,11),(2,24)],
  #[(0,11),(0,19),(0,7),(2,10),(0,11),(0,11)],
  #[(0,17),(2,15),(2,13),(2,18),(0,28),(2,17)],
  #[(0,19),(2,22),(2,14),(2,24),(0,17),(0,15)],
  #[(2,20),(2,5),(2,5),(0,15),(2,17),(2,22)],
  #[(2,17),(2,17),(0,12),(0,12),(0,19),(2,18)],
  #[(0,15),(2,20),(2,16),(2,3),(0,15),(2,11)],
  #[(2,13),(2,13),(2,9),(2,9),(2,13),(0,17)],
  #[(2,18),(0,13),(2,3),(2,13),(2,18),(2,7)]
]

def capAffine (j : Fin 3) (odd : Bool) (i : Fin 36) : ℤ × ℤ :=
  (capTable.getD i.val #[]).getD (2 * j.val + if odd then 1 else 0) (0, 0)

def capEpsilon (j : Fin 3) (i : Fin 36) : ℤ :=
  if i.val = 0 ∨ i.val = 5 ∨ i.val = 10 then 4
  else if (i.val = 1 ∧ j.val ≠ 0) ∨ (i.val = 6 ∧ j.val ≠ 1) ∨
      (i.val = 11 ∧ j.val ≠ 2) then 3
  else 0

/-- Tail rows contribute `-ell` after reduction of `4k-ell` modulo `4k`. -/
def capSymbolAffine (j : Fin 3) (odd : Bool) (i : Fin 36) : ℤ × ℤ :=
  let p := capAffine j odd i
  (p.1, p.2 + if i.val < 15 then (i.val : ℤ) + capEpsilon j i
             else (i.val : ℤ) - 36)

def capColumnComplement (s : ℤ) : List (ℤ × ℤ) :=
  ((List.range 8).map (fun u : ℕ => ((0 : ℤ), 14 + s + 2 * (u : ℤ)))) ++
  ((List.range 10).map (fun u : ℕ => ((2 : ℤ), 12 + s + 2 * (u : ℤ)))) ++
  ((List.range 10).map (fun u : ℕ => ((0 : ℤ), 1 + s + 2 * (u : ℤ)))) ++
  ((List.range 8).map (fun u : ℕ => ((2 : ℤ), 3 + s + 2 * (u : ℤ))))

def capSymbolComplement (s : ℤ) : List (ℤ × ℤ) :=
  ((List.range 4).map (fun u : ℕ => ((0 : ℤ), 8 + s + 2 * (u : ℤ)))) ++
  ((List.range 14).map (fun u : ℕ => ((2 : ℤ), -2 + s + 2 * (u : ℤ)))) ++
  ((List.range 14).map (fun u : ℕ => ((0 : ℤ), 1 + s + 2 * (u : ℤ)))) ++
  ((List.range 4).map (fun u : ℕ => ((2 : ℤ), 11 + s + 2 * (u : ℤ))))

def columnRaw (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) (a : Fin (order k)) : ℤ :=
  let odd := k % 2 = 1
  if h : a.val < 15 then
    let p := capAffine j odd ⟨a.val, by omega⟩
    p.1 * (k : ℤ) + p.2
  else if htail : order k - 21 ≤ a.val then
    let i : Fin 36 := ⟨a.val - (order k - 21) + 15, by
      have := a.isLt
      dsimp [order] at *
      omega⟩
    let p := capAffine j odd i
    p.1 * (k : ℤ) + p.2
  else
    bulkColumnRaw k j ((a.val - 15) / 4) ((a.val - 15) % 4)

def symbolRaw (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) (a : Fin (order k)) : ℤ :=
  let odd := k % 2 = 1
  if h : a.val < 15 then
    (a.val : ℤ) + columnRaw k hk j a + capEpsilon j ⟨a.val, by omega⟩
  else if order k - 21 ≤ a.val then
    (a.val : ℤ) + columnRaw k hk j a
  else
    bulkSymbolRaw k j ((a.val - 15) / 4) ((a.val - 15) % 4)

def column (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) (a : Fin (order k)) :
    Fin (order k) := residue k hk (columnRaw k hk j a)

def symbol (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) (a : Fin (order k)) :
    Fin (order k) := residue k hk (symbolRaw k hk j a)

def entry (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) (a : Fin (order k)) :
    Fin (order k) × Fin (order k) × Fin (order k) :=
  (a, column k hk j a, symbol k hk j a)

def T (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) :
    Set (Fin (order k) × Fin (order k) × Fin (order k)) :=
  Set.range (entry k hk j)

def d0 (k : ℕ) (hk : 9 ≤ k) :
    Fin (order k) × Fin (order k) × Fin (order k) :=
  (residue k hk 1, residue k hk 1, residue k hk 5)

def d1 (k : ℕ) (hk : 9 ≤ k) :
    Fin (order k) × Fin (order k) × Fin (order k) :=
  (residue k hk 6, residue k hk 5, residue k hk 14)

def d2 (k : ℕ) (hk : 9 ≤ k) :
    Fin (order k) × Fin (order k) × Fin (order k) :=
  (residue k hk 11, residue k hk 9, residue k hk 23)

def D (k : ℕ) (hk : 9 ≤ k) :
    Finset (Fin (order k) × Fin (order k) × Fin (order k)) :=
  {d0 k hk, d1 k hk, d2 k hk}

def IsTransversal (k : ℕ) (hk : 9 ≤ k)
    (T : Set (Fin (order k) × Fin (order k) × Fin (order k))) : Prop :=
  (∀ e ∈ T, e.2.2 = square k hk e.1 e.2.1) ∧
  (∀ a, ∃! e, e ∈ T ∧ e.1 = a) ∧
  (∀ b, ∃! e, e ∈ T ∧ e.2.1 = b) ∧
  (∀ c, ∃! e, e ∈ T ∧ e.2.2 = c)

def IsPinned (k : ℕ) (hk : 9 ≤ k)
    (e : Fin (order k) × Fin (order k) × Fin (order k)) : Prop :=
  (∃ T, IsTransversal k hk T) ∧ ∀ T, IsTransversal k hk T → e ∈ T

def bulkRow (k : ℕ) (hk : 9 ≤ k) (t : Fin (k - 9)) (r : Fin 4) :
    Fin (order k) :=
  ⟨15 + 4 * t.val + r.val, by
    have ht := t.isLt
    have hr := r.isLt
    dsimp [order]
    omega⟩


def headRow (k : ℕ) (hk : 9 ≤ k) (i : Fin 15) : Fin (order k) :=
  ⟨i.val, by dsimp [order]; omega⟩


def tailRow (k : ℕ) (hk : 9 ≤ k) (i : Fin 21) : Fin (order k) :=
  ⟨order k - 21 + i.val, by dsimp [order]; omega⟩

def capRow (k : ℕ) (hk : 9 ≤ k) (i : Fin 36) : Fin (order k) :=
  ⟨if i.val < 15 then i.val else order k - 36 + i.val, by
    have := i.isLt
    dsimp [order]
    split_ifs <;> omega⟩

set_option maxHeartbeats 3000000 in
/-- Summing the actual priority increments forces at least two distinguished entries in every transversal. -/
theorem transversal_obstruction (k : ℕ) (hk : 9 ≤ k)
    (S : Set (Fin (order k) × Fin (order k) × Fin (order k)))
    (hS : IsTransversal k hk S) :
    2 ≤ {f | f ∈ D k hk ∧ f ∈ S}.ncard := by
  classical
  have hncard : {f | f ∈ D k hk ∧ f ∈ S}.ncard =
      ((D k hk).filter (fun f => f ∈ S)).card := by
    rw [show {f | f ∈ D k hk ∧ f ∈ S} =
      (↑((D k hk).filter (fun f => f ∈ S)) : Set _) by ext; simp]
    exact Set.ncard_coe_finset _
  rw [hncard]
  let e (a : Fin (order k)) := Classical.choose (hS.2.1 a)
  have he (a : Fin (order k)) : e a ∈ S ∧ (e a).1 = a :=
    (Classical.choose_spec (hS.2.1 a)).1
  have hunique (a : Fin (order k)) (f : Fin (order k) × Fin (order k) × Fin (order k))
      (hf : f ∈ S) (hr : f.1 = a) : f = e a :=
    (Classical.choose_spec (hS.2.1 a)).2 f ⟨hf,hr⟩
  have hei : Function.Injective e := by
    intro a b hab
    have h := congrArg Prod.fst hab
    simpa only [(he a).2, (he b).2] using h
  have hcoord (g : (Fin (order k) × Fin (order k) × Fin (order k)) → Fin (order k))
      (hg : ∀ x, ∃! f, f ∈ S ∧ g f = x) : Function.Bijective (fun a => g (e a)) := by
    constructor
    · intro a b hab
      obtain ⟨f,hf,hfuniq⟩ := hg (g (e a))
      have ha : e a = f := hfuniq _ ⟨(he a).1,rfl⟩
      have hb : e b = f := hfuniq _ ⟨(he b).1,hab.symm⟩
      exact hei (ha.trans hb.symm)
    · intro x
      obtain ⟨f,hf,_⟩ := hg x
      refine ⟨f.1, ?_⟩
      change g (e f.1) = x
      rw [← hunique f.1 f hf.1 rfl]
      exact hf.2
  have hc := hcoord (fun f => f.2.1) hS.2.2.1
  have hz := hcoord (fun f => f.2.2) hS.2.2.2
  let R : ℤ := ∑ a : Fin (order k), (a.val : ℤ)
  let charge : ℤ := ∑ a : Fin (order k), delta k a (e a).2.1
  have hR : R = 2 * (k : ℤ) * (4 * (k : ℤ) - 1) := by
    have hgauss := Finset.sum_range_id_mul_two (order k)
    have hgaussInt := congrArg (fun z : ℕ => (z : ℤ)) hgauss
    have horder : 1 ≤ order k := by dsimp [order]; omega
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum,
      Nat.cast_sub horder] at hgaussInt
    have hrange : R = ∑ a ∈ Finset.range (order k), (a : ℤ) :=
      Fin.sum_univ_eq_sum_range (fun a => (a : ℤ)) (order k)
    rw [← hrange] at hgaussInt
    dsimp [order] at hgaussInt
    push_cast at hgaussInt
    nlinarith
  have hmod : charge ≡ 2 * (k : ℤ) [ZMOD (order k : ℤ)] := by
    have hrow (a : Fin (order k)) :
        delta k a (e a).2.1 ≡
          ((e a).2.2.val : ℤ) - (a.val : ℤ) - ((e a).2.1.val : ℤ)
            [ZMOD (order k : ℤ)] := by
      have hsource := hS.1 (e a) (he a).1
      rw [(he a).2] at hsource
      have hval := congrArg (fun z : Fin (order k) => (z.val : ℤ)) hsource
      have hnonneg : 0 ≤ ((a.val : ℤ) + ((e a).2.1.val : ℤ) +
          delta k a (e a).2.1) % (order k : ℤ) :=
        Int.emod_nonneg _ (by dsimp [order]; omega)
      have hb : ((e a).2.2.val : ℤ) < order k := by exact_mod_cast (e a).2.2.isLt
      have ht : (a.val : ℤ) + ((e a).2.1.val : ℤ) + delta k a (e a).2.1 ≡
          ((e a).2.2.val : ℤ) [ZMOD (order k : ℤ)] := by
        change _ % _ = _ % _
        rw [Int.emod_eq_of_lt (by omega) hb]
        simpa [square, residue, Int.toNat_of_nonneg hnonneg] using hval.symm
      have ht' := (ht.sub (Int.ModEq.refl (a.val : ℤ))).sub
        (Int.ModEq.refl ((e a).2.1.val : ℤ))
      convert ht' using 1 <;> ring
    have hsum := Int.ModEq.sum (s := Finset.univ) (fun a _ => hrow a)
    have hcsum : (∑ a : Fin (order k), ((e a).2.1.val : ℤ)) = R := hc.sum_comp (fun b => (b.val : ℤ))
    have hzsum : (∑ a : Fin (order k), ((e a).2.2.val : ℤ)) = R := hz.sum_comp (fun b => (b.val : ℤ))
    have hsum' : charge ≡ -R [ZMOD (order k : ℤ)] := by
      simpa [charge, Finset.sum_sub_distrib, hcsum, hzsum, R] using hsum
    apply hsum'.trans
    rw [hR]
    have hexpr : -(2 * (k : ℤ) * (4 * (k : ℤ) - 1)) =
        2 * (k : ℤ) + (order k : ℤ) * (-2 * (k : ℤ)) := by dsimp [order]; push_cast; ring
    rw [hexpr]
    exact Int.modEq_add_fac_self
  let A0 : Finset (Fin (order k)) := {headRow k hk 0, headRow k hk 5, headRow k hk 10}
  let A1 : Finset (Fin (order k)) := {headRow k hk 1, headRow k hk 6, headRow k hk 11}
  let A4 : Finset (Fin (order k)) := {headRow k hk 4, headRow k hk 9, headRow k hk 14}
  let B (r : Fin 4) := Finset.univ.image (fun t : Fin (k - 9) => bulkRow k hk t r)
  have hA0 (a : Fin (order k)) : a ∈ A0 ↔ a.val = 0 ∨ a.val = 5 ∨ a.val = 10 := by
    simp [A0, Fin.ext_iff, headRow]
  have hA1 (a : Fin (order k)) : a ∈ A1 ↔ a.val = 1 ∨ a.val = 6 ∨ a.val = 11 := by
    simp [A1, Fin.ext_iff, headRow]
  have hA4 (a : Fin (order k)) : a ∈ A4 ↔ a.val = 4 ∨ a.val = 9 ∨ a.val = 14 := by
    simp [A4, Fin.ext_iff, headRow]
  have hB (r : Fin 4) (a : Fin (order k)) :
      a ∈ B r ↔ 15 ≤ a.val ∧ a.val < order k - 21 ∧ a.val % 4 = (3+r.val)%4 := by
    simp only [B, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t,rfl⟩
      have := t.isLt
      have := r.isLt
      dsimp [bulkRow,order]
      omega
    · intro ha
      let t : Fin (k - 9) := ⟨(a.val-15)/4, by dsimp [order] at *; omega⟩
      refine ⟨t, ?_⟩
      apply Fin.ext
      have := r.isLt
      dsimp [bulkRow,t]
      omega
  have hBcard (r : Fin 4) : (B r).card = k - 9 := by
    have hi : Function.Injective (fun t : Fin (k - 9) => bulkRow k hk t r) := by
      intro t u h
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [bulkRow] at hv
      omega
    simp [B, Finset.card_image_of_injective _ hi]
  have hsumIndicator (A : Finset (Fin (order k))) :
      (∑ a : Fin (order k), if a ∈ A then (1 : ℤ) else 0) = A.card := by
    simp
  let lo (a : Fin (order k)) : ℤ :=
    -(if a ∈ A1 then 1 else 0) - 4*(if a ∈ A4 then 1 else 0) - 2*(if a ∈ B 2 then 1 else 0)
  let hi (a : Fin (order k)) : ℤ :=
    4*(if a ∈ A0 then 1 else 0) + 2*(if a ∈ B 0 then 1 else 0)
  have hlo (a : Fin (order k)) : lo a ≤ delta k a (e a).2.1 := by
    simp only [lo,hA1,hA4,hB]
    norm_num
    dsimp only [delta]
    split_ifs <;> omega
  have hres (z : ℤ) (h0 : 0 ≤ z) (hlt : z < order k) :
      ((residue k hk z).val : ℤ) = z := by
    simp [residue,Int.emod_eq_of_lt h0 hlt,Int.toNat_of_nonneg h0]
  have hdist (a : Fin (order k))
      (h : (a.val = 1 ∧ (e a).2.1.val = 1) ∨
        (a.val = 6 ∧ (e a).2.1.val = 5) ∨
        (a.val = 11 ∧ (e a).2.1.val = 9)) : e a ∈ D k hk := by
    have hsource := hS.1 (e a) (he a).1
    rw [(he a).2] at hsource
    have hrow := congrArg Fin.val (he a).2
    rcases h with h | h | h
    all_goals have hdelta : delta k a (e a).2.1 = 3 := by simp [delta,h.1,h.2]
    all_goals simp only [square,hdelta] at hsource
    all_goals simp only [h.1,h.2, Nat.cast_ofNat] at hsource
    all_goals norm_num only at hsource
    all_goals have hsymbol := congrArg (fun z : Fin (order k) => (z.val : ℤ)) hsource
    all_goals simp only [D,Finset.mem_insert,Finset.mem_singleton]
    · left
      simp only [d0,Prod.ext_iff,Fin.ext_iff]
      have hv1 := hres 1 (by omega) (by dsimp [order]; omega)
      have hv5 := hres 5 (by omega) (by dsimp [order]; omega)
      have hz5 : ((e a).2.2.val : ℤ) = 5 := by simpa [hv5] using hsymbol
      omega
    · right; left
      simp only [d1,Prod.ext_iff,Fin.ext_iff]
      have hv6 := hres 6 (by omega) (by dsimp [order]; omega)
      have hv5 := hres 5 (by omega) (by dsimp [order]; omega)
      have hv14 := hres 14 (by omega) (by dsimp [order]; omega)
      have hz14 : ((e a).2.2.val : ℤ) = 14 := by simpa [hv14] using hsymbol
      omega
    · right; right
      simp only [d2,Prod.ext_iff,Fin.ext_iff]
      have hv11 := hres 11 (by omega) (by dsimp [order]; omega)
      have hv9 := hres 9 (by omega) (by dsimp [order]; omega)
      have hv23 := hres 23 (by omega) (by dsimp [order]; omega)
      have hz23 : ((e a).2.2.val : ℤ) = 23 := by simpa [hv23] using hsymbol
      omega
  have hhi (a : Fin (order k)) :
      delta k a (e a).2.1 ≤ hi a + 3*(if e a ∈ D k hk then 1 else 0) := by
    have hd := hdist a
    simp only [hi,hA0,hB]
    norm_num
    dsimp only [delta]
    split_ifs <;> simp_all <;> omega
  have hAs : A0.card = 3 ∧ A1.card = 3 ∧ A4.card = 3 := by
    simp [A0,A1,A4,Fin.ext_iff,headRow]
  have hlosum : (∑ a : Fin (order k), lo a) = -2*(k : ℤ)+3 := by
    simp only [lo, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum, hsumIndicator, hAs, hBcard]
    have hsub : ((k-9 : ℕ) : ℤ) = (k : ℤ)-9 := by omega
    rw [hsub]
    ring
  have hhisum : (∑ a : Fin (order k), hi a) = 2*(k : ℤ)-6 := by
    simp only [hi, Finset.sum_add_distrib, ← Finset.mul_sum, hsumIndicator, hAs, hBcard]
    have hsub : ((k-9 : ℕ) : ℤ) = (k : ℤ)-9 := by omega
    rw [hsub]
    ring
  let chosen := Finset.univ.filter (fun a => e a ∈ D k hk)
  have hchosen : chosen.card ≤ ((D k hk).filter (fun f => f ∈ S)).card := by
    have himage : chosen.image e ⊆ (D k hk).filter (fun f => f ∈ S) := by
      intro f hf
      rcases Finset.mem_image.mp hf with ⟨a,ha,rfl⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).2,(he a).1⟩
    have hh := Finset.card_le_card himage
    rwa [Finset.card_image_of_injective _ hei] at hh
  have hchosenSum : (∑ a : Fin (order k), if e a ∈ D k hk then (1 : ℤ) else 0) =
      chosen.card := by simp [chosen]
  have hlobound : -2*(k : ℤ)+3 ≤ charge := by
    rw [← hlosum]
    exact Finset.sum_le_sum (fun a _ => hlo a)
  have hhibound : charge ≤ 2*(k : ℤ)-6+3*(chosen.card : ℤ) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hhi a)
    simpa only [charge, Finset.sum_add_distrib, ← Finset.mul_sum, hhisum, hchosenSum] using hh
  by_contra hbad
  have hone : chosen.card ≤ 1 := by omega
  have hub : charge ≤ 2*(k : ℤ)-3 := by omega
  have hmodEq : charge % (order k : ℤ) = 2*(k : ℤ) := by
    exact (show charge % (order k : ℤ) = (2*(k : ℤ)) % (order k : ℤ) from hmod).trans
      (Int.emod_eq_of_lt (by omega) (by dsimp [order]; omega))
  by_cases hnonneg : 0 ≤ charge
  · rw [Int.emod_eq_of_lt hnonneg (by dsimp [order]; omega)] at hmodEq
    omega
  · have hshift : (charge+(order k : ℤ)) % (order k : ℤ) = charge % (order k : ℤ) := by simp
    rw [Int.emod_eq_of_lt (by dsimp [order]; omega)
      (by dsimp [order]; omega)] at hshift
    have ho : (order k : ℤ) = 4*(k : ℤ) := by simp [order]
    rw [ho] at hshift hmodEq
    omega

#print axioms transversal_obstruction

end D5.S3.Combinatorics.LatinHTransversals
