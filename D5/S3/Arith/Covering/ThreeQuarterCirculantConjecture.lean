/- GID: D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture
   generality: I
   mirror-B: D5/B/S3/Arith/Covering/ThreeQuarterCirculantConjecture
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Sector radius, integer lattice, and degree boundary for Conjecture 2.4. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Covering.ThreeQuarterCirculantConjecture

/-
proof_shape: kernel_eq_generated: content; sector_cover: content;
  sector_radius_lower: content; generator_regular_for_k_ge_two: content
escape_witness: the public conclusions directly use an integer-kernel decomposition,
  quotient/remainder sector witnesses, a three-sector lower-radius bound, and a
  modular separation bound, respectively
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only)
-/

/-- The three sign sectors in the source definition; representations may overlap. -/
def SectorReach (N : ℕ) (a b : ZMod N) (r : ℕ) (z : ZMod N) : Prop :=
  ∃ m n : ℕ, m + n ≤ r ∧
    (z = (m : ZMod N) * a + (n : ZMod N) * b ∨
     z = -(m : ZMod N) * a + (n : ZMod N) * b ∨
     z = (m : ZMod N) * a - (n : ZMod N) * b)

/-- The order in Conjecture 2.4, written to expose the last quotient block. -/
def order (k : ℕ) : ℕ := (k - 1) * (k + 4) + (k + 2)

def stepB (k : ℕ) : ZMod (order k) := -(k + 4 : ℕ)

def sector (k r : ℕ) (z : ZMod (order k)) : Prop :=
  SectorReach (order k) 1 (stepB k) r z

/-- The two columns displayed in Conjecture 2.4. -/
def latticeFirst (k : ℕ) : ℤ × ℤ := ((k : ℤ) + 2, 1 - (k : ℤ))
def latticeSecond (k : ℕ) : ℤ × ℤ := (2, (k : ℤ))

def integerKernel (k : ℕ) : Set (ℤ × ℤ) :=
  {p | (((p.1 : ZMod (order k)) + p.2 * stepB k) : ZMod (order k)) = 0}

def generatedLattice (k : ℕ) : Set (ℤ × ℤ) :=
  {p | ∃ s t : ℤ, p = (s * (latticeFirst k).1 + t * (latticeSecond k).1,
                         s * (latticeFirst k).2 + t * (latticeSecond k).2)}

/-- Every congruence-kernel point is an integral combination of the source columns. -/
theorem kernel_eq_generated (k : ℕ) (hk : 1 ≤ k) :
    order k = k ^ 2 + 4 * k - 2 ∧
    (latticeFirst k).1 * (latticeSecond k).2 -
      (latticeSecond k).1 * (latticeFirst k).2 = (order k : ℤ) ∧
    integerKernel k = generatedLattice k := by
  have horder : order k = k ^ 2 + 4 * k - 2 := by
    have h : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hcalc : order k + 2 = k ^ 2 + 4 * k := by
      dsimp [order]
      nlinarith [h]
    omega
  have hdet : (latticeFirst k).1 * (latticeSecond k).2 -
      (latticeSecond k).1 * (latticeFirst k).2 = (order k : ℤ) := by
    have h : k - 1 + 1 = k := Nat.sub_add_cancel hk
    dsimp [latticeFirst, latticeSecond, order]
    nlinarith
  refine ⟨horder, hdet, ?_⟩
  ext p
  obtain ⟨x, y⟩ := p
  have hfirst : (latticeFirst k).1 - (k + 4 : ℤ) * (latticeFirst k).2 =
      (order k : ℤ) := by
    have h := hdet
    dsimp [latticeFirst, latticeSecond] at h ⊢
    nlinarith
  have hsecond : (latticeSecond k).1 - (k + 4 : ℤ) * (latticeSecond k).2 =
      -(order k : ℤ) := by
    have h := hdet
    dsimp [latticeFirst, latticeSecond] at h ⊢
    nlinarith
  change ((x : ZMod (order k)) + (y : ZMod (order k)) * stepB k = 0) ↔
    ∃ s t : ℤ, (x, y) =
      (s * (latticeFirst k).1 + t * (latticeSecond k).1,
       s * (latticeFirst k).2 + t * (latticeSecond k).2)
  have hkernel : (x : ZMod (order k)) + (y : ZMod (order k)) * stepB k = 0 ↔
      (order k : ℤ) ∣ x - (k + 4 : ℤ) * y := by
    have heq : (x : ZMod (order k)) + (y : ZMod (order k)) * stepB k =
        ((x - (k + 4 : ℤ) * y : ℤ) : ZMod (order k)) := by
      dsimp [stepB]
      push_cast
      ring
    rw [heq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [hkernel]
  constructor
  · rintro ⟨s, hs⟩
    let t : ℤ := y + (k - 1 : ℕ) * s
    refine ⟨y + k * s, t, ?_⟩
    have hn : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hkm1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
      have hi : ((k - 1 : ℕ) : ℤ) + 1 = (k : ℤ) := by exact_mod_cast hn
      omega
    apply Prod.ext
    · dsimp [latticeFirst, latticeSecond, t]
      have hd := hdet
      dsimp [latticeFirst, latticeSecond] at hd
      have hcoeff : ((k : ℤ) + 2) * k + 2 * ((k : ℤ) - 1) = (order k : ℤ) := by
        nlinarith [hd]
      have hnormal : (y + (k : ℤ) * s) * ((k : ℤ) + 2) +
          (y + ((k - 1 : ℕ) : ℤ) * s) * 2 =
          ((k : ℤ) + 4) * y + (order k : ℤ) * s := by
        rw [hkm1, ← hcoeff]
        ring
      calc
        x = ((k : ℤ) + 4) * y + (order k : ℤ) * s := by linear_combination hs
        _ = _ := hnormal.symm
    · dsimp [latticeFirst, latticeSecond, t]
      rw [hkm1]
      ring
  · rintro ⟨s, t, heq⟩
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    dsimp at hx hy
    use s - t
    rw [hx, hy]
    calc
      (s * (latticeFirst k).1 + t * (latticeSecond k).1) -
          (k + 4 : ℤ) * (s * (latticeFirst k).2 + t * (latticeSecond k).2) =
          s * ((latticeFirst k).1 - (k + 4 : ℤ) * (latticeFirst k).2) +
          t * ((latticeSecond k).1 - (k + 4 : ℤ) * (latticeSecond k).2) := by ring
      _ = s * (order k : ℤ) + t * (-(order k : ℤ)) := by rw [hfirst, hsecond]
      _ = (order k : ℤ) * (s - t) := by ring

/-- Every residue has a source-sector representation of radius at most `k`. -/
theorem sector_cover (k : ℕ) (hk : 1 ≤ k) :
    ∀ z : ZMod (order k), sector k k z := by
  intro z
  let q := k - 1
  let c := k + 4
  let d := k + 2
  let N := order k
  let w := z.val
  let n := w / c
  let r := w % c
  have hc : 0 < c := by dsimp [c]; omega
  have hd : d < c := by dsimp [d, c]; omega
  have hN : N = q * c + d := rfl
  have hNpos : 0 < N := by rw [hN]; dsimp [d]; omega
  letI : NeZero (order k) := ⟨Nat.ne_of_gt hNpos⟩
  have hNlt : N < (q + 1) * c := by rw [hN]; nlinarith
  have hwlt : w < N := ZMod.val_lt z
  have hn : n ≤ q := by
    have h : w / c < q + 1 := (Nat.div_lt_iff_lt_mul hc).2 (lt_trans hwlt hNlt)
    dsimp [n]
    omega
  have hr : r < c := Nat.mod_lt _ hc
  have hw : w = n * c + r := by
    dsimp [n, c, r]
    simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div w (k + 4)).symm
  by_cases hright : r ≤ k - n
  · have hrad : r + n ≤ k := by dsimp [q] at hn; omega
    refine ⟨r, n, hrad, Or.inr (Or.inr ?_)⟩
    change z = (r : ZMod N) * 1 - (n : ZMod N) * stepB k
    rw [← ZMod.natCast_zmod_val z]
    change (w : ZMod N) = _
    rw [hw]
    simp only [Nat.cast_add, Nat.cast_mul, mul_one, stepB, mul_neg]
    dsimp [c]
    push_cast
    ring
  · let j := q - n
    have hj : j + n = q := Nat.sub_add_cancel hn
    have hjc : j * c + n * c = q * c := by
      calc
        j * c + n * c = (j + n) * c := by ring
        _ = q * c := by rw [hj]
    have hgap : k - n < r := by omega
    by_cases hleft : r ≤ d
    · let m := d - r
      have hm : m ≤ n + 1 := by dsimp [m, d, q] at *; omega
      have hrad : m + j ≤ k := by dsimp [q] at hj ⊢; omega
      have heq : w + j * c + m = N := by rw [hN]; dsimp [m] at *; omega
      refine ⟨m, j, hrad, Or.inr (Or.inl ?_)⟩
      change z = -(m : ZMod N) * 1 + (j : ZMod N) * stepB k
      rw [← ZMod.natCast_zmod_val z]
      change (w : ZMod N) = _
      have hcast := congrArg (fun a : ℕ => (a : ZMod N)) heq
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self] at hcast
      dsimp [stepB]
      linear_combination hcast
    · let m := r - d
      have hm : m ≤ 1 := by
        dsimp [m]
        have hcd : c = d + 2 := by dsimp [c, d]
        omega
      have hq : q + 1 = k := Nat.sub_add_cancel hk
      have hjle : j ≤ q := Nat.le.intro hj
      have hrad : m + j ≤ k := by
        calc
          m + j ≤ 1 + j := Nat.add_le_add_right hm j
          _ ≤ 1 + q := Nat.add_le_add_left hjle 1
          _ = k := by omega
      have heq : w + j * c = N + m := by rw [hN]; dsimp [m] at *; omega
      refine ⟨m, j, hrad, Or.inl ?_⟩
      change z = (m : ZMod N) * 1 + (j : ZMod N) * stepB k
      rw [← ZMod.natCast_zmod_val z]
      change (w : ZMod N) = _
      have hcast := congrArg (fun a : ℕ => (a : ZMod N)) heq
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_add] at hcast
      dsimp [stepB]
      linear_combination hcast

/-- The residue `k` needs all `k` steps in the paper's three-sector distance. -/
theorem sector_radius_lower (k : ℕ) (hk : 1 ≤ k) :
    ¬ sector k (k - 1) (k : ZMod (order k)) := by
  let q := k - 1
  let c := k + 4
  let d := k + 2
  let N := order k
  have hN : N = q * c + d := rfl
  have hNpos : 0 < N := by rw [hN]; dsimp [d]; omega
  letI : NeZero (order k) := ⟨Nat.ne_of_gt hNpos⟩
  have hkN : k < N := by rw [hN]; dsimp [d]; omega
  have hc : 0 < c := by dsimp [c]; omega
  have hstep : stepB k = -(c : ZMod N) := rfl
  have cast_inj (u v : ℕ) (hu : u < N) (hv : v < N)
      (heq : (u : ZMod N) = (v : ZMod N)) : u = v := by
    have hmod := (ZMod.natCast_eq_natCast_iff' u v N).mp heq
    simpa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] using hmod
  intro hreach
  change SectorReach N 1 (stepB k) q (k : ZMod N) at hreach
  obtain ⟨m, n, hrad, hsector⟩ := hreach
  have hmq : m ≤ q := Nat.le_trans (Nat.le_add_right m n) hrad
  have hqk : q < k := by dsimp [q]; omega
  have hmc : m ≤ m * c := Nat.le_mul_of_pos_right m hc
  have hmul : (m + n) * c ≤ q * c := Nat.mul_le_mul_right c hrad
  have hH : m + n * c ≤ q * c := by
    have ha : m * c + n * c = (m + n) * c := by ring
    omega
  have hHlt : m + n * c < N := by rw [hN]; omega
  have hknc : k + n * c < N := by rw [hN]; dsimp [d]; omega
  have hkH : k + m + n * c < N := by rw [hN]; dsimp [d]; omega
  have hmlt : m < N := by omega
  rcases hsector with hfirst | hsecond | hthird
  · have hcast : ((k + n * c : ℕ) : ZMod N) = (m : ZMod N) := by
      change (k : ZMod N) = (m : ZMod N) * 1 + (n : ZMod N) * stepB k at hfirst
      simp only [hstep, mul_one, mul_neg] at hfirst
      push_cast
      linear_combination hfirst
    have heq := cast_inj (k + n * c) m hknc hmlt hcast
    omega
  · have hzero : ((k + m + n * c : ℕ) : ZMod N) = 0 := by
      change (k : ZMod N) = -(m : ZMod N) * 1 + (n : ZMod N) * stepB k at hsecond
      simp only [hstep, mul_one, mul_neg] at hsecond
      push_cast
      linear_combination hsecond
    have hdvd : N ∣ k + m + n * c :=
      (ZMod.natCast_eq_zero_iff (k + m + n * c) N).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hkH) hdvd
  · have hcast : (k : ZMod N) = ((m + n * c : ℕ) : ZMod N) := by
      change (k : ZMod N) = (m : ZMod N) * 1 - (n : ZMod N) * stepB k at hthird
      simp only [hstep, mul_one, mul_neg] at hthird
      push_cast
      linear_combination hthird
    have heq := cast_inj k (m + n * c) hkN hHlt hcast
    by_cases hn0 : n = 0
    · subst n
      simp only [zero_mul, add_zero] at heq
      omega
    · have hnpos : 1 ≤ n := by omega
      have hcn : c ≤ n * c := by
        calc
          c = 1 * c := by ring
          _ ≤ n * c := Nat.mul_le_mul_right c hnpos
      have hck : k < c := by dsimp [c]; omega
      omega

/-- For `k ≥ 2`, the two source steps are nonzero, distinct, and give degree two. -/
theorem generator_regular_for_k_ge_two (k : ℕ) (hk : 2 ≤ k) :
    (1 : ZMod (order k)) ≠ 0 ∧
    stepB k ≠ 0 ∧
    (1 : ZMod (order k)) ≠ stepB k ∧
    ∀ z : ZMod (order k),
      ({z + 1, z + stepB k} : Finset (ZMod (order k))).card = 2 := by
  have hq : 1 ≤ k - 1 := by omega
  have hmul : k + 4 ≤ (k - 1) * (k + 4) := by
    calc
      k + 4 = 1 * (k + 4) := by ring
      _ ≤ (k - 1) * (k + 4) := Nat.mul_le_mul_right _ hq
  have hgt : k + 5 < order k := by dsimp [order]; omega
  have hcgt : k + 4 < order k := by omega
  have h1gt : 1 < order k := by omega
  have ha : (1 : ZMod (order k)) ≠ 0 := by
    intro h
    have hdvd : order k ∣ 1 := (ZMod.natCast_eq_zero_iff 1 (order k)).mp h
    exact (Nat.not_dvd_of_pos_of_lt (by omega) h1gt) hdvd
  have hb : stepB k ≠ 0 := by
    intro h
    have hz : ((k + 4 : ℕ) : ZMod (order k)) = 0 := by
      change -((k + 4 : ℕ) : ZMod (order k)) = 0 at h
      exact neg_eq_zero.mp h
    have hdvd : order k ∣ k + 4 :=
      (ZMod.natCast_eq_zero_iff (k + 4) (order k)).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hcgt) hdvd
  have hab : (1 : ZMod (order k)) ≠ stepB k := by
    intro h
    have hsum : (1 : ZMod (order k)) + (k + 4 : ZMod (order k)) = 0 := by
      rw [h]
      simp [stepB]
    have hz : ((k + 5 : ℕ) : ZMod (order k)) = 0 := by
      convert hsum using 1
      push_cast
      ring
    have hdvd : order k ∣ k + 5 :=
      (ZMod.natCast_eq_zero_iff (k + 5) (order k)).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hgt) hdvd
  refine ⟨ha, hb, hab, ?_⟩
  intro z
  have hneq : z + 1 ≠ z + stepB k := by
    intro h
    exact hab (add_left_cancel h)
  simp [hneq]

end D5.S3.Arith.Covering.ThreeQuarterCirculantConjecture
