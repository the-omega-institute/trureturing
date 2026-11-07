/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/Binary
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 PermutationStabilizer Binary on original physical labels. -/
/- Source only: not elaborated or kernel checked. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer.Basic
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
open scoped BigOperators
open SourceWidth ZeroSumSubsets
open D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer
  (place slice sum_slices)
open private top_floors bit
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer.Basic

def digit (z : ℤ) (j : ℕ) : ℤ := z / (2 : ℤ)^j % 2

private theorem digit_cases (z : ℤ) (j : ℕ) :
    digit z j = 0 ∨ digit z j = 1 := by
  have h0 := Int.emod_nonneg (z / (2 : ℤ)^j) (by norm_num : (2 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos (z / (2 : ℤ)^j) (by norm_num : (0 : ℤ) < 2)
  dsimp [digit]
  omega

def read {A : Type*} [AddCommGroup A]
    (d : ℕ) (f : ℕ → A) (z : ℤ) : A :=
  ∑ j : Fin d, digit z j.val • f j.val

private theorem digit_succ (z : ℤ) (j : ℕ) :
    digit z (j+1) = digit (z/2) j := by
  unfold digit
  rw [Int.ediv_ediv_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)]
  congr 2
  rw [pow_succ']

theorem read_succ {A : Type*} [AddCommGroup A] (d : ℕ) (f : ℕ → A) (z : ℤ) :
    read (d+1) f z = (z%2 : ℤ) • f 0 + read d (fun i => f (i+1)) (z/2) := by
  simp only [read, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    digit_succ]
  simp only [digit, pow_zero, Int.ediv_one]

theorem read_congr {A : Type*} [AddCommGroup A] (d : ℕ) (f g : ℕ → A) (z : ℤ)
    (h : ∀ j, j<d → f j=g j) : read d f z=read d g z := by
  apply Finset.sum_congr rfl
  intro j _
  rw [h j.val j.isLt]

theorem read_add {A : Type*} [AddCommGroup A] (d : ℕ) (f g : ℕ → A) (z : ℤ) :
    read d (fun j => f j+g j) z = read d f z+read d g z := by
  simp [read, smul_add, Finset.sum_add_distrib]

private theorem read_scale {R : Type*} [CommRing R] (d : ℕ) (c : R) (f : ℕ → R) (z : ℤ) :
    read d (fun j => c*f j) z=c*read d f z := by
  simp [read, zsmul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem read_sub {A : Type*} [AddCommGroup A] (d : ℕ) (f g : ℕ → A) (z : ℤ) :
    read d (fun j => f j-g j) z = read d f z-read d g z := by
  simp [read, smul_sub, Finset.sum_sub_distrib]

theorem read_unit {R : Type*} [CommRing R] (d k : ℕ) (z : ℤ) (hk : k<d) :
    read d (fun j => if j=k then 1 else 0) z=(digit z k : R) := by
  classical
  have he (j : Fin d) : j.val=k ↔ j=⟨k,hk⟩ :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp [read, zsmul_eq_mul, he]

theorem read_geom {R : Type*} [CommRing R] (d : ℕ) (z : ℤ)
    (hz0 : 0≤z) (hz1 : z<(2 : ℤ)^d) :
    read d (fun j => (2 : R)^j) z=(z : R) := by
  induction d generalizing z with
  | zero =>
      have : z=0 := by norm_num at hz1; omega
      subst z
      simp [read]
  | succ d ih =>
      have hq0 : 0≤z/2 := Int.ediv_nonneg hz0 (by norm_num)
      have hq1 : z/2<(2 : ℤ)^d := by
        rw [pow_succ] at hz1
        omega
      rw [read_succ]
      simp only [zsmul_eq_mul]
      have hs : read d (fun i => (2 : R)^(i+1)) (z/2) =
          2*read d (fun i => (2 : R)^i) (z/2) := by
        simpa only [pow_succ, mul_comm] using
          read_scale d 2 (fun i => (2 : R)^i) (z/2)
      rw [hs, ih (z/2) hq0 hq1]
      have he : ((z%2 : ℤ) : R)+2*((z/2 : ℤ) : R)=(z : R) := by
        have hi := congrArg (fun t : ℤ => (t : R)) (Int.emod_add_mul_ediv z 2)
        simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hi
      simpa using he

/-- The exact signed binary carry, valid even before imposing a digit bound.
The argument uses no valuation API and no finite certificate. -/
private theorem read_carry {A : Type*} [AddCommGroup A] (d j : ℕ) (f : ℕ → A) (k : ℤ) (hj : j<d) :
    read d f ((2 : ℤ)^j*(2*k+1)) -
      read d f ((2 : ℤ)^j*(2*k+1)-1) =
        f j - ∑ i : Fin j, f i.val := by
  induction j generalizing d f with
  | zero =>
      obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
      have he : ((2*k+1)%2 : ℤ)=1 := by omega
      have he' : ((2*k+1-1)%2 : ℤ)=0 := by omega
      have hq : (2*k+1)/2=k := by omega
      have hq' : (2*k+1-1)/2=k := by omega
      simp [read_succ, he, he', hq, hq']
  | succ j ih =>
      obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
      let z : ℤ := (2 : ℤ)^j*(2*k+1)
      have hp : (2 : ℤ)^(j+1)*(2*k+1)=2*z := by dsimp [z]; ring
      have he : (2*z)%2=0 := by omega
      have he' : (2*z-1)%2=1 := by omega
      have hq : (2*z)/2=z := by omega
      have hq' : (2*z-1)/2=z-1 := by omega
      rw [hp, read_succ, read_succ, he, he', hq, hq']
      have hc := ih d (fun i => f (i+1)) (by omega)
      change read d (fun i => f (i+1)) z -
        read d (fun i => f (i+1)) (z-1) = _ at hc
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ]
      norm_num only [zero_smul, one_smul, zero_add]
      linear_combination (norm := abel) hc

private theorem read_carry_mod {A : Type*} [AddCommGroup A] (d j : ℕ) (f : ℕ → A) (z : ℤ)
    (hj : j<d) (hz : z%(2 : ℤ)^(j+1)=(2 : ℤ)^j) :
    read d f z-read d f (z-1)=f j-∑ i : Fin j, f i.val := by
  let k : ℤ := z/(2 : ℤ)^(j+1)
  have he : z=(2 : ℤ)^j*(2*k+1) := by
    have h := Int.emod_add_mul_ediv z ((2 : ℤ)^(j+1))
    rw [hz] at h
    calc
      z = (2 : ℤ)^j + (2 : ℤ)^(j+1)*k := h.symm
      _ = (2 : ℤ)^j*(2*k+1) := by rw [pow_succ]; ring
  rw [he]
  exact read_carry d j f k hj

def word (d : ℕ) (z : ℤ) : Finset (Fin d) :=
  Finset.univ.filter (fun j => digit z j.val=1)

private theorem read_word {A : Type*} [AddCommGroup A] (d : ℕ) (f : ℕ → A) (z : ℤ) :
    (∑ j ∈ word d z, f j.val)=read d f z := by
  classical
  simp only [word, Finset.sum_filter, read]
  apply Finset.sum_congr rfl
  intro j _
  rcases digit_cases z j.val with h | h <;> simp [h]

private theorem word_mask (d : ℕ) (z : ℤ) (hz0 : 0≤z)
    (hz1 : z<(2 : ℤ)^d) : (mask (word d z) : ℤ)=z := by
  have he : (mask (word d z) : ℚ)=(z : ℚ) := by
    rw [mask, Nat.cast_sum]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (read_word d (fun j => (2 : ℚ)^j) z).trans (read_geom d z hz0 hz1)
  exact_mod_cast he

private theorem word_bit (d j : ℕ) (z : ℤ) (hj : j<d) :
    bit (word d z) j=digit z j := by
  rcases digit_cases z j with h | h <;> simp [bit, word, hj, h]

theorem top_digits (d : ℕ) (hd : 3≤d) (z : ℤ)
    (hz0 : 0≤z) (hz1 : z<(2 : ℤ)^d) :
    2*z/(2 : ℤ)^d=digit z (d-1) ∧
    4*z/(2 : ℤ)^d=digit z (d-2)+2*digit z (d-1) ∧
    8*z/(2 : ℤ)^d=digit z (d-3)+2*digit z (d-2)+4*digit z (d-1) := by
  have h := top_floors hd (word d z)
  rw [word_mask d z hz0 hz1, word_bit d (d-1) z (by omega),
    word_bit d (d-2) z (by omega), word_bit d (d-3) z (by omega)] at h
  exact h

private theorem place_eq_iff {d : ℕ} (hd : 0<d)
    (p q : Fin 3) (i j : Fin d) : place p i=place q j ↔ p=q ∧ i=j := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    fin_cases p <;> fin_cases q <;>
      simp only [place, Fin.val_mk] at hv <;>
      constructor <;> first | rfl | exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
  · rintro ⟨rfl,rfl⟩
    rfl

def physical (d : ℕ) (L M U : ℤ) : Finset (Fin (3*d)) :=
  (word d L).image (place 0) ∪
    ((word d M).image (place 1) ∪ (word d U).image (place 2))

private theorem physical_slices (d : ℕ) (hd : 0<d) (L M U : ℤ) :
    slice 0 (physical d L M U)=word d L ∧
    slice 1 (physical d L M U)=word d M ∧
    slice 2 (physical d L M U)=word d U := by
  classical
  have hm (p q : Fin 3) (z : ℤ) (j : Fin d) :
      place p j ∈ (word d z).image (place q) ↔ p=q ∧ j∈word d z := by
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨i,hi,he⟩
      obtain ⟨hp,hj⟩ := (place_eq_iff hd q p i j).mp he
      exact ⟨hp.symm, hj ▸ hi⟩
    · rintro ⟨rfl,hj⟩
      exact ⟨j,hj,rfl⟩
  refine ⟨?_,?_,?_⟩ <;> ext j <;>
    simp [slice, physical, hm]

def block {A : Type*} [Zero A] {d : ℕ}
    (x : Fin (3*d) → A) (h : Fin 3) (j : ℕ) : A :=
  if hj : j<d then x (place h ⟨j,hj⟩) else 0

theorem physical_read {A : Type*} [AddCommGroup A] {d : ℕ} (hd : 0<d)
    (x : Fin (3*d) → A) (L M U : ℤ) :
    (∑ i ∈ physical d L M U, x i) =
      read d (block x 0) L+read d (block x 1) M+read d (block x 2) U := by
  rw [sum_slices hd, (physical_slices d hd L M U).1,
    (physical_slices d hd L M U).2.1, (physical_slices d hd L M U).2.2]
  have hb (h : Fin 3) (z : ℤ) :
      (∑ j ∈ word d z, x (place h j))=read d (block x h) z := by
    rw [← read_word]
    apply Finset.sum_congr rfl
    intro j _
    simp [block, j.isLt]
  rw [hb, hb, hb]

end D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
