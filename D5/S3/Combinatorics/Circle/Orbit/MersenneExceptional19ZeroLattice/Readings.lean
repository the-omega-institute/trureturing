/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/Readings
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [lake/module/D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.NormalForm]
   utility: none
   digest: Integral exceptional19 ZeroLattice Readings on original physical labels. -/
/- UNCOMPILED source candidate. Only integer coefficients are divided. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.NormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice
open scoped BigOperators
open MersenneExceptional19Stabilizer (degree base)
open MersenneExceptional19PermutationStabilizer
  (digit read read_succ read_add read_sub read_congr read_unit read_geom
    top_digits block correction)

variable {A : Type*} [AddCommGroup A]

private theorem read_zsmul (d : ℕ) (f : ℕ → ℤ) (c : A) (z : ℤ) :
    read d (fun j => f j • c) z = read d f z • c := by
  simp only [MersenneExceptional19PermutationStabilizer.read, zsmul_eq_mul, Int.cast_id, mul_smul, Finset.sum_smul]

private theorem read_spike (d k : ℕ) (c : A) (z : ℤ) (hk : k<d) :
    read d (fun j => if j=k then c else 0) z = digit z k • c := by
  have he : (fun j => if j=k then c else 0) =
      (fun j => (if j=k then (1 : ℤ) else 0) • c) := by
    funext j
    split_ifs <;> simp
  rw [he, read_zsmul, read_unit d k z hk]
  simp

/-- Reading the separate low generator and the remaining binary ladder.
The quotient z/2 occurs in ℤ, never in A. -/
private theorem read_half (d : ℕ) (hd : 0<d) (u x : A) (z : ℤ)
    (hz : 0≤z ∧ z<(2 : ℤ)^d) :
    read d (fun j => if j=0 then u else (2 : ℤ)^(j-1) • x) z =
      (z%2) • u + (z/2) • x := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  rw [read_succ]
  have he : (fun j => if j+1=0 then u else (2 : ℤ)^(j+1-1) • x) =
      (fun j => (2 : ℤ)^j • x) := by
    funext j
    simp
  simp only [ite_true]
  rw [he, read_zsmul]
  have hz0 : 0≤z/2 := Int.ediv_nonneg hz.1 (by norm_num)
  have hz1 : z/2<(2 : ℤ)^m := by
    have := hz.2
    rw [pow_succ] at this
    omega
  rw [read_geom m (z/2) hz0 hz1]
  simp

private theorem read_first (d : ℕ) (hd : 3≤d) (u x ρ θ : A) (z : ℤ)
    (hz : 0≤z ∧ z<(2 : ℤ)^d) :
    read d (first d u x ρ θ) z =
      (z%2) • u + (z/2) • x + digit z (d-1) • (ρ-θ) := by
  unfold first
  rw [read_add, read_half d (by omega) u x z hz,
    read_spike d (d-1) (ρ-θ) z (by omega)]

private theorem read_middle (d : ℕ) (hd : 3≤d) (y θ : A) (z : ℤ)
    (hz : 0≤z ∧ z<(2 : ℤ)^d) :
    read d (middle d y θ) z = z • y + digit z (d-3) • θ +
      digit z (d-2) • θ + digit z (d-1) • ((2 : ℤ) • θ) := by
  unfold middle
  rw [read_add, read_add, read_add, read_zsmul,
    read_geom d z hz.1 hz.2, read_spike d (d-3) θ z (by omega),
    read_spike d (d-2) θ z (by omega),
    read_spike d (d-1) ((2 : ℤ) • θ) z (by omega)]
  simp

private theorem read_last (d : ℕ) (hd : 3≤d) (u x y ρ θ : A) (z : ℤ)
    (hz : 0≤z ∧ z<(2 : ℤ)^d) :
    read d (last d u x y ρ θ) z =
      (z%2) • (-u-y) + (z/2) • (-x-(2 : ℤ) • y) -
        digit z (d-2) • θ - digit z (d-1) • (ρ+(2 : ℤ) • θ) := by
  unfold last
  rw [read_sub, read_sub, read_half d (by omega) _ _ z hz,
    read_spike d (d-2) θ z (by omega),
    read_spike d (d-1) (ρ+(2 : ℤ) • θ) z (by omega)]

/-- The integer presentation's five-generator mask reading. It is valid
in every abelian group; all physical labels are retained. -/
theorem integral_read (r : ℕ) (X : Fin (3*degree r) → A)
    (u x y ρ θ : A)
    (hf : ∀ j, j<degree r → block X 0 j=first (degree r) u x ρ θ j)
    (hg : ∀ j, j<degree r → block X 1 j=middle (degree r) y θ j)
    (hh : ∀ j, j<degree r → block X 2 j=last (degree r) u x y ρ θ j)
    (L M U : ℤ) (hL : 0≤L ∧ L<base r) (hM : 0≤M ∧ M<base r)
    (hU : 0≤U ∧ U<base r) :
    read (degree r) (block X 0) L + read (degree r) (block X 1) M +
      read (degree r) (block X 2) U =
      (L%2-U%2) • u + (L/2-U/2) • x + (M-U) • y +
        (2*L/(base r : ℤ)-2*U/(base r : ℤ)) • ρ +
        correction (base r) L M U • θ := by
  have hd : 3≤degree r := by dsimp [degree]; omega
  have hp : (2 : ℤ)^degree r=base r := by simp [base]
  have hL' : 0≤L ∧ L<(2 : ℤ)^degree r := by simpa [hp] using hL
  have hM' : 0≤M ∧ M<(2 : ℤ)^degree r := by simpa [hp] using hM
  have hU' : 0≤U ∧ U<(2 : ℤ)^degree r := by simpa [hp] using hU
  rw [read_congr _ _ _ L hf, read_congr _ _ _ M hg,
    read_congr _ _ _ U hh, read_first _ hd _ _ _ _ L hL',
    read_middle _ hd _ _ M hM', read_last _ hd _ _ _ _ _ U hU']
  obtain ⟨l2,l4,l8⟩ := top_digits (degree r) hd L hL'.1 hL'.2
  obtain ⟨m2,m4,m8⟩ := top_digits (degree r) hd M hM'.1 hM'.2
  obtain ⟨u2,u4,u8⟩ := top_digits (degree r) hd U hU'.1 hU'.2
  rw [hp] at l2 m4 m8 u2 u4
  unfold correction
  simp only [l2,m8,m4,u2,u4]
  have heU : M-U=M-2*(U/2)-U%2 := by omega
  rw [heU]
  module

end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice
