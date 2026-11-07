/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Readout
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 UpperBasis Readout on original physical labels. -/
/- UNCOMPILED. Integer binary transport, consumed by the physical upper-row
   calculation. All coefficient divisions take place in Z, never in A. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Family
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
open scoped BigOperators
open MersenneExceptional19PermutationStabilizer
  (digit read read_succ read_geom read_congr)
open private digit_cases
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary

variable {A : Type*} [AddCommGroup A]

/-- Adding an integral multiple of the word length leaves every low digit
unchanged. This is also used with negative multiples for upper-row differences. -/
private theorem digit_period (n i : ℕ) (z k : ℤ) (hi : i<n) :
    digit (z+(2 : ℤ)^n*k) i=digit z i := by
  have he : (2 : ℤ)^n*k=((2 : ℤ)^(n-i)*k)*(2 : ℤ)^i := by
    rw [mul_right_comm,← pow_add,Nat.sub_add_cancel (by omega : i≤n)]
  have hp : (2 : ℤ)^(n-i)*k=2*((2 : ℤ)^(n-i-1)*k) := by
    rw [show n-i=(n-i-1)+1 by omega,pow_succ]
    ring
  unfold digit
  rw [he,Int.add_mul_ediv_right _ _ (by positivity),hp]
  omega

private theorem read_period (n : ℕ) (f : ℕ → A) (z k : ℤ) :
    read n f (z+(2 : ℤ)^n*k)=read n f z := by
  apply Finset.sum_congr rfl
  intro i _
  rw [digit_period n i.val z k i.isLt]

/-- Split a binary readout at an arbitrary bit position. No sign or size
hypothesis is necessary for this exact Euclidean-division identity. -/
private theorem read_split (n k : ℕ) (f : ℕ → A) (z : ℤ) :
    read (n+k) f z=read n f z+
      read k (fun i => f (n+i)) (z/(2 : ℤ)^n) := by
  induction n generalizing f z with
  | zero => simp [read]
  | succ n ih =>
    rw [show n+1+k=(n+k)+1 by omega,read_succ,ih,read_succ]
    have hq : (z/2)/(2 : ℤ)^n=z/(2 : ℤ)^(n+1) := by
      rw [Int.ediv_ediv_of_nonneg (by norm_num : (0 : ℤ)≤2),pow_succ']
    simp only [hq]
    have hf : (fun i => f (n+i+1))=(fun i => f (n+1+i)) := by
      funext i
      congr 1
      omega
    rw [hf]
    abel

private theorem read_geom_smul (n : ℕ) (c : A) (z : ℤ)
    (hz : 0≤z ∧ z<(2 : ℤ)^n) :
    read n (fun i => (2 : ℤ)^i • c) z=z • c := by
  have hc : read n (fun i => (2 : ℤ)^i • c) z=
      (read n (fun i => (2 : ℤ)^i) z) • c := by
    simp only [read,smul_smul,Finset.sum_smul,zsmul_eq_mul]
  rw [hc,read_geom n z hz.1 hz.2]
  simp

/-- Read the top three bits after cancelling the common low word. The
integer q values are calculated from the actual affine digits in HighRows. -/
theorem read_top_difference (n : ℕ) (f : ℕ → A) (z z' q q' k : ℤ)
    (hz : z/(2 : ℤ)^n=q) (hz' : z'/(2 : ℤ)^n=q')
    (hshift : z=z'+(2 : ℤ)^n*k) :
    read (n+3) f z-read (n+3) f z'=
      read 3 (fun i => f (n+i)) q-read 3 (fun i => f (n+i)) q' := by
  rw [read_split,read_split,hz,hz']
  have hlo : read n f z=read n f z' := by
    rw [hshift,read_period]
  rw [hlo]
  abel

/-- Adding 2^j reads only bits j and j+1 once all higher coordinates double.
The endpoint j+1<d is explicit: no implicit out-of-range coordinate is used.
Naturals provide the required 0≤j. This lemma applies to arbitrary torsion. -/
theorem read_add_power (d j : ℕ) (f : ℕ → A) (m : ℤ)
    (hj : j+1<d) (hm : 0≤m ∧ m+(2 : ℤ)^j<(2 : ℤ)^d)
    (hdbl : ∀ i, j<i → i<d → f i=(2 : ℤ)^(i-j-1) • f (j+1)) :
    read d f (m+(2 : ℤ)^j)-read d f m=
      (1-2*digit m j) • f j+digit m j • f (j+1) := by
  induction j generalizing d f m with
  | zero =>
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
    have hn : 0<n := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    have hq0 : 0≤m/2 := Int.ediv_nonneg hm.1 (by norm_num)
    have hq1 : m/2<(2 : ℤ)^(k+1) := by
      rw [pow_succ] at hm
      omega
    have hq0' : 0≤(m+1)/2 := by omega
    have hq1' : (m+1)/2<(2 : ℤ)^(k+1) := by
      rw [pow_zero,pow_succ] at hm
      omega
    have tail (z : ℤ) (hz : 0≤z ∧ z<(2 : ℤ)^(k+1)) :
        read (k+1) (fun i => f (i+1)) z=z • f 1 := by
      calc
        _=read (k+1) (fun i => (2 : ℤ)^i • f 1) z := by
          apply read_congr
          intro i hi
          simpa using hdbl (i+1) (by omega) (by omega)
        _=z • f 1 := read_geom_smul _ _ _ hz
    rw [pow_zero,read_succ,read_succ,tail _ ⟨hq0',hq1'⟩,tail _ ⟨hq0,hq1⟩]
    rcases digit_cases m 0 with he | he
    · have hp : m%2=0 := by simpa [digit] using he
      have hp' : (m+1)%2=1 := by omega
      have hq : (m+1)/2=m/2 := by omega
      simp [he,hp,hp',hq]
    · have hp : m%2=1 := by simpa [digit] using he
      have hp' : (m+1)%2=0 := by omega
      have hq : (m+1)/2=m/2+1 := by omega
      simp only [he,hp,hp',hq,zero_smul,one_smul,zero_add]
      module
  | succ j ih =>
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
    have hp : (2 : ℤ)^(j+1)=2*(2 : ℤ)^j := by rw [pow_succ']
    have he : (m+(2 : ℤ)^(j+1))%2=m%2 := by rw [hp]; omega
    have hq : (m+(2 : ℤ)^(j+1))/2=m/2+(2 : ℤ)^j := by rw [hp]; omega
    have hm' : 0≤m/2 ∧ m/2+(2 : ℤ)^j<(2 : ℤ)^n := by
      rw [hp,pow_succ] at hm
      omega
    have hh : ∀ i, j<i → i<n →
        f (i+1)=(2 : ℤ)^(i-j-1) • f (j+1+1) := by
      intro i hi hin
      have ht := hdbl (i+1) (by omega) (by omega)
      convert ht using 1 <;> congr 1 <;> omega
    have hc := ih n (fun i => f (i+1)) (m/2) (by omega) hm' hh
    have hdigit : digit m (j+1)=digit (m/2) j := by
      unfold digit
      rw [Int.ediv_ediv_of_nonneg (by norm_num : (0 : ℤ)≤2),pow_succ']
    rw [read_succ,read_succ,he,hq,hdigit]
    linear_combination (norm := abel) hc

end D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
