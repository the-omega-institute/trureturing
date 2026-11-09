/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/SmallAAllHData
   generality: I
   mirror-B: none(waiver:physical-construction-component)
   mirror-E: none(waiver:physical-construction-component)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Twenty scaled mask families, shift invariance and unbounded dyadic residues. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.TableData
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural
import Mathlib.Tactic.FinCases

/-! Dyadic support transport and unrestricted residue families on the actual physical definitions. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllH
open private submask_shift
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.QTwoStructural

structure ResidueFamily where
  p : ℕ
  r : ℕ
  m0 : ℕ
  C : ℕ

structure FixedFamily where
  x : ℕ
  p : ℕ
  q : ℕ
  v : ℕ
  m0 : ℕ
  M0 : ℕ

def residueFamilies : Fin 12 → ResidueFamily :=
  ![⟨4,8,5,205⟩, ⟨4,16,5,429⟩, ⟨4,32,5,885⟩,
    ⟨4,64,5,1797⟩, ⟨4,56,5,1567⟩, ⟨4,40,5,1111⟩,
    ⟨8,8,2,402⟩, ⟨8,16,2,855⟩, ⟨8,32,2,1766⟩,
    ⟨8,64,2,3586⟩, ⟨8,56,2,3130⟩, ⟨8,40,2,2222⟩]

def fixedFamilies : Fin 8 → FixedFamily :=
  ![⟨8,4,2,3,36,37⟩, ⟨8,4,4,3,93,95⟩,
    ⟨8,8,2,5,77,79⟩, ⟨8,8,4,5,192,193⟩,
    ⟨8,16,2,8,168,169⟩, ⟨16,8,2,5,83,87⟩,
    ⟨16,8,4,5,204,205⟩, ⟨16,16,2,9,172,173⟩]

/-- A common dyadic scaling shifts both sets of bits by the same arbitrary amount. -/
theorem submask_scale (k m M : ℕ) (hs : Submask m M) :
    Submask (2^k*m) (2^k*M) := by
  exact submask_shift m M k hs

theorem residue_masks (i : Fin 12) (R k : ℕ) :
    let f := residueFamilies i
    Submask (2^k*f.m0) (2^k*(512*f.p*R+f.C)) := by
  apply submask_scale
  fin_cases i
  all_goals dsimp [residueFamilies]
  all_goals first
    | exact submask_high_block 11 R _ _ (by norm_num) (by norm_num)
        (submask_of_land _ _ (by decide))
    | exact submask_high_block 12 R _ _ (by norm_num) (by norm_num)
        (submask_of_land _ _ (by decide))

theorem fixed_masks (i : Fin 8) (k : ℕ) :
    Submask (2^k*(fixedFamilies i).m0) (2^k*(fixedFamilies i).M0) := by
  apply submask_scale
  fin_cases i <;> apply submask_of_land <;> decide

/-- The only residue calculation is an induction on the unrestricted exponent. -/
private theorem mod_nine (s : ℕ) :
    2^s%9=1 ∨ 2^s%9=2 ∨ 2^s%9=4 ∨ 2^s%9=8 ∨ 2^s%9=7 ∨ 2^s%9=5 := by
  induction s with
  | zero => norm_num
  | succ s ih =>
    rw [pow_succ,Nat.mul_mod]
    rcases ih with h|h|h|h|h|h <;> rw [h] <;> norm_num

theorem residue_decomposition (s : ℕ) :
    ∃ R r : ℕ, 8*2^s=72*R+r ∧
      (r=8 ∨ r=16 ∨ r=32 ∨ r=64 ∨ r=56 ∨ r=40) := by
  refine ⟨(8*2^s)/72,(8*2^s)%72,by omega,?_⟩
  have he : (8*2^s)%72=8*(2^s%9) := by omega
  rw [he]
  rcases mod_nine s with h|h|h|h|h|h <;> rw [h] <;> norm_num

/-- The two exact charge identities required by the transparent generic adapter.
These are absent from the frozen compiled Algebra, so they live in this consumer. -/
theorem first_charge (x p q h v m M : ℤ) :
    newEnds x p q h v m M true 0 =
      2*oldEnds x p q h v m M 0+2*((Y x p q h-m)*(Z x q+1)+1) := by
  dsimp [newEnds,oldEnds,A,B,L,K,SU,SV,SW,Z,T,Y]
  ring

theorem second_charge (x p q h v m M : ℤ) (before : Bool) :
    newEnds x p q h v m M before 1 =
      2*oldEnds x p q h v m M 1+2*(Y x p q h-M)*(Z x q+1) := by
  dsimp [newEnds,oldEnds,A,B,L,K,SU,SV,SW,Z,T,Y]
  ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SmallAAllH
