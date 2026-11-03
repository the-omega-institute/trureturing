/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/TableData
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/TableData
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Exact paired row bounds and finite row type. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.LowBits

/-! Exact paired row bounds and finite row type. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD

structure FixedRow where
  x : ℕ
  p : ℕ
  q : ℕ
  h : ℕ
  v : ℕ
  m : ℕ
  M : ℕ
  before : Bool

def rowBounds (x p q h v m M : ℤ) (before : Bool) : Prop :=
  (∀ r : Fin 3,
    0≤oldEnds x p q h v m M r.castSucc ∧
    oldEnds x p q h v m M r.castSucc≤oldHeads x p q h r.castSucc-1 ∧
    0≤newEnds x p q h v m M before r.castSucc ∧
    newEnds x p q h v m M before r.castSucc≤newHeads x p q h r.castSucc-1) ∧
  1≤v ∧ 2*v≤T x p q ∧ 0≤M ∧ 2*M≤Y x p q h-2


structure ResidueRow where
  p : ℕ
  h : ℕ
  r : ℕ
  block : ℕ
  offset : ℕ
  m : ℕ
  constant : ℕ
  before : Bool
def residueRows : Fin 24 → ResidueRow :=
  ![⟨4,1,8,512,2,3,51,true⟩,
    ⟨4,1,16,512,2,3,107,true⟩,
    ⟨4,1,32,512,2,3,223,true⟩,
    ⟨4,1,64,512,2,3,451,true⟩,
    ⟨4,1,56,512,1,2,394,false⟩,
    ⟨4,1,40,512,2,3,279,true⟩,
    ⟨4,2,8,1024,2,6,102,true⟩,
    ⟨4,2,16,1024,2,6,214,true⟩,
    ⟨4,2,32,1024,2,6,446,true⟩,
    ⟨4,2,64,1024,2,6,902,true⟩,
    ⟨4,2,56,1024,2,6,783,true⟩,
    ⟨4,2,40,1024,2,6,558,true⟩,
    ⟨8,1,8,1024,3,4,100,true⟩,
    ⟨8,1,16,1024,3,4,214,true⟩,
    ⟨8,1,32,1024,3,4,444,true⟩,
    ⟨8,1,64,1024,3,4,900,true⟩,
    ⟨8,1,56,1024,3,4,783,true⟩,
    ⟨8,1,40,1024,3,4,556,true⟩,
    ⟨8,2,8,2048,1,1,201,true⟩,
    ⟨8,2,16,2048,1,1,429,true⟩,
    ⟨8,2,32,2048,1,1,883,true⟩,
    ⟨8,2,64,2048,1,1,1793,true⟩,
    ⟨8,2,56,2048,1,1,1565,true⟩,
    ⟨8,2,40,2048,1,1,1111,true⟩]

def fixedRows : Fin 16 → FixedRow :=
  ![⟨8,4,2,1,3,9,9,true⟩,
    ⟨8,4,2,2,7,3,15,true⟩,
    ⟨8,4,4,1,13,5,23,true⟩,
    ⟨8,4,4,2,15,3,47,true⟩,
    ⟨8,8,2,1,11,8,15,true⟩,
    ⟨8,8,2,2,15,1,29,true⟩,
    ⟨8,8,4,1,29,4,44,true⟩,
    ⟨8,8,4,2,31,1,87,true⟩,
    ⟨8,16,2,1,25,10,30,true⟩,
    ⟨8,16,2,2,30,1,59,true⟩,
    ⟨16,8,2,1,7,17,17,true⟩,
    ⟨16,8,2,2,15,3,31,true⟩,
    ⟨16,8,4,1,29,5,47,true⟩,
    ⟨16,8,4,2,31,3,91,true⟩,
    ⟨16,16,2,1,27,8,31,true⟩,
    ⟨16,16,2,2,31,1,61,true⟩]

/-- The only late-fresh entry is exactly p=4,h=1,r=56. -/
theorem residue_fresh_exact (i : Fin 24) :
    (residueRows i).before=false ↔
      (residueRows i).p=4 ∧ (residueRows i).h=1 ∧ (residueRows i).r=56 := by
  fin_cases i <;> norm_num [residueRows]


end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
