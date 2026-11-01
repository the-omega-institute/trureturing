/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Seams
   generality: I
   mirror-B: none(waiver:private-consumed-seam-polynomials)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Exact doubled seam gates and exact source-native seam algebra. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Native
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
open private heads newHeads successor newSuccessor sourceN delta eight_recurrences
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Source
open private p H F C E
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Native

private def allocation (u h p c f e : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![u,0,p,0], ![0,u,h-p,c], ![0,0,f-h,0], ![0,0,0,e-c]]
private def nativeAllocation (a b s : ℕ) : Fin 4 → Fin 4 → ℤ :=
  allocation ((2:ℤ)^(s-1)-1) (H b s) (p a b s) (C a b s) (F b) (E a)
private def dot (v w : Fin 4 → ℤ) : ℤ :=
  v 0*w 0+v 1*w 1+v 2*w 2+v 3*w 3
private def termOrder : Fin 4 → Fin 4 := ![2,0,3,1]
private def doubledSeams (v su : Fin 4 → ℤ) (n fresh : ℤ)
    (m : Fin 4 → Fin 4 → ℤ) : Fin 3 → ℤ :=
  let h1 := 2*dot v (m 0)+su 2-n
  let h2 := h1+2*dot v (m 1)+su 0-n
  let h3 := h2+2*dot v (m 2)+2*fresh+su 3-n
  ![h1,h2,h3]
private def gate (x y z : ℤ) (m : Fin 4 → Fin 4 → ℤ) (r : Fin 3) : Fin 4 → ℤ :=
  let old := doubledSeams (heads x y z) (successor x y z) (sourceN x y z) 0 m r
  let new := doubledSeams (newHeads x y z) (newSuccessor x y z)
    (2*sourceN x y z+1) (heads x y z 0) m r
  let t : Fin 4 := ![2,0,3] r
  ![old,successor x y z t-1-old,new,newSuccessor x y z t-1-new]

private theorem last_seams (x y z u h p c f e : ℤ)
    (hu : 2*(u+1)=z) (hf : 2*(f+1)=y) (he : 2*(e+1)=x) :
    doubledSeams (heads x y z) (successor x y z) (sourceN x y z) 0
        (allocation u h p c f e) 2 +
      2*dot (heads x y z) (allocation u h p c f e 3)+
      successor x y z 1-sourceN x y z=0 ∧
    doubledSeams (newHeads x y z) (newSuccessor x y z) (2*sourceN x y z+1)
        (heads x y z 0) (allocation u h p c f e) 2 +
      2*dot (newHeads x y z) (allocation u h p c f e 3)+
      newSuccessor x y z 1-(2*sourceN x y z+1)=0 := by
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7⟩ := eight_recurrences x y z
  have r8 : newHeads x y z 0=2*heads x y z 0 := rfl
  rw [←hu,←hf,←he] at r0 r1 r2 r3 r4 r5 r6 r7 r8 ⊢
  dsimp only [doubledSeams,dot,allocation,successor,newSuccessor]
  simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  constructor
  · linear_combination r0+r1+r2+r3
  · linear_combination r4+r5+r6+r7-2*r8

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
