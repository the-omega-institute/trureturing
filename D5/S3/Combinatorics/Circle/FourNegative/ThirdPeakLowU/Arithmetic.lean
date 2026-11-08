/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLowU/Arithmetic
   generality: I
   mirror-B: none(waiver:consumed-low-u-support)
   mirror-E: none(waiver:physical-low-u-construction)
   anchors: []
   utility: none
   digest: Polynomial inequalities for unbounded low-U selection. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Banks

/-! Polynomial inequalities for unbounded low-U selection. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU

private def A (x y z : ℤ) : ℤ := 1+x+x*y+x*y*z
private def B (x y s : ℤ) : ℤ := 1+s*y+s*y*x+s*y*x*y
private def L (x y s z : ℤ) : ℤ := 1+z+z*s*y+x*z*s*y
private def K (y s z : ℤ) : ℤ := 1+y+y*z+y*z*s*y
private def C (y z : ℤ) : ℤ := 1+y+y*z
private def SU (x y s : ℤ) : ℤ := 2*B x y s-1
private def SV (x y s z : ℤ) : ℤ := 2*L x y s z-1-z
private def SW (y s z : ℤ) : ℤ := 2*K y s z-C y z
private def window (h H : ℤ) : Prop := 0≤h ∧ 2*h≤H-1

private theorem strict_polynomials (x y s z : ℤ)
    (hx : 4≤x) (hy : 2*x≤y) (hs : 2≤s) (hz : 8*s*y≤z) :
    3*SU x y s+1 ≤ A x y z ∧ 16*s ≤ SU x y s ∧
    0 ≤ SV x y s z-2*s*A x y z ∧
    2*L x y s z+1 ≤ (4*s-1)*A x y z ∧
    4*s*A x y z < z*SU x y s ∧
    A x y z ≥ C y z ∧ A x y z+C y z ≤ L x y s z ∧
    2*K y s z ≤ y*L x y s z := by
  let X := x-4
  let Y := y-2*x
  let S := s-2
  let Z := z-8*s*y
  have hX : 0≤X := by dsimp [X]; omega
  have hY : 0≤Y := by dsimp [Y]; omega
  have hS : 0≤S := by dsimp [S]; omega
  have hZ : 0≤Z := by dsimp [Z]; omega
  have ex : x=X+4 := by dsimp [X]; ring
  have ey : y=Y+2*x := by dsimp [Y]; ring
  have es : s=S+2 := by dsimp [S]; ring
  have ez : z=Z+8*s*y := by dsimp [Z]; ring
  have p0 : 0≤A x y z-3*SU x y s-1 := by
    dsimp [A,SU,B]; rw [ez,es,ey,ex]; ring_nf; positivity
  have p1 : 0≤SU x y s-16*s := by
    dsimp [SU,B]; rw [es,ey,ex]; ring_nf; positivity
  have p2 : 0≤SV x y s z-2*s*A x y z := by
    dsimp [SV,L,A]; rw [ez,es,ey,ex]; ring_nf; positivity
  have p3 : 0≤(4*s-1)*A x y z-2*L x y s z-1 := by
    dsimp [A,L]; rw [ez,es,ey,ex]; ring_nf; positivity
  have p4 : 0<z*SU x y s-4*s*A x y z := by
    dsimp [A,SU,B]; rw [ez,es,ey,ex]; ring_nf; positivity
  have p5 : 0≤A x y z-C y z := by
    dsimp [A,C]; rw [ez,es,ey,ex]; ring_nf; positivity
  have p6 : 0≤L x y s z-A x y z-C y z := by
    dsimp [A,L,C]; rw [ez,es,ey,ex]; ring_nf; positivity
  have p7 : 0≤y*L x y s z-2*K y s z := by
    dsimp [K,L]; rw [ez,es,ey,ex]; ring_nf; positivity
  exact ⟨by omega,by omega,p2,by omega,by omega,by omega,by omega,by omega⟩

private theorem strict_w_polynomials (x y s z : ℤ)
    (hx : 4≤x) (hs : 2≤s) (hz : 8*s*y≤z) :
    (y=2*x → A x y z+C y z ≤ K y s z-L x y s z ∧ K y s z≤2*L x y s z) ∧
    (y=4*x → A x y z+C y z ≤ K y s z-2*L x y s z ∧ K y s z≤4*L x y s z) ∧
    (8*x≤y → 4*L x y s z≤K y s z) := by
  let X := x-4
  let S := s-2
  let Z := z-8*s*y
  have hX : 0≤X := by dsimp [X]; omega
  have hS : 0≤S := by dsimp [S]; omega
  have hZ : 0≤Z := by dsimp [Z]; omega
  have ex : x=X+4 := by dsimp [X]; ring
  have es : s=S+2 := by dsimp [S]; ring
  have ez : z=Z+8*s*y := by dsimp [Z]; ring
  refine ⟨?_,?_,?_⟩
  · intro ey
    have p : 0≤K y s z-L x y s z-A x y z-C y z := by
      dsimp [K,L,A,C]; rw [ez,ey,es,ex]; ring_nf; positivity
    have q : 0≤2*L x y s z-K y s z := by
      dsimp [K,L]; rw [ez,ey,es,ex]; ring_nf; positivity
    omega
  · intro ey
    have p : 0≤K y s z-2*L x y s z-A x y z-C y z := by
      dsimp [K,L,A,C]; rw [ez,ey,es,ex]; ring_nf; positivity
    have q : 0≤4*L x y s z-K y s z := by
      dsimp [K,L]; rw [ez,ey,es,ex]; ring_nf; positivity
    omega
  · intro hy
    let Y := y-8*x
    have hY : 0≤Y := by dsimp [Y]; omega
    have ey : y=Y+8*x := by dsimp [Y]; ring
    have p : 0≤K y s z-4*L x y s z := by
      dsimp [K,L]; rw [ez,ey,es,ex]; ring_nf; positivity
    omega

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU
