/- GID: D5/S3/Arith/Covering/Erdos203Normalization
   generality: I
   mirror-B: D5/B/S3/Arith/Covering/Erdos203Normalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Common seven-phase normalization and the exact six-row homogeneous kernel. -/

import D5.S3.Arith.Covering.Erdos203Rows
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace D5.S3.Arith.Covering.Erdos203

/-- There is one translation for the entire original phase vector. The event equivalence
holds for all 252 rows, every point, and the same translation chosen before the point. -/
theorem normalize_original_phases (c : Phases) :
    ∃ t : ℤ × ℤ, Canonical (shiftPhases c t) ∧
      ∀ (i : Fin 252) (x y : ℤ),
        (rows i).hits (shiftPhases c t i) x y ↔
        (rows i).hits (c i) (x+t.1) (y+t.2) := by
  let x0 : ℤ := 0
  let y0 := -c 0
  let q1 := c 1 - (2*x0+y0)
  let x1 := x0 - 3*q1
  let y1 := y0 + q1
  let q2 := (c 2-(x1+8*y1))/2
  let x2 := x1-2*q2
  let y2 := y1-2*q2
  let q3 := (c 3-(x2+4*y2))/2
  let x3 := x2-14*q3
  let y3 := y2-2*q3
  let q4 := (c 4-(14*x3+y3))/4
  let x4 := x3-24*q4
  let y4 := y3-12*q4
  let q5 := (c 5-(x4+13*y4))/6
  let x5 := x4+12*q5
  let y5 := y4-24*q5
  let q6 := c 6-(x5+8*y5)
  let tx := x5-36*q6
  let ty := y5+72*q6
  refine ⟨(tx,ty), ?_, ?_⟩
  · intro i
    fin_cases i
    · change (c 0-(1*tx+3*ty))%4<1
      dsimp [tx,ty,x0,y0,q1,x1,y1,q2,x2,y2,q3,x3,y3,q4,x4,y4,q5,x5,y5,q6]
      omega
    · change (c 1-(2*tx+1*ty))%6<1
      dsimp [tx,ty,x0,y0,q1,x1,y1,q2,x2,y2,q3,x3,y3,q4,x4,y4,q5,x5,y5,q6]
      omega
    · change (c 2-(1*tx+8*ty))%10<2
      dsimp [tx,ty,x0,y0,q1,x1,y1,q2,x2,y2,q3,x3,y3,q4,x4,y4,q5,x5,y5,q6]
      omega
    · change (c 3-(1*tx+4*ty))%12<2
      dsimp [tx,ty,x0,y0,q1,x1,y1,q2,x2,y2,q3,x3,y3,q4,x4,y4,q5,x5,y5,q6]
      omega
    · change (c 4-(14*tx+1*ty))%16<4
      dsimp [tx,ty,x0,y0,q1,x1,y1,q2,x2,y2,q3,x3,y3,q4,x4,y4,q5,x5,y5,q6]
      omega
    · change (c 5-(1*tx+13*ty))%18<6
      dsimp [tx,ty,x0,y0,q1,x1,y1,q2,x2,y2,q3,x3,y3,q4,x4,y4,q5,x5,y5,q6]
      omega
    · change (c 6-(1*tx+8*ty))%11<1
      dsimp [tx,ty,x0,y0,q1,x1,y1,q2,x2,y2,q3,x3,y3,q4,x4,y4,q5,x5,y5,q6]
      omega
  · intro i x y
    simp only [Row.hits, shiftPhases, Int.modEq_iff_dvd]
    ring_nf

/-- Exact homogeneous kernel of the first six original rows. The reverse direction includes
all integer coefficients, and the forward direction constructs both lattice coordinates. -/
theorem six_row_kernel_coordinates (x y : ℤ) :
    (∀ i : Fin 6, (rows (i.castLE (by decide : 6 ≤ 252))).hits 0 x y) ↔
    ∃ u v : ℤ, x = 360*u+228*v ∧ y=24*v := by
  have expand : (∀ i : Fin 6, (rows (i.castLE (by decide : 6 ≤ 252))).hits 0 x y) ↔
      (x + 3*y) % 4 = 0 ∧ (2*x+y) % 6 = 0 ∧ (x+8*y) % 10 = 0 ∧
        (x+4*y) % 12 = 0 ∧ (14*x+y) % 16 = 0 ∧ (x+13*y) % 18 = 0 := by
    constructor
    · intro h
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      have h3 := h 3
      have h4 := h 4
      have h5 := h 5
      change (1*x+3*y)%4=0%4 at h0
      change (2*x+1*y)%6=0%6 at h1
      change (1*x+8*y)%10=0%10 at h2
      change (1*x+4*y)%12=0%12 at h3
      change (14*x+1*y)%16=0%16 at h4
      change (1*x+13*y)%18=0%18 at h5
      simp only [one_mul,Int.zero_emod] at h0 h1 h2 h3 h4 h5
      exact ⟨h0,h1,h2,h3,h4,h5⟩
    · rintro ⟨h0,h1,h2,h3,h4,h5⟩ i
      fin_cases i
      · change (1*x+3*y)%4=0%4
        simpa only [one_mul,Int.zero_emod] using h0
      · change (2*x+1*y)%6=0%6
        simpa only [one_mul,Int.zero_emod] using h1
      · change (1*x+8*y)%10=0%10
        simpa only [one_mul,Int.zero_emod] using h2
      · change (1*x+4*y)%12=0%12
        simpa only [one_mul,Int.zero_emod] using h3
      · change (14*x+1*y)%16=0%16
        simpa only [one_mul,Int.zero_emod] using h4
      · change (1*x+13*y)%18=0%18
        simpa only [one_mul,Int.zero_emod] using h5
  rw [expand]
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5⟩
    have s1 : ∃ u v : ℤ, x=4*u+v ∧ y=v := by
      clear h1 h2 h3 h4 h5
      exact ⟨(x-y)/4,y,by omega,rfl⟩
    obtain ⟨u1,v1,hx1,hy1⟩ := s1
    have s2 : ∃ u v : ℤ, x=12*u+2*v ∧ y=2*v := by
      clear h0 h2 h3 h4 h5
      refine ⟨u1/3,v1/2,?_,?_⟩ <;> omega
    obtain ⟨u2,v2,hx2,hy2⟩ := s2
    have s3 : ∃ u v : ℤ, x=60*u+14*v ∧ y=2*v := by
      clear h0 h1 h3 h4 h5 hx1 hy1
      refine ⟨(u2-v2)/5,v2,?_,?_⟩ <;> omega
    obtain ⟨u3,v3,hx3,hy3⟩ := s3
    have s4 : ∃ u v : ℤ, x=60*u+24*v ∧ y=12*v := by
      clear h0 h1 h2 h4 h5 hx1 hy1 hx2 hy2
      refine ⟨u3+v3/6,v3/6,?_,?_⟩ <;> omega
    obtain ⟨u4,v4,hx4,hy4⟩ := s4
    have s5 : ∃ u v : ℤ, x=120*u+108*v ∧ y=24*v := by
      clear h0 h1 h2 h3 h5 hx1 hy1 hx2 hy2 hx3 hy3
      refine ⟨(u4-v4/2)/2,v4/2,?_,?_⟩ <;> omega
    obtain ⟨u5,v5,hx5,hy5⟩ := s5
    clear h0 h1 h2 h3 h4 hx1 hy1 hx2 hy2 hx3 hy3 hx4 hy4
    refine ⟨(u5-v5)/3,v5,?_,?_⟩ <;> omega
  · rintro ⟨u,v,rfl,rfl⟩
    omega

end D5.S3.Arith.Covering.Erdos203
