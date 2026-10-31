/- GID: D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentSource
   mirror-E: none(waiver:no-public-declarations)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Independent paired-gap centered chains on the original physical labels. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoublePhysical

/-! Source identities for independent paired gaps; physical multiplicities are retained. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentSource
open SourceWidth PeriodicShortening RunFirstEarTransport
open private centered_ladder from D5.S3.Combinatorics.Circle.ThreeBitSource
open private shift from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleJointLift

private theorem coefficient_bounds (x y : ℤ) (hx : 4 ≤ x) (hy : 4 ≤ y) :
    let N := x^2*y^2-1
    let A := 1+x+x^2+x^2*y
    let B := 1+y+x*y+x^2*y
    let L := 1+y+y^2+x*y^2
    let M := 1+x+x*y+x*y^2
    let e := 1+x+x*y
    (0 < A ∧ 2*A < N) ∧ (0 < B ∧ 2*B < N) ∧
    (0 < L ∧ 2*L < N) ∧ (0 < M ∧ 2*M < N) ∧
    0 < 2*B-1 ∧ 0 < 2*L-1-y ∧ 0 < 2*M-e := by
  dsimp only
  let u := x-4
  let v := y-4
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have ex : x=u+4 := by dsimp [u]; ring
  have ey : y=v+4 := by dsimp [v]; ring
  have margins :
      0 < x^2*y^2-1-2*(1+x+x^2+x^2*y) ∧
      0 < x^2*y^2-1-2*(1+y+x*y+x^2*y) ∧
      0 < x^2*y^2-1-2*(1+y+y^2+x*y^2) ∧
      0 < x^2*y^2-1-2*(1+x+x*y+x*y^2) := by
    rw [ex,ey]
    ring_nf
    exact ⟨by positivity,by positivity,by positivity,by positivity⟩
  have positive_new : 0 < 2*(1+y+x*y+x^2*y)-1 ∧
      0 < 2*(1+y+y^2+x*y^2)-1-y ∧
      0 < 2*(1+x+x*y+x*y^2)-(1+x+x*y) := by
    rw [ex,ey]
    ring_nf
    exact ⟨by positivity,by positivity,by positivity⟩
  refine ⟨⟨by positivity,by linarith [margins.1]⟩,
    ⟨by positivity,by linarith [margins.2.1]⟩,
    ⟨by positivity,by linarith [margins.2.2.1]⟩,
    ⟨by positivity,by linarith [margins.2.2.2]⟩,positive_new⟩

set_option maxHeartbeats 800000 in
private theorem chains (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) :
    let x : ℤ := 2^r
    let y : ℤ := 2^s
    let k := 2*r+2*s
    let N := modulus k
    let A := 1+x+x^2+x^2*y
    let B := 1+y+x*y+x^2*y
    let L := 1+y+y^2+x*y^2
    let M := 1+x+x*y+x*y^2
    let e := 1+x+x*y
    let f := fun i : ℕ => centered N ((2 : ℤ)^i*A)
    let g := fun i : ℕ => centered (modulus (k+1)) ((2 : ℤ)^i*(2*A))
    (∀ i<s, f i = if i+1<s then 2^i*A else -(N-B)/2) ∧
    (∀ i<s, f (s+i) = if i+1<s then 2^i*B else -(N-L)/2) ∧
    (∀ i<r, f (2*s+i) = if i+1<r then 2^i*L else -(N-M)/2) ∧
    (∀ i<r, f (2*s+r+i) = if i+1<r then 2^i*M else -(N-A)/2) ∧
    (∀ i<s, g i = if i+1<s then 2^i*(2*A) else -(modulus (k+1)-(2*B-1))/2) ∧
    (∀ i<s, g (s+i) = if i+1<s then 2^i*(2*B-1) else -(modulus (k+1)-(2*L-1-y))/2) ∧
    (∀ i<r, g (2*s+i) = if i+1<r then 2^i*(2*L-1-y) else -(modulus (k+1)-(2*M-e))/2) ∧
    (∀ i<r, g (2*s+r+i) = if i+1<r then 2^i*(2*M-e) else -(modulus (k+1)-A)/2) ∧
    g k=A := by
  dsimp only
  let x : ℤ := 2^r
  let y : ℤ := 2^s
  let k := 2*r+2*s
  let N := modulus k
  let NN := modulus (k+1)
  let A := 1+x+x^2+x^2*y
  let B := 1+y+x*y+x^2*y
  let L := 1+y+y^2+x*y^2
  let M := 1+x+x*y+x*y^2
  let e := 1+x+x*y
  have hx : 4 ≤ x := by simpa [x] using pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) hr
  have hy : 4 ≤ y := by simpa [y] using pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) hs
  have hN : N=x^2*y^2-1 := by
    dsimp [N,k,modulus,x,y]
    rw [show 2*r+2*s=r+r+(s+s) by omega]
    simp only [pow_add]; ring
  have hNN : NN=2*N+1 := by dsimp [NN,N,modulus]; rw [pow_succ]; ring
  obtain ⟨hA,hB,hL,hM,hGV,hGW,hGX⟩ := coefficient_bounds x y hx hy
  change 0<A ∧ 2*A<x^2*y^2-1 at hA
  change 0<B ∧ 2*B<x^2*y^2-1 at hB
  change 0<L ∧ 2*L<x^2*y^2-1 at hL
  change 0<M ∧ 2*M<x^2*y^2-1 at hM
  change 0<2*B-1 at hGV
  change 0<2*L-1-y at hGW
  change 0<2*M-e at hGX
  rw [←hN] at hA hB hL hM
  have hrels : y*A=N+B ∧ y*B=N+L ∧ x*L=N+M ∧ x*M=N+A := by
    rw [hN]; dsimp [A,B,L,M]; refine ⟨?_,?_,?_,?_⟩ <;> ring
  have hgrels : y*(2*A)=NN+(2*B-1) ∧ y*(2*B-1)=NN+(2*L-1-y) ∧
      x*(2*L-1-y)=NN+(2*M-e) ∧ x*(2*M-e)=NN+A := by
    rw [hNN,hN]; dsimp [A,B,L,M,e]; refine ⟨?_,?_,?_,?_⟩ <;> ring
  have hNp : 0<N := by omega
  have hNo : N%2=1 := by
    have hp : (2 : ℤ)^k%2=0 := by
      rw [show k=(k-1)+1 by dsimp [k]; omega,pow_succ]; omega
    dsimp [N,modulus]; omega
  have he0 : 0≤e := by dsimp [e]; positivity
  have hNNp : 0<NN := by omega
  have hNNo : NN%2=1 := by omega
  have fV (i : ℕ) : centered N ((2 : ℤ)^(s+i)*A)=centered N ((2 : ℤ)^i*B) :=
    shift N A B s i hrels.1
  have fW (i : ℕ) : centered N ((2 : ℤ)^(2*s+i)*A)=centered N ((2 : ℤ)^i*L) := by
    rw [show 2*s+i=s+(s+i) by omega,fV]
    exact shift N B L s i hrels.2.1
  have fX (i : ℕ) : centered N ((2 : ℤ)^(2*s+r+i)*A)=centered N ((2 : ℤ)^i*M) := by
    rw [show 2*s+r+i=2*s+(r+i) by omega,fW]
    exact shift N L M r i hrels.2.2.1
  have gV (i : ℕ) : centered NN ((2 : ℤ)^(s+i)*(2*A))=centered NN ((2 : ℤ)^i*(2*B-1)) :=
    shift NN (2*A) (2*B-1) s i hgrels.1
  have gW (i : ℕ) : centered NN ((2 : ℤ)^(2*s+i)*(2*A))=centered NN ((2 : ℤ)^i*(2*L-1-y)) := by
    rw [show 2*s+i=s+(s+i) by omega,gV]
    exact shift NN (2*B-1) (2*L-1-y) s i hgrels.2.1
  have gX (i : ℕ) : centered NN ((2 : ℤ)^(2*s+r+i)*(2*A))=centered NN ((2 : ℤ)^i*(2*M-e)) := by
    rw [show 2*s+r+i=2*s+(r+i) by omega,gW]
    exact shift NN (2*L-1-y) (2*M-e) r i hgrels.2.2.1
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi; exact centered_ladder N A B s i hNp hNo hA.1 ⟨by omega,by omega⟩ hi hrels.1
  · intro i hi; rw [fV]; exact centered_ladder N B L s i hNp hNo hB.1 ⟨by omega,by omega⟩ hi hrels.2.1
  · intro i hi; rw [fW]; exact centered_ladder N L M r i hNp hNo hL.1 ⟨by omega,by omega⟩ hi hrels.2.2.1
  · intro i hi; rw [fX]; exact centered_ladder N M A r i hNp hNo hM.1 ⟨by omega,by omega⟩ hi hrels.2.2.2
  · intro i hi; exact centered_ladder NN (2*A) (2*B-1) s i hNNp hNNo (by omega) ⟨by omega,by omega⟩ hi hgrels.1
  · intro i hi; rw [gV]; exact centered_ladder NN (2*B-1) (2*L-1-y) s i hNNp hNNo hGV ⟨by omega,by omega⟩ hi hgrels.2.1
  · intro i hi; rw [gW]; exact centered_ladder NN (2*L-1-y) (2*M-e) r i hNNp hNNo hGW ⟨by omega,by omega⟩ hi hgrels.2.2.1
  · intro i hi; rw [gX]; exact centered_ladder NN (2*M-e) A r i hNNp hNNo hGX ⟨by omega,by omega⟩ hi hgrels.2.2.2
  · have hh : centered NN ((2 : ℤ)^k*(2*A))=centered NN A := by
      apply centered_congr
      have he : (2 : ℤ)^k*(2*A)=A+A*NN := by dsimp [NN,modulus]; rw [pow_succ]; ring
      rw [he,Int.add_mul_emod_self_right]
    change centered NN ((2 : ℤ)^k*(2*A))=A
    rw [hh]
    exact centered_unique hNNp hNNo (centered_bounds hNNp hNNo A) ⟨by omega,by omega⟩ (centered_mod NN A)

end D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentSource
