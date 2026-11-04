/- GID: D5/S3/Combinatorics/Circle/FourNegative/OuterMaximumTie/Arithmetic
   generality: I
   mirror-B: none(waiver:consumed-arithmetic)
   mirror-E: none(waiver:consumed-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual charged seam arithmetic at the outer maximum tie. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingArithmetic

/-! Candidate source; no compilation or acceptance is asserted.  The variables
are t=2^a, y=2^b, z=2^c, with the ORIGINAL physical orientation d=a. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie

private def D (y z : ℤ) : ℤ := y*z+y+1
private def A (t y z : ℤ) : ℤ := t*D y z+1
private def B (t y : ℤ) : ℤ := t^2*(y+1)+t+1
private def L (t z : ℤ) : ℤ := z*t^2+z*t+z+1
private def M (t y z : ℤ) : ℤ := t*y*z+D y z
private def eps (t y z : ℤ) : ℤ := A t y z-M t y z

private def oldSeam (asc : Bool) (t y z v w : ℤ) : Fin 4 → ℤ :=
  if asc then ![eps t y z, B t y-M t y z-v*A t y z,
    L t z-M t y z-v*A t y z-w*B t y,0]
  else ![eps t y z, (v+1)*A t y z-M t y z+(w+1)*L t z-B t y,
    (w+1)*L t z-M t y z,0]
private def newSeam (asc : Bool) (t y z v w : ℤ) : Fin 4 → ℤ :=
  let E := oldSeam asc t y z v w
  if asc then ![2*E 0+D y z,2*E 1+D y z-1,2*E 2+D y z+w-z-1,0]
  else ![2*E 0+D y z,2*E 1+D y z-z-w*(z+1),
    2*E 2+D y z-(w+1)*(z+1),0]
private def oldHead (asc : Bool) (t y z : ℤ) : Fin 4 → ℤ :=
  if asc then ![A t y z,B t y,L t z,M t y z]
  else ![A t y z,L t z,B t y,M t y z]
private def newHead (asc : Bool) (t y z : ℤ) : Fin 4 → ℤ :=
  if asc then ![A t y z,2*B t y-1,2*L t z-z-1,2*M t y z-D y z]
  else ![A t y z,2*L t z-z-1,2*B t y-1,2*M t y z-D y z]
private def Gates (asc : Bool) (t y z v w : ℤ) : Prop :=
  ∀ j : Fin 4,
    (0 ≤ oldSeam asc t y z v w j ∧
      2*oldSeam asc t y z v w j ≤ oldHead asc t y z j-1) ∧
    (0 ≤ newSeam asc t y z v w j ∧
      2*newSeam asc t y z v w j ≤ newHead asc t y z j-1)
private def Stock (asc : Bool) (t y z v w : ℤ) : Prop :=
  0 ≤ v ∧ 2*v<t ∧ 0 ≤ w ∧ 2*w<(if asc then z else y)

private theorem first_gates (t y z : ℤ)
    (hy : 4≤y) (hz : 4≤z) (hyt : y≤t) (hzt : z≤t) :
    0≤eps t y z ∧ 2*eps t y z≤A t y z-1 ∧
    0≤2*eps t y z+D y z ∧ 2*(2*eps t y z+D y z)≤A t y z-1 := by
  have hd : 0≤D y z := by unfold D; positivity
  have he : eps t y z=y*(t-z)+(t-y) := by unfold eps A M D; ring
  have htz : 0≤t-z := by omega
  have hty : 0≤t-y := by omega
  have hp : 0≤eps t y z := by rw [he]; positivity
  have hinner : 1≤y*(z-3)-3 := by
    have h := mul_le_mul_of_nonneg_left (show 1≤z-3 by omega) (show 0≤y by omega)
    nlinarith
  have hprod : 4≤t*(y*(z-3)-3) := by
    have h := mul_le_mul_of_nonneg_left hinner (show 0≤t by omega)
    nlinarith
  have hid : A t y z-1-2*(2*eps t y z+D y z)=
      t*(y*(z-3)-3)+2*D y z-4 := by unfold eps A M D; ring
  exact ⟨hp,by omega,by omega,by omega⟩

private theorem positive_heads (t y z : ℤ) (ht : 4≤t) (hy : 4≤y) (hz : 4≤z) :
    0<A t y z ∧ 0<B t y ∧ 0<L t z ∧ 0<M t y z ∧
    0<2*M t y z-D y z ∧ z+1≤D y z := by
  have hm : 2*M t y z-D y z=2*t*y*z+D y z := by unfold M; ring
  rw [hm]
  have hD : z+1≤D y z := by
    unfold D
    have h := mul_le_mul_of_nonneg_right (show 1≤y by omega) (show 0≤z by omega)
    nlinarith
  refine ⟨?_,?_,?_,?_,?_,hD⟩ <;> dsimp [A,B,L,M,D] <;> positivity

/- The four inequalities here are supplied by explicit floor constructions,
never assumed in the public endpoint. -/
private theorem ascending_gates (t y z v w : ℤ)
    (hy : 4≤y) (hz : 4≤z) (hyt : y≤t) (hzt : z≤t) (hw : 0≤w)
    (h1 : B t y+D y z≤2*(M t y z+v*A t y z))
    (h2 : M t y z+v*A t y z≤B t y)
    (h3 : 2*L t z+2*D y z-z≤
      4*(M t y z+v*A t y z)+2*(2*B t y-1)*w)
    (h4 : M t y z+v*A t y z+w*B t y≤L t z) :
    Gates true t y z v w := by
  have first := first_gates t y z hy hz hyt hzt
  have hp := positive_heads t y z (by omega) hy hz
  have hD := hp.2.2.2.2.2
  intro j; fin_cases j
  all_goals dsimp [oldSeam,newSeam,oldHead,newHead]
  all_goals constructor <;> constructor <;> nlinarith

private theorem reverse_gates (t y z v : ℤ)
    (hy : 4≤y) (hz : 4≤z) (hyt : y≤t) (hzt : z≤t)
    (hBL : 2*L t z+1≤B t y) (hLM : 0<L t z-M t y z)
    (hlo : B t y-L t z<(v+1)*A t y z-M t y z)
    (hhi : 4*((v+1)*A t y z-M t y z)≤
      4*B t y-2*L t z+z-2*D y z-2) : Gates false t y z v 0 := by
  have first := first_gates t y z hy hz hyt hzt
  have hp := positive_heads t y z (by omega) hy hz
  have hD := hp.2.2.2.2.2
  intro j; fin_cases j
  all_goals dsimp [oldSeam,newSeam,oldHead,newHead]
  all_goals constructor <;> constructor <;> nlinarith

private theorem dyadic_split (m n : ℕ) (h : n≤m) :
    (2:ℤ)^m=(2:ℤ)^(m-n)*2^n := by
  rw [←pow_add, Nat.sub_add_cancel h]

private theorem dyadic_four (n : ℕ) (hn : 2≤n) : (4:ℤ)≤2^n := by
  simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hn

end D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie
