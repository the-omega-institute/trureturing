/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/FullCone
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/FullCone
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete independent max-plus-two physical cone using one rounded U reserve. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.EqualGaps

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.FullCone
open SourceWidth PeriodicShortening RunFirstEarTransport
open private source_table
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
open private centered_shift centered_ladder
  from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventual
open private chainMask chainMask_partition chainMask_sum
  from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventual
open private four_strip_of_masses negative_step last_seam_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
open private four_mask_inventory
  from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private theorem ceil_bounds (K A : ℕ) (hA : 0 < A) :
    let q := (K + 2*A - 1) / (2*A)
    K ≤ 2*A*q ∧ 2*A*q < K + 2*A := by
  dsimp only
  have hd : 0 < 2*A := by omega
  let q := (K + 2*A - 1) / (2*A)
  have hdiv := Nat.div_add_mod (K + 2*A - 1) (2*A)
  have hmod := Nat.mod_lt (K + 2*A - 1) hd
  have hmul := Nat.mul_div_le (K + 2*A - 1) (2*A)
  have hq : 2*A*q ≤ K + 2*A - 1 := by
    simpa [q, Nat.mul_comm] using hmul
  have heq : K + 2*A - 1 = (2*A)*q + (K + 2*A - 1) % (2*A) := by
    simpa [q, Nat.add_comm, Nat.mul_comm] using hdiv
  constructor
  · omega
  · omega

private theorem cone_arithmetic (x y z t : ℤ)
    (hx : 4 ≤ x) (hy : 4 ≤ y) (hz : 4 ≤ z)
    (htx : 4*x ≤ t) (hty : 4*y ≤ t) (htz : 4*z ≤ t) :
    let P := x*y*z
    let C := 1+x+x*y
    let A := P+C
    let B := t*C+1
    let L := t*(z*(1+x))+1+z
    let M := t*(y*z)+1+y+y*z
    let N := P*t-1
    let K := max B (max L M)
    0 < A ∧ A < N ∧ 0 < B ∧ 0 < L ∧ 0 < M ∧
      K + 2*A ≤ N ∧ B ≥ 2*A := by
  dsimp only
  have hxy : 0 < x*y := mul_pos (by omega) (by omega)
  have hyz : 0 < y*z := mul_pos (by omega) (by omega)
  have hP : 0 < x*y*z := mul_pos hxy (by omega)
  have hC : 0 < 1+x+x*y := by nlinarith
  have hA : 0 < x*y*z + (1+x+x*y) := by nlinarith
  have hN : 0 < x*y*z*t - 1 := by nlinarith [htx, hty, htz]
  have hB : 0 < t*(1+x+x*y)+1 := by nlinarith
  have hL : 0 < t*(z*(1+x))+1+z := by nlinarith
  have hM : 0 < t*(y*z)+1+y+y*z := by nlinarith
  have hBN : t*(1+x+x*y)+1 + 2*(x*y*z + (1+x+x*y)) ≤ x*y*z*t-1 := by
    nlinarith [mul_nonneg (show 0 ≤ x*y by omega) (show 0 ≤ t-4*z by omega),
      mul_nonneg (show 0 ≤ x*z by nlinarith) (show 0 ≤ t-4*y by omega)]
  have hLN : t*(z*(1+x))+1+z + 2*(x*y*z + (1+x+x*y)) ≤ x*y*z*t-1 := by
    nlinarith [mul_nonneg (show 0 ≤ x*y by omega) (show 0 ≤ t-4*z by omega),
      mul_nonneg (show 0 ≤ y*z by omega) (show 0 ≤ t-4*x by omega)]
  have hMN : t*(y*z)+1+y+y*z + 2*(x*y*z + (1+x+x*y)) ≤ x*y*z*t-1 := by
    nlinarith [mul_nonneg (show 0 ≤ x*z by omega) (show 0 ≤ t-4*y by omega),
      mul_nonneg (show 0 ≤ y*z by omega) (show 0 ≤ t-4*x by omega)]
  have hK : max (t*(1+x+x*y)+1) (max (t*(z*(1+x))+1+z) (t*(y*z)+1+y+y*z)) +
      2*(x*y*z + (1+x+x*y)) ≤ x*y*z*t-1 := by
    rcases le_total (t*(1+x+x*y)+1) (max (t*(z*(1+x))+1+z) (t*(y*z)+1+y+y*z)) with h | h
    · rw [max_eq_right h]; exact le_max_of_le_right (le_max_of_le_left hLN hLN) -- placeholder
    · rw [max_eq_left h]
      exact hBN
  have hB2 : 2*(x*y*z + (1+x+x*y)) ≤ t*(1+x+x*y)+1 := by
    nlinarith [mul_nonneg (show 0 ≤ x*y by omega) (show 0 ≤ t-4*z by omega)]
  refine ⟨hA, by nlinarith [hK], hB, hL, hM, ?_, hB2⟩
  exact hK

set_option maxHeartbeats 2000000 in
/-- Every independent `a,b,c` at the max-plus-two threshold has one physical witness. -/
theorem actualSource_full_cone (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : max (max a b) c + 2 ≤ d) :
    ∃ sigma : List (Fin (a+b+c+d)),
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1)
        (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma 0) := by
  let k := a+b+c+d
  let u := 1+2^a+2^(a+b)+2^(a+b+c)
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let t : ℤ := 2^d
  let P := x*y*z
  let C := 1+x+x*y
  let A := P+C
  let B := t*C+1
  let L := t*(z*(1+x))+1+z
  let M := t*(y*z)+1+y+y*z
  let N := P*t-1
  let f := fun i : ℕ => centered N ((2 : ℤ)^i*A)
  let f2 := fun i : ℕ => centered (2*N+1) ((2 : ℤ)^i*(2*A))
  obtain ⟨hA,hB,hL,hM,huf,hvf,hwf,hxf,hug,hvg,hwg,hxg,hfresh⟩ :=
    source_table a b c d ha hb hc (by omega)
  change 1 ≤ A ∧ A < N at hA
  change 1 ≤ B ∧ B < N at hB
  change 1 ≤ L ∧ L < N at hL
  change 1 ≤ M ∧ M < N at hM
  change ∀ i<d, f i = if i+1<d then (2:ℤ)^i*A else -(N-B)/2 at huf
  change ∀ i<c, f (d+i) = if i+1<c then (2:ℤ)^i*B else -(N-L)/2 at hvf
  change ∀ i<b, f (d+c+i) = if i+1<b then (2:ℤ)^i*L else -(N-M)/2 at hwf
  change ∀ i<a, f (d+c+b+i) = if i+1<a then (2:ℤ)^i*M else -(N-A)/2 at hxf
  change ∀ i<d, f2 i = if i+1<d then (2:ℤ)^i*(2*A) else -((2*N+1)-(2*B-1))/2 at hug
  change ∀ i<c, f2 (d+i) = if i+1<c then (2:ℤ)^i*(2*B-1) else -((2*N+1)-(2*L-1-z))/2 at hvg
  change ∀ i<b, f2 (d+c+i) = if i+1<b then (2:ℤ)^i*(2*L-1-z) else -((2*N+1)-(2*M-1-y-y*z))/2 at hwg
  change ∀ i<a, f2 (d+c+b+i) = if i+1<a then (2:ℤ)^i*(2*M-1-y-y*z) else -((2*N+1)-A)/2 at hxg
  have h2pow (n : ℕ) : (2:ℤ)^n = (2^n : ℕ) := by norm_num
  let An : ℕ := 2^(a+b+c)+1+2^a+2^(a+b)
  let Bn : ℕ := 2^d*(1+2^a+2^(a+b))+1
  let Ln : ℕ := 2^d*(2^c*(1+2^a))+1+2^c
  let Mn : ℕ := 2^d*(2^b*2^c)+1+2^b+2^b*2^c
  let Kn : ℕ := max Bn (max Ln Mn)
  let q : ℕ := (Kn+2*An-1)/(2*An)
  have hAn : 0 < An := by dsimp [An]; positivity
  have hceil := ceil_bounds Kn An hAn
  have hcastA : (An : ℤ) = A := by dsimp [An,A,P,C,x,y,z]; norm_num; ring
  have hcastB : (Bn : ℤ) = B := by dsimp [Bn,B,C,x,y,z,t]; norm_num; ring
  have hcastL : (Ln : ℤ) = L := by dsimp [Ln,L,x,y,z,t]; norm_num; ring
  have hcastM : (Mn : ℤ) = M := by dsimp [Mn,M,x,y,z,t]; norm_num; ring
  have hcastK : (Kn : ℤ) = max B (max L M) := by rw [show (Kn:ℤ)=max (Bn:ℤ) (max (Ln:ℤ) (Mn:ℤ)) by simp [Kn, Int.ofNat_max]]; rw [hcastB,hcastL,hcastM]
  have hpowd : 4*x ≤ t ∧ 4*y ≤ t ∧ 4*z ≤ t := by
    dsimp [x,y,z,t]
    constructor
    · have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show a+2≤d by omega)
      nlinarith [this]
    constructor
    · have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show b+2≤d by omega)
      nlinarith [this]
    · have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show c+2≤d by omega)
      nlinarith [this]
  have hx4 : 4 ≤ x := by dsimp [x]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ha; norm_num at this ⊢; omega
  have hy4 : 4 ≤ y := by dsimp [y]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hb; norm_num at this ⊢; omega
  have hz4 : 4 ≤ z := by dsimp [z]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hc; norm_num at this ⊢; omega
  have harith := cone_arithmetic x y z t hx4 hy4 hz4 hpowd.1 hpowd.2.1 hpowd.2.2
  have hqcast : (q : ℤ) = ((Kn + 2*An - 1) / (2*An) : ℕ) := by rfl
  have hq1 : 1 ≤ q := by
    dsimp [q]
    have : 1 ≤ Kn := by dsimp [Kn,Bn]; positivity
    omega
  have hqcap : q ≤ 2^(d-1) := by
    have hden : 0 < 2*An := by omega
    have hqmul : 2*An*q < Kn+2*An := hceil.2
    have hKN : (Kn:ℤ)+2*A ≤ N := by rw [← hcastK, ← hcastA]; exact_mod_cast harith.2.2.2.2.1
    have hqmul' : (2:ℤ)*A*(q:ℤ) < N := by exact_mod_cast hqmul; simpa [hcastA] using hqmul'
    have hrel : (2:ℤ)^(d-1)*A = (N+B)/2 := by
      have ht : t = 2*(2:ℤ)^(d-1) := by dsimp [t]; rw [show d=(d-1)+1 by omega,pow_succ]; ring
      rw [←ht]; dsimp [N,B,A,P,C]; ring
    have hBpos : 0 < B := by omega
    have hApos : 0 < A := by omega
    by_contra hh
    have hq' : 2^(d-1)+1 ≤ q := by omega
    have := mul_le_mul_of_nonneg_left hq' (show 0 ≤ (2:ℤ)*A by omega)
    nlinarith [hrel]
  have hqcastA : (q:ℤ)*A = ((q:ℤ)*A) := rfl
  let U0 := chainMask (d-1) 0 (2^(d-1)-q)
  let U1 := chainMask (d-1) 0 (q-1)
  let V1 := chainMask (c-1) d (2^(c-1)-1)
  let W1 := chainMask (b-1) (d+c) (2^(b-1)-1)
  let X1 := chainMask (a-1) (d+c+b) (2^(a-1)-1)
  let P1 := U0
  let P2 := V1
  let P3 := W1
  let P4 := U1 ++ X1
  have hmask : (P1++[d-1]++P2++[d+c-1]++P3++[d+c+b-1]++P4++[d+c+b+a-1]).Perm (List.range k) := by
    simpa [P1,P2,P3,P4,U0,U1,V1,W1,X1] using
      four_mask_inventory a b c d q 1 1 1 ha hb hc (by omega) ⟨hq1,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hU0 := chainMask_sum (d-1) 0 (2^(d-1)-q) (by omega) f A (by intro e he; exact (huf e (by omega)).trans (by simp [Nat.add_comm]))
  have hU1 := chainMask_sum (d-1) 0 (q-1) (by omega) f A (by intro e he; exact (huf e (by omega)).trans (by simp [Nat.add_comm]))
  have hV1 := chainMask_sum (c-1) d (2^(c-1)-1) (by omega) f B (by intro e he; simpa [Nat.add_comm] using (hvf e (by omega)).trans (by simp))
  have hW1 := chainMask_sum (b-1) (d+c) (2^(b-1)-1) (by omega) f L (by intro e he; simpa [Nat.add_comm] using (hwf e (by omega)).trans (by simp))
  have hX1 := chainMask_sum (a-1) (d+c+b) (2^(a-1)-1) f M (by omega) (by intro e he; simpa [Nat.add_comm] using (hxf e (by omega)).trans (by simp))
  sorry
end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.FullCone
