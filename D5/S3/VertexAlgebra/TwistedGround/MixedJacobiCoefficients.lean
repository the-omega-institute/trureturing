/- GID: D5/S3/VertexAlgebra/TwistedGround/MixedJacobiCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/MixedJacobiCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual energy support and both signed finite coefficient transports. -/
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobi
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceClosure

/-! Finite coefficient calculations for the actual mixed Jacobi law. All
supports below follow from actual energy covariance, before convolution.
The two ordered products use the original ordered slots of actualForm. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator DirectSum
namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace
open LatticeHalfFockFiniteCorrection (sourceWeight)
open LatticeAllStateField LatticePositiveEnergy LatticeInvolution
open ActualChargedAdjoint LatticeSugawaraCurrents LatticeSugawaraVirasoro
open HalfFock.LatticeHalfFockParityField
open private T originalL1 original_l1_grade original_l1_fixed lowering_eigen
  from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private signed_supported_transform
  from D5.S3.VertexAlgebra.TwistedGround.MixedJacobi

/-- Actual rank-twenty-four integer-energy vectors below weight two vanish. -/
theorem integer_energy_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (w : ℤ) (x : ActualTensor D hu)
    (hx : actualTensorL0 D hu x = (w : ℂ) • x) (hw : w < 2) : x = 0 := by
  classical
  let b := actualAmbientBasis D hu
  apply b.repr.injective
  ext ib
  have hc := congrArg (fun z => b.repr z ib) hx
  rw [actualTensorL0_repr] at hc
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  have nonneg : 0 ≤ (oddWeight D ib.1 : ℤ) := by positivity
  have scalar : ((D.rank : ℂ)/16+(oddWeight D ib.1 : ℂ)/2)-(w : ℂ) ≠ 0 := by
    intro hs
    have hs' : (12 : ℂ)+4*(oddWeight D ib.1 : ℂ)-8*(w : ℂ) = 0 := by
      rw [h24] at hs
      linear_combination 8*hs
    have hs'' : (12 : ℤ)+4*(oddWeight D ib.1 : ℤ)-8*w = 0 := by
      exact_mod_cast hs'
    omega
  have product : (((D.rank : ℂ)/16+(oddWeight D ib.1 : ℂ)/2)-(w : ℂ))*
      b.repr x ib = 0 := by linear_combination hc
  exact (mul_eq_zero.mp product).resolve_left scalar

/-- Actual tensor lowering shifts an integer energy by its lowering index. -/
theorem lowering_integer_energy (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (w : ℤ) (x : ActualTensor D hu)
    (hx : actualTensorL0 D hu x = (w : ℂ) • x) (i : ℕ) :
    actualTensorL0 D hu ((T D hu ^ i) x) =
      ((w-(i : ℤ) : ℤ) : ℂ) • ((T D hu ^ i) x) := by
  have input : actualTensorL0 D hu x =
      ((D.rank : ℂ)/16+((2*w-3 : ℤ) : ℂ)/2) • x := by
    rw [hx]
    congr 1
    rw [h24]
    push_cast
    ring
  have output := lowering_eigen D hu (2*w-3) x input i
  have scalar : (D.rank : ℂ)/16+((2*w-3-2*(i : ℤ) : ℤ) : ℂ)/2 =
      ((w-(i : ℤ) : ℤ) : ℂ) := by rw [h24]; push_cast; ring
  rw [scalar] at output
  exact output

/-- An original homogeneous source mode has the displayed actual integer energy. -/
theorem original_mode_integer_energy (D : LatticeData) (hu : IsUnit D.G.det)
    (d w t : ℤ) (a : Carrier D) (ha : a ∈ grade D d) (x : ActualTensor D hu)
    (hx : actualTensorL0 D hu x = (w : ℂ) • x) :
    actualTensorL0 D hu ((correctedField D hu a).coeff (-2*t-2) x) =
      ((w+d-t-1 : ℤ) : ℂ) • ((correctedField D hu a).coeff (-2*t-2) x) := by
  have cov := LinearMap.congr_fun
    (HalfFock.ActualEnergyCovariance.correctedField_L_zero_commutator D hu d a ha
      (-2*t-2)) x
  change actualTensorL0 D hu ((correctedField D hu a).coeff (-2*t-2) x) -
    (correctedField D hu a).coeff (-2*t-2) (actualTensorL0 D hu x) =
    (((-2*t-2 : ℤ) : ℂ)/2+(d : ℂ)) •
      (correctedField D hu a).coeff (-2*t-2) x at cov
  rw [hx, map_smul, sub_eq_iff_eq_add] at cov
  rw [cov, ← add_smul]
  congr 1
  push_cast
  ring

/-- The first ordered actual source product at the signed Jacobi indices. -/
def mixedSourceFirst (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (d m n r : ℤ) (a b : Carrier D) (u v : ActualTensor D hu)
    (p q L k : ℕ) : ℂ :=
  let Q : ℤ := 2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ)
  let R : ℤ := 2*d-(L : ℤ)-m-r-2
  actualForm D hu ((T D hu ^ p) v)
    ((correctedField D hu ((originalL1 D ^ L) a)).coeff (-2*(r+R-(k : ℤ))-2)
      ((correctedField D hu b).coeff (-2*(Q+(k : ℤ))-2) ((T D hu ^ q) u)))

/-- The second ordered actual source product at the signed Jacobi indices. -/
def mixedSourceSecond (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (d m n r : ℤ) (a b : Carrier D) (u v : ActualTensor D hu)
    (p q L k : ℕ) : ℂ :=
  let Q : ℤ := 2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ)
  let R : ℤ := 2*d-(L : ℤ)-m-r-2
  actualForm D hu ((T D hu ^ p) v)
    ((correctedField D hu b).coeff (-2*(Q+R-(k : ℤ))-2)
      ((correctedField D hu ((originalL1 D ^ L) a)).coeff
        (-2*(r+(k : ℤ))-2) ((T D hu ^ q) u)))

private theorem mixedSourceSecond_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H : ℕ) (d m n r : ℤ) (a b : Carrier D)
    (ha : a ∈ grade D d) (u v : ActualTensor D hu)
    (huH : actualTensorL0 D hu u = (H : ℂ) • u) (p q L k : ℕ)
    (outside : (H : ℤ)+d-r-3 < (q : ℤ)+(L : ℤ)+(k : ℤ)) :
    mixedSourceSecond D hu H d m n r a b u v p q L k = 0 := by
  have energy := original_mode_integer_energy D hu (d-(L : ℤ))
    ((H : ℤ)-(q : ℤ)) (r+(k : ℤ)) ((originalL1 D ^ L) a)
    (original_l1_grade D hu d a ha L) ((T D hu ^ q) u)
    (lowering_integer_energy D hu h24 (H : ℤ) u huH q)
  have zero := integer_energy_zero D hu h24
    (((H : ℤ)-(q : ℤ))+(d-(L : ℤ))-(r+(k : ℤ))-1) _ energy (by omega)
  simp only [mixedSourceSecond, zero, map_zero]

private theorem mixedSourceFirst_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ) (a b : Carrier D)
    (hb : b ∈ grade D E) (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (u v : ActualTensor D hu) (huH : actualTensorL0 D hu u = (H : ℂ) • u)
    (p q L k : ℕ) (outside : (K : ℤ)+d-m-3 < (p : ℤ)+(k : ℤ)) :
    mixedSourceFirst D hu H d m n r a b u v p q L k = 0 := by
  let Q : ℤ := 2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ)
  have energy := original_mode_integer_energy D hu E ((H : ℤ)-(q : ℤ))
    (Q+(k : ℤ)) b hb ((T D hu ^ q) u)
    (lowering_integer_energy D hu h24 (H : ℤ) u huH q)
  have zero := integer_energy_zero D hu h24
    (((H : ℤ)-(q : ℤ))+E-(Q+(k : ℤ))-1) _ energy (by dsimp [Q]; omega)
  simp only [mixedSourceFirst, Q, zero, map_zero]

/- The two finite diagonal maps are (j,h) ↦ (t=j+h,j), followed by
(ell,t) ↦ (k=ell+t,ell). Thus k=j+ell+h and every inverse is a Nat
subtraction under its displayed triangle bound. No infinite binomial
support is asserted for signed parameters. -/
private theorem twice_signed_transform (N L : ℕ) (r B : ℂ) (f : ℕ → ℂ)
    (tail : ∀ k, N ≤ k → f k = 0) :
    (∑ ell ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
      Ring.choose (L : ℂ) ell * Ring.choose r j * (-1 : ℂ)^h *
        Ring.choose (B-(j : ℂ)-(ell : ℂ)) h * f (j+ell+h)) =
      ∑ k ∈ Finset.range N,
        ((-1 : ℂ)^k * Ring.choose (B-r-(L : ℂ)) k) * f k := by
  calc
    _ = ∑ ell ∈ Finset.range N, Ring.choose (L : ℂ) ell *
        (∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
          Ring.choose r j * (-1 : ℂ)^h * Ring.choose ((B-(ell : ℂ))-(j : ℂ)) h *
            f (ell+(j+h))) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell hell
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro h hh
      rw [show B-(j : ℂ)-(ell : ℂ) = (B-(ell : ℂ))-(j : ℂ) by ring,
        show j+ell+h = ell+(j+h) by omega]
      ring
    _ = ∑ ell ∈ Finset.range N, ∑ t ∈ Finset.range N,
        Ring.choose (L : ℂ) ell * (-1 : ℂ)^t *
          Ring.choose ((B-r)-(ell : ℂ)) t * f (ell+t) := by
      apply Finset.sum_congr rfl
      intro ell hell
      rw [signed_supported_transform N (fun t => f (ell+t))
        (fun t ht => tail (ell+t) (by omega)) r (B-(ell : ℂ)), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [show B-(ell : ℂ)-r = (B-r)-(ell : ℂ) by ring]
      ring
    _ = _ := signed_supported_transform N f tail (L : ℂ) (B-r)

/-- The supported signed contraction for the second ordered source product. -/
theorem mixed_first_contraction (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H : ℕ) (d m n r : ℤ) (a b : Carrier D)
    (ha : a ∈ grade D d) (u v : ActualTensor D hu)
    (huH : actualTensorL0 D hu u = (H : ℂ) • u) (p q L N : ℕ)
    (hN : ((H : ℤ)+d-r-2).toNat ≤ N) :
    (∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
      Ring.choose (m : ℂ) j * (-1 : ℂ)^h *
        Ring.choose (2*(d : ℂ)-(r : ℂ)-(L : ℂ)-2-(j : ℂ)) h *
          mixedSourceSecond D hu H d m n r a b u v p q L (j+h)) =
      ∑ k ∈ Finset.range N,
        ((-1 : ℂ)^k * Ring.choose ((2*d-(L : ℤ)-m-r-2 : ℤ) : ℂ) k) *
          mixedSourceSecond D hu H d m n r a b u v p q L k := by
  have tail (k : ℕ) (hk : N ≤ k) :
      mixedSourceSecond D hu H d m n r a b u v p q L k = 0 := by
    apply mixedSourceSecond_zero D hu h24 H d m n r a b ha u v huH p q L k
    omega
  have diagonal := signed_supported_transform N
    (mixedSourceSecond D hu H d m n r a b u v p q L) tail (m : ℂ)
    (2*(d : ℂ)-(r : ℂ)-(L : ℂ)-2)
  have scalar : 2*(d : ℂ)-(r : ℂ)-(L : ℂ)-2-(m : ℂ) =
      ((2*d-(L : ℤ)-m-r-2 : ℤ) : ℂ) := by push_cast; ring
  simpa only [scalar] using diagonal

/-- The twice-supported signed contraction for the first ordered source product. -/
theorem mixed_second_contraction (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ) (a b : Carrier D)
    (hb : b ∈ grade D E) (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (u v : ActualTensor D hu) (huH : actualTensorL0 D hu u = (H : ℂ) • u)
    (p q L N : ℕ) (hN : ((K : ℤ)+d-m-2).toNat ≤ N) :
    (∑ ell ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
      Ring.choose (L : ℂ) ell * Ring.choose (r : ℂ) j * (-1 : ℂ)^h *
        Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
          mixedSourceFirst D hu H d m n r a b u v p q L (j+ell+h)) =
      ∑ k ∈ Finset.range N,
        ((-1 : ℂ)^k * Ring.choose ((2*d-(L : ℤ)-m-r-2 : ℤ) : ℂ) k) *
          mixedSourceFirst D hu H d m n r a b u v p q L k := by
  have tail (k : ℕ) (hk : N ≤ k) :
      mixedSourceFirst D hu H d m n r a b u v p q L k = 0 := by
    apply mixedSourceFirst_zero D hu h24 H K d m n r E a b hb hE u v huH p q L k
    omega
  have diagonal := twice_signed_transform N L (r : ℂ)
    (2*(d : ℂ)-(m : ℂ)-2)
    (mixedSourceFirst D hu H d m n r a b u v p q L) tail
  have scalar : 2*(d : ℂ)-(m : ℂ)-2-(r : ℂ)-(L : ℂ) =
      ((2*d-(L : ℤ)-m-r-2 : ℤ) : ℂ) := by push_cast; ring
  simpa only [scalar] using diagonal

private theorem lowering_triangle_to_cube (N : ℕ) (f : ℕ → ℕ → ℕ → ℂ)
    (tail : ∀ i L h, N ≤ i+L+h → f i L h = 0) :
    (∑ q ∈ Finset.range N, ∑ i ∈ Finset.range (q+1),
      ∑ L ∈ Finset.range (q-i+1), f i L (q-i-L)) =
      ∑ i ∈ Finset.range N, ∑ L ∈ Finset.range N, ∑ h ∈ Finset.range N, f i L h := by
  rw [Finset.sum_range_diag_flip N
    (fun i s => ∑ L ∈ Finset.range (s+1), f i L (s-L))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_range_diag_flip (N-i) (fun L h => f i L h)]
  have hiN := Finset.mem_range.mp hi
  calc
    _ = ∑ L ∈ Finset.range (N-i), ∑ h ∈ Finset.range N, f i L h := by
      apply Finset.sum_congr rfl
      intro L hL
      have hLN := Finset.mem_range.mp hL
      apply Finset.sum_subset (Finset.range_mono (by omega : N - i - L ≤ N))
      intro h hh outside
      apply tail
      have := Finset.mem_range.not.mp outside
      omega
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega : N - i ≤ N))
      intro L hL outside
      apply Finset.sum_eq_zero
      intro h hh
      apply tail
      have := Finset.mem_range.not.mp outside
      omega

/-- Literal first-input reindexing q_target=i+L+h. The signed-output
alternative is consumed before the transformed triangle is padded. Its
actual rightmost output has weight H+d-r-1-i-L-(j+h); every term outside
that support is zero, including negative, zero and weight-one outputs. -/
theorem mixed_first_input_reindexed_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (j N : ℕ) (hN : ((H : ℤ)+d-r-2).toNat ≤ N) :
    normalizedCoefficient D hu (m+n-(j : ℤ))
      (((fixedParitySlice D hu (-1)
        (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u) v E b =
    ∑ p ∈ Finset.range (K-1), ∑ i ∈ Finset.range N,
      ∑ L ∈ Finset.range N, ∑ h ∈ Finset.range N,
        (((-1 : ℂ)^(m+n+r+2-(p : ℤ)-(H : ℤ)-d+(i : ℤ)+(L : ℤ)))/
          ((p.factorial : ℂ)*(i.factorial : ℂ)*(L.factorial : ℂ))) *
        ((-1 : ℂ)^h * Ring.choose
          (2*(d : ℂ)-(r : ℂ)-(L : ℂ)-2-(j : ℂ)) h) *
        actualForm D hu ((T D hu ^ p) v.val)
          ((correctedField D hu b.val).coeff
            (-2*((2*(H : ℤ)-n-r-2+(p : ℤ)-(i : ℤ))+
              (2*d-(L : ℤ)-m-r-2)-((j+h : ℕ) : ℤ))-2)
            ((correctedField D hu ((originalL1 D ^ L) a.val)).coeff
              (-2*(r+((j+h : ℕ) : ℤ))-2) ((T D hu ^ i) u.val))) := by
  classical
  let f (p i L h : ℕ) : ℂ :=
    (((-1 : ℂ)^(m+n+r+2-(p : ℤ)-(H : ℤ)-d+(i : ℤ)+(L : ℤ)))/
      ((p.factorial : ℂ)*(i.factorial : ℂ)*(L.factorial : ℂ))) *
    ((-1 : ℂ)^h * Ring.choose
      (2*(d : ℂ)-(r : ℂ)-(L : ℂ)-2-(j : ℂ)) h) *
    mixedSourceSecond D hu H d m n r a.val b.val u.val v.val p i L (j+h)
  change _ = ∑ p ∈ Finset.range (K-1), ∑ i ∈ Finset.range N,
    ∑ L ∈ Finset.range N, ∑ h ∈ Finset.range N, f p i L h
  have zero (p i L h : ℕ)
      (outside : (H : ℤ)+d-r-3 < (i : ℤ)+(L : ℤ)+(j : ℤ)+(h : ℤ)) :
      f p i L h = 0 := by
    dsimp only [f]
    rw [mixedSourceSecond_zero D hu h24 H d m n r a.val b.val a.property.1
      u.val v.val huH p i L (j+h) (by push_cast; omega), mul_zero]
  have tail (p i L h : ℕ) (outside : N ≤ i+L+h) : f p i L h = 0 := by
    apply zero
    omega
  have signed := mixed_first_input_signed_support D hu h24 H K d
    (m+n-(j : ℤ)) (r+(j : ℤ)) E a u v huH hvK b
  dsimp only at signed
  rcases signed with ⟨negative, result⟩ | ⟨W, hW, result⟩
  · rw [result]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro L hL
    apply Finset.sum_eq_zero
    intro h hh
    apply zero
    omega
  · rw [result]
    have bound : W-1 ≤ N := by omega
    calc
      _ = ∑ p ∈ Finset.range (K-1), ∑ q ∈ Finset.range (W-1),
          ∑ i ∈ Finset.range (q+1), ∑ L ∈ Finset.range (q-i+1), f p i L (q-i-L) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro L hL
        have hiq : i ≤ q := by have := Finset.mem_range.mp hi; omega
        have hLq : L ≤ q-i := by have := Finset.mem_range.mp hL; omega
        have split : q = i+L+(q-i-L) := by omega
        have phase : (W : ℤ)+(m+n-(j : ℤ)+1-(p : ℤ)-2*(W : ℤ)+(q : ℤ)) =
            (m+n+r+2-(p : ℤ)-(H : ℤ)-d+(i : ℤ)+(L : ℤ))+
              ((q-i-L : ℕ) : ℤ) := by omega
        have leftExponent :
            2*(m+n-(j : ℤ)+1-(p : ℤ)-2*(W : ℤ)+(q : ℤ)) =
            -2*((2*(H : ℤ)-n-r-2+(p : ℤ)-(i : ℤ))+
              (2*d-(L : ℤ)-m-r-2)-((j+(q-i-L) : ℕ) : ℤ))-2 := by omega
        have rightExponent :
            -2*(r+(j : ℤ))-2-2*((q-i : ℕ) : ℤ)+2*(L : ℤ) =
            -2*(r+((j+(q-i-L) : ℕ) : ℤ))-2 := by omega
        have parameter : 2*(d : ℂ)-((r+(j : ℤ) : ℤ) : ℂ)-(L : ℂ)-2 =
            2*(d : ℂ)-(r : ℂ)-(L : ℂ)-2-(j : ℂ) := by push_cast; ring
        dsimp only [f, mixedSourceSecond]
        rw [phase, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast,
          leftExponent, rightExponent, parameter]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = ∑ p ∈ Finset.range (K-1), ∑ q ∈ Finset.range N,
          ∑ i ∈ Finset.range (q+1), ∑ L ∈ Finset.range (q-i+1), f p i L (q-i-L) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_subset (Finset.range_mono bound)
        intro q hq outside
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro L hL
        apply zero
        have hiq : i ≤ q := by have := Finset.mem_range.mp hi; omega
        have hLq : L ≤ q-i := by have := Finset.mem_range.mp hL; omega
        have := Finset.mem_range.not.mp outside
        omega
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        exact lowering_triangle_to_cube N (f p) (tail p)

/-- The actual all-source supplier at P=r,
Q=2H-n-r-2+p-q and R=2d-L-m-r-2, after the two supported signed
transforms. The first and second ordered source products both remain.
This is the finite source calculation needed by the mixed law; it does
not assume that law or identify the original space with its restricted dual. -/
theorem mixed_source_finite_cancellation (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (u v : ActualTensor D hu) (huH : actualTensorL0 D hu u = (H : ℂ) • u)
    (p q L N : ℕ)
    (hNfirst : ((H : ℤ)+d-r-2).toNat ≤ N)
    (hNsecond : ((K : ℤ)+d-m-2).toNat ≤ N) :
    let Q : ℤ := 2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ)
    let R : ℤ := 2*d-(L : ℤ)-m-r-2
    let first (k : ℕ) : ℂ := actualForm D hu ((T D hu ^ p) v)
      ((correctedField D hu ((originalL1 D ^ L) a.val)).coeff (-2*(r+R-(k : ℤ))-2)
        ((correctedField D hu b.val).coeff (-2*(Q+(k : ℤ))-2) ((T D hu ^ q) u)))
    let second (k : ℕ) : ℂ := actualForm D hu ((T D hu ^ p) v)
      ((correctedField D hu b.val).coeff (-2*(Q+R-(k : ℤ))-2)
        ((correctedField D hu ((originalL1 D ^ L) a.val)).coeff
          (-2*(r+(k : ℤ))-2) ((T D hu ^ q) u)))
    (∑ᶠ j : ℕ, Ring.choose (r : ℂ) j *
      actualForm D hu ((T D hu ^ p) v)
        ((correctedField D hu
          (((Y D ((originalL1 D ^ L) a.val))[[R+(j : ℤ)]]) b.val)).coeff
            (-2*(r+Q-(j : ℤ))-2) ((T D hu ^ q) u))) =
      (∑ ell ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
        Ring.choose (L : ℂ) ell * Ring.choose (r : ℂ) j * (-1 : ℂ)^h *
          Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h * first (j+ell+h)) -
      (-1 : ℂ)^R *
        (∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
          Ring.choose (m : ℂ) j * (-1 : ℂ)^h *
            Ring.choose (2*(d : ℂ)-(r : ℂ)-(L : ℂ)-2-(j : ℂ)) h * second (j+h)) := by
  classical
  intro Q R first second
  have firstTail (k : ℕ) (hk : N ≤ k) : first k = 0 := by
    exact mixedSourceFirst_zero D hu h24 H K d m n r E a.val b.val b.property.1
      hE u v huH p q L k (by omega)
  have secondTail (k : ℕ) (hk : N ≤ k) : second k = 0 := by
    exact mixedSourceSecond_zero D hu h24 H d m n r a.val b.val a.property.1
      u v huH p q L k (by omega)
  have firstContraction := mixed_second_contraction D hu h24 H K d m n r E
    a.val b.val b.property.1 hE u v huH p q L N hNsecond
  have secondContraction := mixed_first_contraction D hu h24 H d m n r
    a.val b.val a.property.1 u v huH p q L N hNfirst
  dsimp only [first, second, Q, R]
  dsimp only [mixedSourceFirst, mixedSourceSecond] at firstContraction secondContraction
  change _ = _ - (-1 : ℂ)^R * _
  rw [firstContraction, secondContraction]
  let form := actualForm D hu ((T D hu ^ p) v)
  have fixed : theta D ((originalL1 D ^ L) a.val) =
      (-1 : ℂ)^(0 : ℤ) • ((originalL1 D ^ L) a.val) := by
    simpa only [zpow_zero, one_smul] using original_l1_fixed D hu a.val a.property.2 L
  have supplier := LatticeHalfFockGroundRightCurrentTransport.first_eigen_arbitrary_second
    D hu ((originalL1 D ^ L) a.val) 0 fixed b.val 0
  obtain ⟨hl, hf, hs, law⟩ := supplier r Q R ((T D hu ^ q) u)
  have paired := congrArg form law
  rw [map_sub, map_finsum form hl, map_finsum form hf, map_finsum form hs] at paired
  simp only [LatticeHalfFockGroundRightCurrentTransport.Calculus.leftTerm,
    LatticeHalfFockGroundRightCurrentTransport.Calculus.firstTerm,
    LatticeHalfFockGroundRightCurrentTransport.Calculus.secondTerm,
    LatticeHalfFockPhysicalRescaling.physicalSlice_mode,
    LatticeAllStateReconstruction.mu, Int.cast_zero, zero_div, add_zero, sub_zero,
    map_smul, smul_eq_mul, LatticeHalfFockGroundRightCurrentTransport.residueWeight] at paired
  have finiteFirst : (∑ᶠ k : ℕ,
      ((-1 : ℂ)^k * Ring.choose (R : ℂ) k) * first k) =
      ∑ k ∈ Finset.range N, ((-1 : ℂ)^k * Ring.choose (R : ℂ) k) * first k := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra outside
    have zero := firstTail k (by simpa using outside)
    exact hk (by simp only [zero, mul_zero])
  have finiteSecond : (∑ᶠ k : ℕ,
      ((-1 : ℂ)^k * Ring.choose (R : ℂ) k) * ((-1 : ℂ)^R * second k)) =
      (-1 : ℂ)^R *
        ∑ k ∈ Finset.range N, ((-1 : ℂ)^k * Ring.choose (R : ℂ) k) * second k := by
    rw [Finset.mul_sum]
    trans ∑ k ∈ Finset.range N,
      ((-1 : ℂ)^k * Ring.choose (R : ℂ) k) * ((-1 : ℂ)^R * second k)
    · apply finsum_eq_sum_of_support_subset
      intro k hk
      by_contra outside
      have zero := secondTail k (by simpa using outside)
      exact hk (by simp only [zero, mul_zero])
    · apply Finset.sum_congr rfl
      intro k hk
      ring
  change _ = (∑ᶠ k : ℕ, ((-1 : ℂ)^k * Ring.choose (R : ℂ) k) * first k) -
    (∑ᶠ k : ℕ, ((-1 : ℂ)^k * Ring.choose (R : ℂ) k) * ((-1 : ℂ)^R * second k)) at paired
  rw [finiteFirst, finiteSecond] at paired
  exact paired

/-- The entire first-input branch, with q_target=i+L+h and
k_source=j+h. Actual output-energy support makes the outer signed sum finite
before the two index changes. The resulting ordered product is the second
source branch, with its literal signed phase retained. -/
theorem mixed_first_input_branch_reindexed (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (N : ℕ) (hN : ((H : ℤ)+d-r-2).toNat ≤ N) :
    (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j *
      (normalizedCoefficient D hu (m+n-(j : ℤ))
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u) v) E b) =
    ∑ p ∈ Finset.range (K-1), ∑ i ∈ Finset.range N, ∑ L ∈ Finset.range N,
      (((-1 : ℂ)^(m+n+r+2-(p : ℤ)-(H : ℤ)-d+(i : ℤ)+(L : ℤ)))/
        ((p.factorial : ℂ)*(i.factorial : ℂ)*(L.factorial : ℂ))) *
      (∑ k ∈ Finset.range N,
        ((-1 : ℂ)^k * Ring.choose ((2*d-(L : ℤ)-m-r-2 : ℤ) : ℂ) k) *
        actualForm D hu ((T D hu ^ p) v.val)
          ((correctedField D hu b.val).coeff
            (-2*((2*(H : ℤ)-n-r-2+(p : ℤ)-(i : ℤ))+
              (2*d-(L : ℤ)-m-r-2)-(k : ℤ))-2)
            ((correctedField D hu ((originalL1 D ^ L) a.val)).coeff
              (-2*(r+(k : ℤ))-2) ((T D hu ^ i) u.val)))) := by
  classical
  have finite : (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j *
      (normalizedCoefficient D hu (m+n-(j : ℤ))
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u) v) E b) =
      ∑ j ∈ Finset.range N, Ring.choose (m : ℂ) j *
        (normalizedCoefficient D hu (m+n-(j : ℤ))
          (((fixedParitySlice D hu (-1)
            (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u) v) E b := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have bound : N ≤ j := by simpa using outside
    have energy := original_mode_integer_energy D hu d (H : ℤ) (r+(j : ℤ))
      a.val a.property.1 u.val huH
    have zero := integer_energy_zero D hu h24 ((H : ℤ)+d-(r+(j : ℤ))-1)
      _ energy (by omega)
    have input : ((fixedParitySlice D hu (-1)
        (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u = 0 := by
      apply Subtype.ext
      change (correctedField D hu a.val).coeff (2*(-(r+(j : ℤ))-1)) u.val = 0
      rw [show 2*(-(r+(j : ℤ))-1) = -2*(r+(j : ℤ))-2 by ring]
      exact zero
    apply hj
    simp only [input, map_zero, LinearMap.zero_apply, DirectSum.zero_apply, mul_zero]
  rw [finite]
  simp_rw [mixed_first_input_reindexed_pairing D hu h24 H K d m n r E a b u v huH hvK
    (N := N) (hN := hN)]
  let c (p i L : ℕ) : ℂ :=
    ((-1 : ℂ)^(m+n+r+2-(p : ℤ)-(H : ℤ)-d+(i : ℤ)+(L : ℤ)))/
      ((p.factorial : ℂ)*(i.factorial : ℂ)*(L.factorial : ℂ))
  change (∑ j ∈ Finset.range N, Ring.choose (m : ℂ) j *
    (∑ p ∈ Finset.range (K-1), ∑ i ∈ Finset.range N, ∑ L ∈ Finset.range N,
      ∑ h ∈ Finset.range N, c p i L *
        ((-1 : ℂ)^h * Ring.choose (2*(d : ℂ)-(r : ℂ)-(L : ℂ)-2-(j : ℂ)) h) *
        mixedSourceSecond D hu H d m n r a.val b.val u.val v.val p i L (j+h))) = _
  calc
    _ = ∑ p ∈ Finset.range (K-1), ∑ i ∈ Finset.range N, ∑ L ∈ Finset.range N,
        c p i L * (∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
          Ring.choose (m : ℂ) j * (-1 : ℂ)^h *
            Ring.choose (2*(d : ℂ)-(r : ℂ)-(L : ℂ)-2-(j : ℂ)) h *
            mixedSourceSecond D hu H d m n r a.val b.val u.val v.val p i L (j+h)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro L hL
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro L hL
      rw [mixed_first_contraction D hu h24 H d m n r a.val b.val a.property.1
        u.val v.val huH p i L N hN]
      rfl

/-- Literal second-input reindexing p_target=i+ell+h,
L=ell+z and k_source=j+ell+h. The actual rightmost b-mode has output
weight K+d-m-1-i-k_source. The signed support split is consumed before
padding; the original source-lowering sum remains its actual finite finsum. -/
theorem mixed_second_input_reindexed_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (j N : ℕ) (hN : ((K : ℤ)+d-m-2).toNat ≤ N) :
    normalizedCoefficient D hu (n+r-(j : ℤ)) u
      (((fixedParitySlice D hu (-1)
        (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b =
    ∑ q ∈ Finset.range (H-1), ∑ i ∈ Finset.range N,
      ∑ ell ∈ Finset.range N, ∑ h ∈ Finset.range N, ∑ᶠ z : ℕ,
        (((-1 : ℂ)^(n+r-(j : ℤ)+1-(i : ℤ)-(H : ℤ)+(q : ℤ)+d-
          2*(ell : ℤ)-(h : ℤ)))/
          ((i.factorial : ℂ)*(q.factorial : ℂ)*(ell.factorial : ℂ)*(z.factorial : ℂ))) *
        Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
        actualForm D hu ((T D hu ^ i) v.val)
          ((correctedField D hu ((originalL1 D ^ (ell+z)) a.val)).coeff
            (-2*(r+(2*d-((ell+z : ℕ) : ℤ)-m-r-2)-((j+ell+h : ℕ) : ℤ))-2)
            ((correctedField D hu b.val).coeff
              (-2*((2*(H : ℤ)-n-r-2+(i : ℤ)-(q : ℤ))+
                ((j+ell+h : ℕ) : ℤ))-2) ((T D hu ^ q) u.val))) := by
  classical
  let f (q i ell h : ℕ) : ℂ := ∑ᶠ z : ℕ,
    (((-1 : ℂ)^(n+r-(j : ℤ)+1-(i : ℤ)-(H : ℤ)+(q : ℤ)+d-
      2*(ell : ℤ)-(h : ℤ)))/
      ((i.factorial : ℂ)*(q.factorial : ℂ)*(ell.factorial : ℂ)*(z.factorial : ℂ))) *
    Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
    mixedSourceFirst D hu H d m n r a.val b.val u.val v.val i q (ell+z) (j+ell+h)
  change _ = ∑ q ∈ Finset.range (H-1), ∑ i ∈ Finset.range N,
    ∑ ell ∈ Finset.range N, ∑ h ∈ Finset.range N, f q i ell h
  have zero (q i ell h : ℕ)
      (outside : (K : ℤ)+d-m-3 < (i : ℤ)+(j : ℤ)+(ell : ℤ)+(h : ℤ)) :
      f q i ell h = 0 := by
    dsimp only [f]
    apply finsum_eq_zero_of_forall_eq_zero
    intro z
    rw [mixedSourceFirst_zero D hu h24 H K d m n r E a.val b.val b.property.1 hE
      u.val v.val huH i q (ell+z) (j+ell+h) (by push_cast; omega), mul_zero]
  have tail (q i ell h : ℕ) (outside : N ≤ i+ell+h) : f q i ell h = 0 := by
    apply zero
    omega
  have signed := mixed_second_input_signed_support D hu h24 H K d
    (n+r-(j : ℤ)) (m+(j : ℤ)) E a u v huH hvK b
  dsimp only at signed
  rcases signed with ⟨negative, result⟩ | ⟨W, hW, result⟩
  · rw [result]
    symm
    apply Finset.sum_eq_zero
    intro q hq
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro ell hell
    apply Finset.sum_eq_zero
    intro h hh
    apply zero
    omega
  · rw [result]
    rw [Finset.sum_comm]
    have bound : W-1 ≤ N := by omega
    apply Finset.sum_congr rfl
    intro q hq
    calc
      _ = ∑ p ∈ Finset.range (W-1), ∑ i ∈ Finset.range (p+1),
          ∑ ell ∈ Finset.range (p-i+1), f q i ell (p-i-ell) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ell hell
        rw [mul_finsum, mul_finsum]
        apply finsum_congr
        intro z
        have hip : i ≤ p := by have := Finset.mem_range.mp hi; omega
        have hellp : ell ≤ p-i := by have := Finset.mem_range.mp hell; omega
        have split : p = i+ell+(p-i-ell) := by omega
        have phase :
            ((H : ℤ)+(n+r-(j : ℤ)+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)))+
              (d-(ell : ℤ)) =
            n+r-(j : ℤ)+1-(i : ℤ)-(H : ℤ)+(q : ℤ)+d-
              2*(ell : ℤ)-((p-i-ell : ℕ) : ℤ) := by omega
        have outerExponent :
            2*(m+(j : ℤ))+2-4*d+2*((p-i : ℕ) : ℤ)+2*((z+ell : ℕ) : ℤ) =
            -2*(r+(2*d-((ell+z : ℕ) : ℤ)-m-r-2)-
              ((j+ell+(p-i-ell) : ℕ) : ℤ))-2 := by omega
        have innerExponent :
            2*(n+r-(j : ℤ)+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)) =
            -2*((2*(H : ℤ)-n-r-2+(i : ℤ)-(q : ℤ))+
              ((j+ell+(p-i-ell) : ℕ) : ℤ))-2 := by omega
        have parameter : 2*(d : ℂ)-((m+(j : ℤ) : ℤ) : ℂ)-(ell : ℂ)-2 =
            2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ) := by push_cast; ring
        dsimp only [f, mixedSourceFirst]
        rw [outerExponent, innerExponent, parameter, Nat.add_comm z ell]
        have phases :
            ((-1 : ℂ)^((H : ℤ)+(n+r-(j : ℤ)+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)))) *
              ((-1 : ℂ)^(d-(ell : ℤ))) =
            (-1 : ℂ)^(n+r-(j : ℤ)+1-(i : ℤ)-(H : ℤ)+(q : ℤ)+d-
              2*(ell : ℤ)-((p-i-ell : ℕ) : ℤ)) := by
          rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), phase]
        simp only [div_eq_mul_inv, mul_inv_rev]
        linear_combination
          ((i.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹ *
            (ell.factorial : ℂ)⁻¹ * (z.factorial : ℂ)⁻¹ *
            Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) (p-i-ell) *
            actualForm D hu ((T D hu ^ i) v.val)
              ((correctedField D hu ((originalL1 D ^ (ell+z)) a.val)).coeff
                (-2*(r+(2*d-((ell+z : ℕ) : ℤ)-m-r-2)-
                  ((j+ell+(p-i-ell) : ℕ) : ℤ))-2)
                ((correctedField D hu b.val).coeff
                  (-2*((2*(H : ℤ)-n-r-2+(i : ℤ)-(q : ℤ))+
                    ((j+ell+(p-i-ell) : ℕ) : ℤ))-2) ((T D hu ^ q) u.val)))) * phases
      _ = ∑ p ∈ Finset.range N, ∑ i ∈ Finset.range (p+1),
          ∑ ell ∈ Finset.range (p-i+1), f q i ell (p-i-ell) := by
        apply Finset.sum_subset (Finset.range_mono bound)
        intro p hp outside
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro ell hell
        apply zero
        have hip : i ≤ p := by have := Finset.mem_range.mp hi; omega
        have hellp : ell ≤ p-i := by have := Finset.mem_range.mp hell; omega
        have := Finset.mem_range.not.mp outside
        omega
      _ = _ := lowering_triangle_to_cube N (f q) (tail q)

/-- The two actual source-lowering factorials are gathered at L=ell+z.
Actual original-source nilpotence supplies the rectangle tail, independently
of the signed binomial parameters. The factor choose(L,ell)/L! is retained
on the actual first ordered source product. -/
theorem mixed_second_source_factorial_contraction (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (d m n r : ℤ) (a b : Carrier D) (u v : ActualTensor D hu)
    (i q j h N : ℕ)
    (hN : a.support.sup
      (fun c => MvPolynomial.weightedTotalDegree
        (LatticeHalfFockFiniteCorrection.sourceWeight D) (a c))+1 ≤ N) :
    (∑ ell ∈ Finset.range N, ∑ z ∈ Finset.range N,
      ((ell.factorial : ℂ)⁻¹ * (z.factorial : ℂ)⁻¹) *
      (Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
        actualForm D hu ((T D hu ^ i) v)
          ((correctedField D hu ((originalL1 D ^ (ell+z)) a)).coeff
            (-2*(r+(2*d-((ell+z : ℕ) : ℤ)-m-r-2)-((j+ell+h : ℕ) : ℤ))-2)
            ((correctedField D hu b).coeff
              (-2*((2*(H : ℤ)-n-r-2+(i : ℤ)-(q : ℤ))+
                ((j+ell+h : ℕ) : ℤ))-2) ((T D hu ^ q) u))))) =
    ∑ L ∈ Finset.range N, (L.factorial : ℂ)⁻¹ *
      (∑ ell ∈ Finset.range N, Ring.choose (L : ℂ) ell *
        Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
        actualForm D hu ((T D hu ^ i) v)
          ((correctedField D hu ((originalL1 D ^ L) a)).coeff
            (-2*(r+(2*d-(L : ℤ)-m-r-2)-((j+ell+h : ℕ) : ℤ))-2)
            ((correctedField D hu b).coeff
              (-2*((2*(H : ℤ)-n-r-2+(i : ℤ)-(q : ℤ))+
                ((j+ell+h : ℕ) : ℤ))-2) ((T D hu ^ q) u)))) := by
  classical
  let S := a.support.sup
    (fun c => MvPolynomial.weightedTotalDegree
      (LatticeHalfFockFiniteCorrection.sourceWeight D) (a c))+1
  have sourceZero (L : ℕ) (hL : N ≤ L) : (originalL1 D ^ L) a = 0 := by
    have killed : (originalL1 D ^ S) a = 0 :=
      SourceMobius.actual_sugawara_one_bound D hu a
    rw [show L = (L-S)+S by dsimp [S] at *; omega,
      pow_add, Module.End.mul_apply, killed, map_zero]
  have productZero (L k : ℕ) (hL : N ≤ L) :
      mixedSourceFirst D hu H d m n r a b u v i q L k = 0 := by
    simp only [mixedSourceFirst, sourceZero L hL, map_zero,
      Pi.zero_apply, LinearMap.zero_apply]
  let F (ell z : ℕ) : ℂ :=
    Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
      mixedSourceFirst D hu H d m n r a b u v i q (ell+z) (j+ell+h)
  have tail (ell z : ℕ) (outside : N ≤ ell ∨ N ≤ z) : F ell z = 0 := by
    dsimp only [F]
    rw [productZero (ell+z) (j+ell+h) (by omega), mul_zero]
  change (∑ ell ∈ Finset.range N, ∑ z ∈ Finset.range N,
    ((ell.factorial : ℂ)⁻¹ * (z.factorial : ℂ)⁻¹) * F ell z) = _
  rw [twice_signed_supported_factorial_contraction N F tail]
  calc
    _ = ∑ L ∈ Finset.range (2*N), ∑ ell ∈ Finset.range (L+1),
        (Ring.choose (L : ℂ) ell / (L.factorial : ℂ)) *
        (Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
          mixedSourceFirst D hu H d m n r a b u v i q L (j+ell+h)) := by
      apply Finset.sum_congr rfl
      intro L hL
      apply Finset.sum_congr rfl
      intro ell hell
      have bound : ell ≤ L := by have := Finset.mem_range.mp hell; omega
      dsimp only [F]
      rw [Nat.add_sub_of_le bound]
    _ = ∑ L ∈ Finset.range N, ∑ ell ∈ Finset.range (L+1),
        (Ring.choose (L : ℂ) ell / (L.factorial : ℂ)) *
        (Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
          mixedSourceFirst D hu H d m n r a b u v i q L (j+ell+h)) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega : N ≤ 2*N))
      intro L hL outside
      apply Finset.sum_eq_zero
      intro ell hell
      rw [productZero L (j+ell+h) (by simpa using outside), mul_zero, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro L hL
      change _ = (L.factorial : ℂ)⁻¹ *
        (∑ ell ∈ Finset.range N, Ring.choose (L : ℂ) ell *
          Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
          mixedSourceFirst D hu H d m n r a b u v i q L (j+ell+h))
      rw [Finset.mul_sum]
      trans ∑ ell ∈ Finset.range (L+1), (L.factorial : ℂ)⁻¹ *
        (Ring.choose (L : ℂ) ell *
          Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
          mixedSourceFirst D hu H d m n r a b u v i q L (j+ell+h))
      · apply Finset.sum_congr rfl
        intro ell hell
        ring
      · apply Finset.sum_subset (Finset.range_mono (by have := Finset.mem_range.mp hL; omega))
        intro ell hell outside
        have bound : L < ell := by have := Finset.mem_range.not.mp outside; omega
        rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt bound, Nat.cast_zero,
          zero_mul, zero_mul, mul_zero]

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
