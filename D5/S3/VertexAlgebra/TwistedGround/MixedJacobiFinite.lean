/- GID: D5/S3/VertexAlgebra/TwistedGround/MixedJacobiFinite
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/MixedJacobiFinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-source signed two-twisted-input mixed Jacobi in the actual restricted dual. -/
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
open scoped BigOperators VertexOperator
namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeAllStateField LatticePositiveEnergy LatticeInvolution
open ActualChargedAdjoint LatticeSugawaraCurrents LatticeSugawaraVirasoro
open HalfFock.LatticeHalfFockParityField
open private T originalL1 original_l1_grade original_l1_fixed lowering_eigen
  from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private signed_supported_transform
  from D5.S3.VertexAlgebra.TwistedGround.MixedJacobi

private theorem integer_energy_zero (D : LatticeData) (hu : IsUnit D.G.det)
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

private theorem lowering_integer_energy (D : LatticeData) (hu : IsUnit D.G.det)
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

private theorem original_mode_integer_energy (D : LatticeData) (hu : IsUnit D.G.det)
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

private def mixedSourceFirst (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (d m n r : ℤ) (a b : Carrier D) (u v : ActualTensor D hu)
    (p q L k : ℕ) : ℂ :=
  let Q : ℤ := 2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ)
  let R : ℤ := 2*d-(L : ℤ)-m-r-2
  actualForm D hu ((T D hu ^ p) v)
    ((correctedField D hu ((originalL1 D ^ L) a)).coeff (-2*(r+R-(k : ℤ))-2)
      ((correctedField D hu b).coeff (-2*(Q+(k : ℤ))-2) ((T D hu ^ q) u)))

private def mixedSourceSecond (D : LatticeData) (hu : IsUnit D.G.det)
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

private theorem mixed_first_contraction (D : LatticeData) (hu : IsUnit D.G.det)
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

private theorem mixed_second_contraction (D : LatticeData) (hu : IsUnit D.G.det)
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
  rw [Finset.sum_range_diag_flip]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_range_diag_flip]
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
    LatticeAllStateReconstruction.mu, Int.cast_zero, zero_div, add_zero,
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
    apply finsum_eq_zero
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

private def sourceLoweringCutoff (D : LatticeData) (a : Carrier D) : ℕ :=
  a.support.sup (fun c => MvPolynomial.weightedTotalDegree
    (LatticeHalfFockFiniteCorrection.sourceWeight D) (a c))+1

private theorem source_lowering_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (L : ℕ) (hL : sourceLoweringCutoff D a ≤ L) :
    (originalL1 D ^ L) a = 0 := by
  have killed : (originalL1 D ^ sourceLoweringCutoff D a) a = 0 :=
    SourceMobius.actual_sugawara_one_bound D hu a
  rw [show L = (L-sourceLoweringCutoff D a)+sourceLoweringCutoff D a by omega,
    pow_add, Module.End.mul_apply, killed, map_zero]

private theorem phase_even_shift (x t : ℤ) :
    (-1 : ℂ)^(x+2*t) = (-1 : ℂ)^x := by
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
  norm_num

private def mixedCommonWeight (H : ℕ) (d n : ℤ) (p q L : ℕ) : ℂ :=
  (-1 : ℂ)^(n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d) /
    ((p.factorial : ℂ)*(q.factorial : ℂ)*(L.factorial : ℂ))

private theorem first_input_common_phase (H : ℕ) (d m n r : ℤ) (p q L : ℕ) :
    ((-1 : ℂ)^(m+n+r+2-(p : ℤ)-(H : ℤ)-d+(q : ℤ)+(L : ℤ))) /
        ((p.factorial : ℂ)*(q.factorial : ℂ)*(L.factorial : ℂ)) =
      -(mixedCommonWeight H d n p q L *
        (-1 : ℂ)^(2*d-(L : ℤ)-m-r-2)) := by
  have phase : m+n+r+2-(p : ℤ)-(H : ℤ)-d+(q : ℤ)+(L : ℤ) =
      (n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d +
        (2*d-(L : ℤ)-m-r-2)+1)+2*(m+r+1-2*d+(L : ℤ)) := by ring
  rw [phase, phase_even_shift, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  simp only [mixedCommonWeight, zpow_one]
  ring

private theorem second_input_common_phase (H : ℕ) (d n r : ℤ)
    (p q j ell h : ℕ) :
    (-1 : ℂ)^r * (-1 : ℂ)^j *
      (-1 : ℂ)^(n+r-(j : ℤ)+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d-
        2*(ell : ℤ)-(h : ℤ)) =
      (-1 : ℂ)^(n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d) * (-1 : ℂ)^h := by
  rw [← zpow_natCast, ← zpow_natCast,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  convert phase_even_shift
    (n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d+(h : ℤ))
    (r-(ell : ℤ)-(h : ℤ)) using 1 <;> congr 1 <;> ring

private theorem cube_sum_rotate (N : ℕ) (f : ℕ → ℕ → ℕ → ℂ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, f i j k) =
      ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, f i j k := by
  calc
    _ = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ∑ j ∈ Finset.range N, f i j k := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem mixed_second_input_branch_contracted (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (N : ℕ) (hN : ((K : ℤ)+d-m-2).toNat ≤ N)
    (hS : sourceLoweringCutoff D a.val ≤ N) :
    (-1 : ℂ)^r * (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
      normalizedCoefficient D hu (n+r-(j : ℤ)) u
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b) =
    ∑ q ∈ Finset.range (H-1), ∑ p ∈ Finset.range N, ∑ L ∈ Finset.range N,
      mixedCommonWeight H d n p q L *
        (∑ k ∈ Finset.range N,
          ((-1 : ℂ)^k * Ring.choose ((2*d-(L : ℤ)-m-r-2 : ℤ) : ℂ) k) *
            mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q L k) := by
  classical
  have finite : (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
      normalizedCoefficient D hu (n+r-(j : ℤ)) u
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b) =
      ∑ j ∈ Finset.range N, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
        normalizedCoefficient D hu (n+r-(j : ℤ)) u
          (((fixedParitySlice D hu (-1)
            (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have energy := original_mode_integer_energy D hu d (K : ℤ) (m+(j : ℤ))
      a.val a.property.1 v.val hvK
    have zero := integer_energy_zero D hu h24 ((K : ℤ)+d-(m+(j : ℤ))-1)
      _ energy (by have := Finset.mem_range.not.mp outside; omega)
    have input : ((fixedParitySlice D hu (-1)
        (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v = 0 := by
      apply Subtype.ext
      change (correctedField D hu a.val).coeff (2*(-(m+(j : ℤ))-1)) v.val = 0
      rw [show 2*(-(m+(j : ℤ))-1) = -2*(m+(j : ℤ))-2 by ring]
      exact zero
    apply hj
    simp only [input, map_zero, DirectSum.zero_apply, LinearMap.zero_apply, mul_zero]
  rw [finite]
  simp_rw [mixed_second_input_reindexed_pairing D hu h24 H K d m n r E a b hE
    u v huH hvK (N := N) (hN := hN)]
  let c (p q : ℕ) : ℂ :=
    (-1 : ℂ)^(n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d) /
      ((p.factorial : ℂ)*(q.factorial : ℂ))
  let F (p q j h ell z : ℕ) : ℂ :=
    ((ell.factorial : ℂ)⁻¹*(z.factorial : ℂ)⁻¹) *
      (Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
        mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q
          (ell+z) (j+ell+h))
  have sourceSum (p q j ell h : ℕ) :
      (∑ᶠ z : ℕ,
        (((-1 : ℂ)^(n+r-(j : ℤ)+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d-
            2*(ell : ℤ)-(h : ℤ)))/
          ((p.factorial : ℂ)*(q.factorial : ℂ)*(ell.factorial : ℂ)*(z.factorial : ℂ))) *
        Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
        mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q
          (ell+z) (j+ell+h)) =
      ∑ z ∈ Finset.range N,
        (((-1 : ℂ)^(n+r-(j : ℤ)+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d-
            2*(ell : ℤ)-(h : ℤ)))/
          ((p.factorial : ℂ)*(q.factorial : ℂ)*(ell.factorial : ℂ)*(z.factorial : ℂ))) *
        Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
        mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q
          (ell+z) (j+ell+h) := by
    apply finsum_eq_sum_of_support_subset
    intro z hz
    by_contra outside
    have killed := source_lowering_zero D hu a.val (ell+z)
      (by have := Finset.mem_range.not.mp outside; omega)
    apply hz
    simp only [mixedSourceFirst, killed, map_zero, Pi.zero_apply,
      LinearMap.zero_apply, mul_zero]
  change (-1 : ℂ)^r * (∑ j ∈ Finset.range N,
    ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
    (∑ q ∈ Finset.range (H-1), ∑ p ∈ Finset.range N,
      ∑ ell ∈ Finset.range N, ∑ h ∈ Finset.range N, _)) = _
  simp_rw [sourceSum]
  calc
    _ = ∑ q ∈ Finset.range (H-1), ∑ p ∈ Finset.range N,
        c p q * (∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
          (Ring.choose (r : ℂ) j * (-1 : ℂ)^h) *
            (∑ ell ∈ Finset.range N, ∑ z ∈ Finset.range N, F p q j h ell z)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro ell hell
      apply Finset.sum_congr rfl
      intro z hz
      have phase := second_input_common_phase H d n r p q j ell h
      dsimp only [c, F]
      simp only [div_eq_mul_inv, mul_inv_rev]
      linear_combination
        ((p.factorial : ℂ)⁻¹*(q.factorial : ℂ)⁻¹*
          (ell.factorial : ℂ)⁻¹*(z.factorial : ℂ)⁻¹*
          Ring.choose (r : ℂ) j *
          Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
          mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q
            (ell+z) (j+ell+h)) * phase
    _ = ∑ q ∈ Finset.range (H-1), ∑ p ∈ Finset.range N,
        c p q * (∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
          (Ring.choose (r : ℂ) j * (-1 : ℂ)^h) *
            (∑ L ∈ Finset.range N, (L.factorial : ℂ)⁻¹ *
              (∑ ell ∈ Finset.range N, Ring.choose (L : ℂ) ell *
                Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
                mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q L
                  (j+ell+h)))) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro h hh
      congr 1
      exact mixed_second_source_factorial_contraction D hu H d m n r a.val b.val
        u.val v.val p q j h N hS
    _ = ∑ q ∈ Finset.range (H-1), ∑ p ∈ Finset.range N, ∑ L ∈ Finset.range N,
        mixedCommonWeight H d n p q L *
          (∑ ell ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
            Ring.choose (L : ℂ) ell * Ring.choose (r : ℂ) j * (-1 : ℂ)^h *
            Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
            mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q L
              (j+ell+h)) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      simp_rw [Finset.mul_sum]
      rw [cube_sum_rotate]
      apply Finset.sum_congr rfl
      intro L hL
      rw [cube_sum_rotate]
      apply Finset.sum_congr rfl
      intro ell hell
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro h hh
      dsimp only [mixedCommonWeight, c]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro L hL
      rw [mixed_second_contraction D hu h24 H K d m n r E a.val b.val
        b.property.1 hE u.val v.val huH p q L N hN]

private theorem lowering_integer_zero_after (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H : ℕ) (u : ActualTensor D hu)
    (huH : actualTensorL0 D hu u = (H : ℂ) • u) (q : ℕ) (hq : H-1 ≤ q) :
    (T D hu ^ q) u = 0 := by
  exact integer_energy_zero D hu h24 ((H : ℤ)-(q : ℤ)) _
    (lowering_integer_energy D hu h24 (H : ℤ) u huH q) (by omega)

private def mixedFirstSum (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (d m n r : ℤ) (a b : Carrier D) (u v : ActualTensor D hu)
    (N p q L : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N,
    ((-1 : ℂ)^k * Ring.choose ((2*d-(L : ℤ)-m-r-2 : ℤ) : ℂ) k) *
      mixedSourceFirst D hu H d m n r a b u v p q L k

private def mixedSecondSum (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (d m n r : ℤ) (a b : Carrier D) (u v : ActualTensor D hu)
    (N p q L : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N,
    ((-1 : ℂ)^k * Ring.choose ((2*d-(L : ℤ)-m-r-2 : ℤ) : ℂ) k) *
      mixedSourceSecond D hu H d m n r a b u v p q L k

private def mixedIterate (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (d m n r : ℤ) (a b : Carrier D) (u v : ActualTensor D hu)
    (p q L : ℕ) : ℂ :=
  ∑ᶠ j : ℕ, Ring.choose (r : ℂ) j *
    actualForm D hu ((T D hu ^ p) v)
      ((correctedField D hu
        (((Y D ((originalL1 D ^ L) a))[[2*d-(L : ℤ)-m-r-2+(j : ℤ)]]) b)).coeff
        (-2*(r+(2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ))-(j : ℤ))-2)
        ((T D hu ^ q) u))

private theorem mixed_first_input_common_cube (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (N : ℕ) (hN : ((H : ℤ)+d-r-2).toNat ≤ N) (hK : K-1 ≤ N) :
    (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j *
      (normalizedCoefficient D hu (m+n-(j : ℤ))
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u) v) E b) =
    ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ L ∈ Finset.range N,
      mixedCommonWeight H d n p q L *
        (-(-1 : ℂ)^(2*d-(L : ℤ)-m-r-2)) *
        mixedSecondSum D hu H d m n r a.val b.val u.val v.val N p q L := by
  classical
  rw [mixed_first_input_branch_reindexed D hu h24 H K d m n r E a b u v huH hvK N hN]
  calc
    _ = ∑ p ∈ Finset.range (K-1), ∑ q ∈ Finset.range N, ∑ L ∈ Finset.range N,
        mixedCommonWeight H d n p q L *
          (-(-1 : ℂ)^(2*d-(L : ℤ)-m-r-2)) *
          mixedSecondSum D hu H d m n r a.val b.val u.val v.val N p q L := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro L hL
      rw [first_input_common_phase]
      ring
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono hK)
      intro p hp outside
      have zero := lowering_integer_zero_after D hu h24 K v.val hvK p
        (by simpa using outside)
      apply Finset.sum_eq_zero
      intro q hq
      apply Finset.sum_eq_zero
      intro L hL
      simp only [mixedSecondSum, mixedSourceSecond, zero, map_zero,
        LinearMap.zero_apply, mul_zero, Finset.sum_const_zero]

private theorem mixed_second_input_common_cube (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (N : ℕ) (hN : ((K : ℤ)+d-m-2).toNat ≤ N)
    (hS : sourceLoweringCutoff D a.val ≤ N) (hH : H-1 ≤ N) :
    (-1 : ℂ)^r * (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
      normalizedCoefficient D hu (n+r-(j : ℤ)) u
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b) =
    ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ L ∈ Finset.range N,
      mixedCommonWeight H d n p q L *
        mixedFirstSum D hu H d m n r a.val b.val u.val v.val N p q L := by
  classical
  rw [mixed_second_input_branch_contracted D hu h24 H K d m n r E a b hE
    u v huH hvK N hN hS]
  change (∑ q ∈ Finset.range (H-1), ∑ p ∈ Finset.range N, ∑ L ∈ Finset.range N,
    mixedCommonWeight H d n p q L *
      mixedFirstSum D hu H d m n r a.val b.val u.val v.val N p q L) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_subset (Finset.range_mono hH)
  intro q hq outside
  have zero := lowering_integer_zero_after D hu h24 H u.val huH q
    (by simpa using outside)
  apply Finset.sum_eq_zero
  intro L hL
  simp only [mixedFirstSum, mixedSourceFirst, zero, map_zero,
    mul_zero, Finset.sum_const_zero]

private theorem mixed_iterate_cancellation (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (u v : ActualTensor D hu) (huH : actualTensorL0 D hu u = (H : ℂ) • u)
    (p q L N : ℕ)
    (hNfirst : ((H : ℤ)+d-r-2).toNat ≤ N)
    (hNsecond : ((K : ℤ)+d-m-2).toNat ≤ N) :
    mixedIterate D hu H d m n r a.val b.val u v p q L =
      mixedFirstSum D hu H d m n r a.val b.val u v N p q L -
        (-1 : ℂ)^(2*d-(L : ℤ)-m-r-2) *
          mixedSecondSum D hu H d m n r a.val b.val u v N p q L := by
  have law := mixed_source_finite_cancellation D hu h24 H K d m n r E
    a b hE u v huH p q L N hNfirst hNsecond
  dsimp only at law
  rw [mixed_second_contraction D hu h24 H K d m n r E a.val b.val b.property.1
    hE u v huH p q L N hNsecond,
    mixed_first_contraction D hu h24 H d m n r a.val b.val a.property.1
      u v huH p q L N hNfirst] at law
  exact law

private theorem original_negative_grade_zero (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (e : ℤ) (x : Carrier D) (hx : x ∈ grade D e) (he : e < 0) : x = 0 := by
  apply (carrierCoeffEquiv D).injective
  ext i
  have nonneg : 0 ≤ energy D i := by
    have hc := chargeEnergy_nonneg D hD i.1
    change 0 ≤ chargeEnergy D i.1 + (oscillatorEnergy i.2 : ℤ)
    omega
  exact (mem_grade_iff D e x).mp hx i (by omega)

private theorem mixed_iterate_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (H K : ℕ) (d m n r E : ℤ) (a : fixedGrade D d) (b : fixedGrade D E)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (u v : ActualTensor D hu) (p q L : ℕ) :
    mixedIterate D hu H d m n r a.val b.val u v p q L =
      ∑ j ∈ Finset.range (((H : ℤ)+(K : ℤ)-n).toNat+1),
        Ring.choose (r : ℂ) j * actualForm D hu ((T D hu ^ p) v)
          ((correctedField D hu
            (((Y D ((originalL1 D ^ L) a.val))[[2*d-(L : ℤ)-m-r-2+(j : ℤ)]])
              b.val)).coeff
            (-2*(r+(2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ))-(j : ℤ))-2)
            ((T D hu ^ q) u)) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra outside
  have grade := positive_actual_mode_grade D hD (d-(L : ℤ)) E
    (2*d-(L : ℤ)-m-r-2+(j : ℤ)) ((originalL1 D ^ L) a.val) b.val
    (original_l1_grade D hu d a.val a.property.1 L) b.property.1
  have zero := original_negative_grade_zero D hD _ _ grade
    (by have := Finset.mem_range.not.mp outside; omega)
  apply hj
  simp only [zero, map_zero, Pi.zero_apply, LinearMap.zero_apply, mul_zero]

private theorem four_sum_reorder (I J K L : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℂ) :
    (∑ i ∈ I, ∑ j ∈ J, ∑ k ∈ K, ∑ l ∈ L, f i j k l) =
      ∑ k ∈ K, ∑ l ∈ L, ∑ j ∈ J, ∑ i ∈ I, f i j k l := by
  calc
    _ = ∑ i ∈ I, ∑ k ∈ K, ∑ j ∈ J, ∑ l ∈ L, f i j k l := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k ∈ K, ∑ i ∈ I, ∑ j ∈ J, ∑ l ∈ L, f i j k l := Finset.sum_comm
    _ = ∑ k ∈ K, ∑ i ∈ I, ∑ l ∈ L, ∑ j ∈ J, f i j k l := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k ∈ K, ∑ l ∈ L, ∑ i ∈ I, ∑ j ∈ J, f i j k l := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      exact Finset.sum_comm

private theorem mixed_first_dual_common_cube (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (d m n r E : ℤ) (a : fixedGrade D d) (b : fixedGrade D E)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (N : ℕ) (hK : K-1 ≤ N) (hH : H-1 ≤ N)
    (hS : sourceLoweringCutoff D a.val ≤ N) :
    (∑ᶠ j : ℕ, (((-1 : ℂ)^j)*Ring.choose (r : ℂ) j) •
      oppositeAction D hu hD (m+r-(j : ℤ))
        (⟨a.val,a.property.2⟩ : FixedCarrier D)
        (normalizedCoefficient D hu (n+(j : ℤ)) u v)) E b =
    ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ L ∈ Finset.range N,
      mixedCommonWeight H d n p q L *
        mixedIterate D hu H d m n r a.val b.val u.val v.val p q L := by
  classical
  rw [mixed_first_branch_pairing D hu hD h24 H K d m n r E a u v huH hvK hE b]
  let S := sourceLoweringCutoff D a.val
  let J := ((H : ℤ)+(K : ℤ)-n).toNat+1
  let f (p q L : ℕ) : ℂ := mixedCommonWeight H d n p q L *
    mixedIterate D hu H d m n r a.val b.val u.val v.val p q L
  have pZero (p q L : ℕ) (hp : K-1 ≤ p) : f p q L = 0 := by
    have zero := lowering_integer_zero_after D hu h24 K v.val hvK p hp
    simp only [f, mixedIterate, zero, map_zero, LinearMap.zero_apply, mul_zero,
      finsum_zero]
  have qZero (p q L : ℕ) (hq : H-1 ≤ q) : f p q L = 0 := by
    have zero := lowering_integer_zero_after D hu h24 H u.val huH q hq
    simp only [f, mixedIterate, zero, map_zero, mul_zero, finsum_zero]
  have LZero (p q L : ℕ) (hL : S ≤ L) : f p q L = 0 := by
    have zero := source_lowering_zero D hu a.val L hL
    simp only [f, mixedIterate, zero, map_zero, Pi.zero_apply, LinearMap.zero_apply,
      mul_zero, finsum_zero]
  calc
    _ = ∑ p ∈ Finset.range (K-1), ∑ q ∈ Finset.range (H-1),
        ∑ L ∈ Finset.range S, f p q L := by
      simp_rw [Finset.mul_sum]
      rw [four_sum_reorder]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro L hL
      dsimp only [f]
      rw [mixed_iterate_finite D hu hD H K d m n r E a b hE u.val v.val p q L,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have mode : 2*d-(L : ℤ)-m-r+(j : ℤ)-2 =
          2*d-(L : ℤ)-m-r-2+(j : ℤ) := by ring
      have exponent : 2*(n+(j : ℤ)+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)) =
          -2*(r+(2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ))-(j : ℤ))-2 := by ring
      have phase : (-1 : ℂ)^j * (-1 : ℂ)^d *
          (-1 : ℂ)^((H : ℤ)+(n+(j : ℤ)+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ))) =
          (-1 : ℂ)^(n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d) := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
          ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
        convert phase_even_shift (n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d) (j : ℤ)
          using 1 <;> congr 1 <;> ring
      rw [mode, exponent]
      dsimp only [mixedCommonWeight]
      simp only [div_eq_mul_inv, mul_inv_rev]
      linear_combination
        ((p.factorial : ℂ)⁻¹*(q.factorial : ℂ)⁻¹*(L.factorial : ℂ)⁻¹*
          Ring.choose (r : ℂ) j * actualForm D hu ((T D hu ^ p) v.val)
            ((correctedField D hu
              (((Y D ((originalL1 D ^ L) a.val))[[2*d-(L : ℤ)-m-r-2+(j : ℤ)]])
                b.val)).coeff
              (-2*(r+(2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ))-(j : ℤ))-2)
              ((T D hu ^ q) u.val))) * phase
    _ = ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range (H-1),
        ∑ L ∈ Finset.range S, f p q L := by
      apply Finset.sum_subset (Finset.range_mono hK)
      intro p hp outside
      apply Finset.sum_eq_zero
      intro q hq
      apply Finset.sum_eq_zero
      intro L hL
      exact pZero p q L (by simpa using outside)
    _ = ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N,
        ∑ L ∈ Finset.range S, f p q L := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_subset (Finset.range_mono hH)
      intro q hq outside
      apply Finset.sum_eq_zero
      intro L hL
      exact qZero p q L (by simpa using outside)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_subset (Finset.range_mono hS)
      intro L hL outside
      exact LZero p q L (by simpa using outside)

private theorem mixed_homogeneous_grade_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (d m n r E : ℤ) (a : fixedGrade D d) (b : fixedGrade D E)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2) :
    (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j *
      normalizedCoefficient D hu (m+n-(j : ℤ))
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u) v E b) =
    (∑ᶠ j : ℕ, (((-1 : ℂ)^j)*Ring.choose (r : ℂ) j) •
      oppositeAction D hu hD (m+r-(j : ℤ))
        (⟨a.val,a.property.2⟩ : FixedCarrier D)
        (normalizedCoefficient D hu (n+(j : ℤ)) u v)) E b -
    (-1 : ℂ)^r * (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
      normalizedCoefficient D hu (n+r-(j : ℤ)) u
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b) := by
  classical
  let N := (H-1)+(K-1)+sourceLoweringCutoff D a.val+
    ((H : ℤ)+d-r-2).toNat+((K : ℤ)+d-m-2).toNat
  have hNfirst : ((H : ℤ)+d-r-2).toNat ≤ N := by dsimp [N]; omega
  have hNsecond : ((K : ℤ)+d-m-2).toNat ≤ N := by dsimp [N]; omega
  have hH : H-1 ≤ N := by dsimp [N]; omega
  have hK : K-1 ≤ N := by dsimp [N]; omega
  have hS : sourceLoweringCutoff D a.val ≤ N := by dsimp [N]; omega
  rw [mixed_first_input_common_cube D hu h24 H K d m n r E a b u v huH hvK N hNfirst hK,
    mixed_first_dual_common_cube D hu hD h24 H K d m n r E a b u v huH hvK hE
      N hK hH hS,
    mixed_second_input_common_cube D hu h24 H K d m n r E a b hE u v huH hvK
      N hNsecond hS hH]
  simp_rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro L hL
  rw [mixed_iterate_cancellation D hu h24 H K d m n r E a b hE u.val v.val huH
    p q L N hNfirst hNsecond]
  ring

private def mixedMode (D : LatticeData) (hu : IsUnit D.G.det) (t : ℤ) :
    FixedCarrier D →ₗ[ℂ] Module.End ℂ (paritySpace D hu (-1)) where
  toFun a := (fixedParitySlice D hu (-1) a)[[t]]
  map_add' a b := by
    ext x
    apply Subtype.ext
    change (correctedField D hu (a.val+b.val)).coeff (2*(-t-1)) x.val = _
    simp only [map_add, LinearMap.add_apply]
    rfl
  map_smul' z a := by
    ext x
    apply Subtype.ext
    change (correctedField D hu (z • a.val)).coeff (2*(-t-1)) x.val = _
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]
    rfl

private def mixedLeftTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) (j : ℕ) :
    FixedRestrictedDual D :=
  Ring.choose (m : ℂ) j • normalizedCoefficient D hu (m+n-(j : ℤ))
    (mixedMode D hu (r+(j : ℤ)) a u) v

private def mixedFirstTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) (j : ℕ) :
    FixedRestrictedDual D :=
  ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
    oppositeAction D hu hD (m+r-(j : ℤ)) a
      (normalizedCoefficient D hu (n+(j : ℤ)) u v)

private def mixedSecondTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) (j : ℕ) :
    FixedRestrictedDual D :=
  (((-1 : ℂ)^j * Ring.choose (r : ℂ) j) * (-1 : ℂ)^r) •
    normalizedCoefficient D hu (n+r-(j : ℤ)) u (mixedMode D hu (m+(j : ℤ)) a v)

private theorem mixed_mode_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (t : ℤ) (a : FixedCarrier D) (u : paritySpace D hu (-1)) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → mixedMode D hu (t+(j : ℤ)) a u = 0 := by
  let A := fixedParitySlice D hu (-1) a
  let b : ℤ := ((HahnModule.of ℂ).symm (A u)).order
  refine ⟨(-t-1-b).toNat+1, ?_⟩
  intro j hj
  exact VertexOperator.ncoeff_eq_zero_of_lt_order A (t+(j : ℤ)) u
    (by dsimp [b] at *; omega)

private theorem mixed_families_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) :
    Function.HasFiniteSupport (mixedLeftTerm D hu m n r a u v) ∧
    Function.HasFiniteSupport (mixedFirstTerm D hu hD m n r a u v) ∧
    Function.HasFiniteSupport (mixedSecondTerm D hu m n r a u v) := by
  classical
  obtain ⟨L, hL⟩ := mixed_mode_tail D hu r a u
  obtain ⟨R, hR⟩ := mixed_mode_tail D hu m a v
  let J := ((ActualEnergyRestrictedDual.maxOddWeight D hu u.val : ℤ)+
    (ActualEnergyRestrictedDual.maxOddWeight D hu v.val : ℤ)+4-n).toNat
  refine ⟨(Finset.range L).finite_toSet.subset ?_,
    (Finset.range J).finite_toSet.subset ?_, (Finset.range R).finite_toSet.subset ?_⟩
  · intro j hj
    by_contra outside
    apply hj
    simp only [mixedLeftTerm, hL j (by simpa using outside), map_zero,
      LinearMap.zero_apply, smul_zero]
  · intro j hj
    by_contra outside
    have zero := normalizedCoefficient_truncation D hu hD u v (n+(j : ℤ))
      (by have := Finset.mem_range.not.mp outside; dsimp [J] at *; omega)
    apply hj
    simp only [mixedFirstTerm, zero, map_zero, smul_zero]
  · intro j hj
    by_contra outside
    apply hj
    simp only [mixedSecondTerm, hR j (by simpa using outside), map_zero, smul_zero]

private def mixedTriples (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (m n r : ℤ) :
    FixedCarrier D →ₗ[ℂ] paritySpace D hu (-1) →ₗ[ℂ]
      paritySpace D hu (-1) →ₗ[ℂ]
        (ℕ → FixedRestrictedDual D × FixedRestrictedDual D × FixedRestrictedDual D) where
  toFun a := {
    toFun u := {
      toFun v := fun j => (mixedLeftTerm D hu m n r a u v j,
        mixedFirstTerm D hu hD m n r a u v j, mixedSecondTerm D hu m n r a u v j)
      map_add' v w := by
        funext j
        simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, map_add,
          LinearMap.add_apply, smul_add, Prod.mk_add_mk]
      map_smul' z v := by
        funext j
        simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, map_smul,
          LinearMap.smul_apply, RingHom.id_apply, smul_smul, Prod.smul_mk]
        module }
    map_add' u w := by
      ext v j
      simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, map_add,
        LinearMap.add_apply, smul_add, Prod.mk_add_mk]
    map_smul' z u := by
      ext v j
      simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, map_smul,
        LinearMap.smul_apply, RingHom.id_apply, smul_smul, Prod.smul_mk]
      all_goals module }
  map_add' a b := by
    ext u v j
    simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, map_add,
      LinearMap.add_apply, smul_add, Prod.mk_add_mk]
  map_smul' z a := by
    ext u v j
    simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, map_smul,
      LinearMap.smul_apply, RingHom.id_apply, smul_smul, Prod.smul_mk]
    all_goals module

private theorem mixed_triples_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) :
    Function.HasFiniteSupport (mixedTriples D hu hD m n r a u v) := by
  obtain ⟨hl, hf, hs⟩ := mixed_families_finite D hu hD m n r a u v
  exact hl.prodMk (hf.prodMk hs)

private def mixedBalance (D : LatticeData) :
    (FixedRestrictedDual D × FixedRestrictedDual D × FixedRestrictedDual D) →ₗ[ℂ]
      FixedRestrictedDual D where
  toFun x := x.1-x.2.1+x.2.2
  map_add' x y := by dsimp; abel
  map_smul' z x := by simp only [Prod.smul_fst, Prod.smul_snd, smul_sub, smul_add]

private def mixedResidual (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (m n r : ℤ) :
    FixedCarrier D →ₗ[ℂ] paritySpace D hu (-1) →ₗ[ℂ]
      paritySpace D hu (-1) →ₗ[ℂ] FixedRestrictedDual D where
  toFun a := {
    toFun u := {
      toFun v := mixedBalance D (∑ᶠ j, mixedTriples D hu hD m n r a u v j)
      map_add' v w := by
        simp only [map_add, LinearMap.add_apply, Pi.add_apply]
        rw [finsum_add_distrib (mixed_triples_finite D hu hD m n r a u v)
          (mixed_triples_finite D hu hD m n r a u w), map_add]
      map_smul' z v := by
        simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]
        rw [← smul_finsum, map_smul] }
    map_add' u w := by
      ext v
      simp only [map_add, LinearMap.add_apply, Pi.add_apply]
      rw [finsum_add_distrib (mixed_triples_finite D hu hD m n r a u v)
        (mixed_triples_finite D hu hD m n r a w v), map_add]
    map_smul' z u := by
      ext v
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]
      rw [← smul_finsum, map_smul] }
  map_add' a b := by
    ext u v
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    rw [finsum_add_distrib (mixed_triples_finite D hu hD m n r a u v)
      (mixed_triples_finite D hu hD m n r b u v), map_add]
  map_smul' z a := by
    ext u v
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]
    rw [← smul_finsum, map_smul]

private theorem mixed_residual_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) :
    mixedResidual D hu hD m n r a u v =
      (∑ᶠ j, mixedLeftTerm D hu m n r a u v j) -
      (∑ᶠ j, mixedFirstTerm D hu hD m n r a u v j) +
      (∑ᶠ j, mixedSecondTerm D hu m n r a u v j) := by
  let F := mixedTriples D hu hD m n r a u v
  have finite := mixed_triples_finite D hu hD m n r a u v
  have fst := (LinearMap.fst ℂ (FixedRestrictedDual D)
    (FixedRestrictedDual D × FixedRestrictedDual D)).map_finsum finite
  have snd := (LinearMap.snd ℂ (FixedRestrictedDual D)
    (FixedRestrictedDual D × FixedRestrictedDual D)).map_finsum finite
  have finiteSnd : Function.HasFiniteSupport (fun j => (F j).2) := finite.snd
  have sf := (LinearMap.fst ℂ (FixedRestrictedDual D) (FixedRestrictedDual D)).map_finsum finiteSnd
  have ss := (LinearMap.snd ℂ (FixedRestrictedDual D) (FixedRestrictedDual D)).map_finsum finiteSnd
  change (∑ᶠ j, F j).1-(∑ᶠ j, F j).2.1+(∑ᶠ j, F j).2.2 = _
  change (∑ᶠ j, F j).1 = ∑ᶠ j, (F j).1 at fst
  change (∑ᶠ j, F j).2 = ∑ᶠ j, (F j).2 at snd
  change (∑ᶠ j, (F j).2).1 = ∑ᶠ j, (F j).2.1 at sf
  change (∑ᶠ j, (F j).2).2 = ∑ᶠ j, (F j).2.2 at ss
  rw [fst, snd, sf, ss]
  rfl

private def restrictedEvaluation (D : LatticeData) (E : ℤ) (b : fixedGrade D E) :
    FixedRestrictedDual D →ₗ[ℂ] ℂ where
  toFun f := f E b
  map_add' f g := rfl
  map_smul' z f := rfl

open private homogeneous_coefficient ambientCoefficient liftGrade kernel
  from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private fixed_mode_energy_int from D5.S3.VertexAlgebra.TwistedGround.MixedJacobi

private theorem normalized_off_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (t E : ℤ)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (b : fixedGrade D E) (outside : E ≠ (H : ℤ)+(K : ℤ)-t-1) :
    normalizedCoefficient D hu t u v E b = 0 := by
  change ambientCoefficient D hu t u.val v.val E b = 0
  rw [homogeneous_coefficient D hu h24 H K t u.val v.val huH hvK]
  simp [liftGrade, DirectSum.lof_eq_of, DirectSum.of_apply, outside, Ne.symm outside]

private theorem mixed_input_off_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (b : fixedGrade D E) (outside : E ≠ (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (j : ℕ) :
    normalizedCoefficient D hu (m+n-(j : ℤ))
      (mixedMode D hu (r+(j : ℤ)) (⟨a.val,a.property.2⟩ : FixedCarrier D) u) v E b = 0 ∧
    normalizedCoefficient D hu (n+r-(j : ℤ)) u
      (mixedMode D hu (m+(j : ℤ)) (⟨a.val,a.property.2⟩ : FixedCarrier D) v) E b = 0 := by
  have firstEnergy := fixed_mode_energy_int D hu H ((H : ℤ)+d-(r+(j : ℤ))-1)
    d (r+(j : ℤ)) a u huH rfl
  have secondEnergy := fixed_mode_energy_int D hu K ((K : ℤ)+d-(m+(j : ℤ))-1)
    d (m+(j : ℤ)) a v hvK rfl
  constructor
  · by_cases negative : (H : ℤ)+d-(r+(j : ℤ))-1 < 0
    · have zero := integer_energy_zero D hu h24 _ _ firstEnergy (by omega)
      have input : mixedMode D hu (r+(j : ℤ))
          (⟨a.val,a.property.2⟩ : FixedCarrier D) u = 0 := Subtype.ext zero
      simp only [input, map_zero, LinearMap.zero_apply, DirectSum.zero_apply]
    · let W := ((H : ℤ)+d-(r+(j : ℤ))-1).toNat
      have hW : (W : ℤ) = (H : ℤ)+d-(r+(j : ℤ))-1 := Int.toNat_of_nonneg (by omega)
      apply normalized_off_grade D hu h24 W K (m+n-(j : ℤ)) E _ v _ hvK b
      · simpa only [hW] using firstEnergy
      · omega
  · by_cases negative : (K : ℤ)+d-(m+(j : ℤ))-1 < 0
    · have zero := integer_energy_zero D hu h24 _ _ secondEnergy (by omega)
      have input : mixedMode D hu (m+(j : ℤ))
          (⟨a.val,a.property.2⟩ : FixedCarrier D) v = 0 := Subtype.ext zero
      simp only [input, map_zero, LinearMap.zero_apply, DirectSum.zero_apply]
    · let W := ((K : ℤ)+d-(m+(j : ℤ))-1).toNat
      have hW : (W : ℤ) = (K : ℤ)+d-(m+(j : ℤ))-1 := Int.toNat_of_nonneg (by omega)
      apply normalized_off_grade D hu h24 H W (n+r-(j : ℤ)) E u _ huH _ b
      · simpa only [hW] using secondEnergy
      · omega

private theorem mixed_dual_off_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (d m n r E : ℤ) (a : fixedGrade D d)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (b : fixedGrade D E) (outside : E ≠ (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (j : ℕ) :
    oppositeAction D hu hD (m+r-(j : ℤ))
      (⟨a.val,a.property.2⟩ : FixedCarrier D)
      (normalizedCoefficient D hu (n+(j : ℤ)) u v) E b = 0 := by
  rw [oppositeAction_homogeneous]
  change (oppositeHomogeneous D hu hD d (m+r-(j : ℤ)) a
    (ambientCoefficient D hu (n+(j : ℤ)) u.val v.val)) E b = 0
  rw [homogeneous_coefficient D hu h24 H K (n+(j : ℤ)) u.val v.val huH hvK]
  change (oppositeHomogeneous D hu hD d (m+r-(j : ℤ)) a
    (DirectSum.lof ℂ ℤ (fun f => Module.Dual ℂ (fixedGrade D f))
      ((H : ℤ)+(K : ℤ)-(n+(j : ℤ))-1)
      ((fixedGrade D ((H : ℤ)+(K : ℤ)-(n+(j : ℤ))-1)).dualRestrict
        (kernel D hu H K (n+(j : ℤ)) u.val v.val)))) E b = 0
  simp only [oppositeHomogeneous, DirectSum.toModule_lof, LinearMap.comp_apply]
  have target : (H : ℤ)+(K : ℤ)-(n+(j : ℤ))-1+d-(m+r-(j : ℤ))-1 =
      (H : ℤ)+(K : ℤ)+d-m-n-r-2 := by ring
  simp [DirectSum.lof_eq_of, DirectSum.of_apply, target, outside, Ne.symm outside]

private theorem mixed_residual_homogeneous (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (d m n r : ℤ) (a : fixedGrade D d)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) :
    mixedResidual D hu hD m n r (⟨a.val,a.property.2⟩ : FixedCarrier D) u v = 0 := by
  classical
  let A : FixedCarrier D := ⟨a.val,a.property.2⟩
  obtain ⟨hl, hf, hs⟩ := mixed_families_finite D hu hD m n r A u v
  rw [mixed_residual_expansion]
  apply DFinsupp.ext
  intro E
  apply LinearMap.ext
  intro b
  let ev := restrictedEvaluation D E b
  change ev ((∑ᶠ j, mixedLeftTerm D hu m n r A u v j) -
    (∑ᶠ j, mixedFirstTerm D hu hD m n r A u v j) +
    (∑ᶠ j, mixedSecondTerm D hu m n r A u v j)) = 0
  rw [map_add, map_sub, map_finsum ev hl, map_finsum ev hf, map_finsum ev hs]
  by_cases hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2
  · have identity := mixed_homogeneous_grade_pairing D hu hD h24 H K d m n r E
      a b u v huH hvK hE
    have firstEval := ev.map_finsum hf
    change (∑ᶠ j, mixedFirstTerm D hu hD m n r A u v j) E b = _ at firstEval
    rw [firstEval] at identity
    have signedSecond : (∑ᶠ j, ev (mixedSecondTerm D hu m n r A u v j)) =
        (-1 : ℂ)^r * (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
          normalizedCoefficient D hu (n+r-(j : ℤ)) u
            (((fixedParitySlice D hu (-1)
              (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b) := by
      rw [mul_finsum]
      apply finsum_congr
      intro j
      change (((-1 : ℂ)^j * Ring.choose (r : ℂ) j) * (-1 : ℂ)^r) * _ = _
      ring
    rw [signedSecond]
    change (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j *
      normalizedCoefficient D hu (m+n-(j : ℤ))
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u) v E b) - _ + _ = 0
    linear_combination identity
  · have zl : ∀ j, ev (mixedLeftTerm D hu m n r A u v j) = 0 := by
      intro j
      have zero := (mixed_input_off_grade D hu h24 H K d m n r E a u v huH hvK b hE j).1
      change Ring.choose (m : ℂ) j * _ = 0
      rw [zero, mul_zero]
    have zf : ∀ j, ev (mixedFirstTerm D hu hD m n r A u v j) = 0 := by
      intro j
      have zero := mixed_dual_off_grade D hu hD h24 H K d m n r E a u v huH hvK b hE j
      change ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) * _ = 0
      rw [zero, mul_zero]
    have zs : ∀ j, ev (mixedSecondTerm D hu m n r A u v j) = 0 := by
      intro j
      have zero := (mixed_input_off_grade D hu h24 H K d m n r E a u v huH hvK b hE j).2
      change (((-1 : ℂ)^j * Ring.choose (r : ℂ) j) * (-1 : ℂ)^r) * _ = 0
      rw [zero, mul_zero]
    simp only [zl, zf, zs, finsum_zero, sub_zero, add_zero]

open private basis_parity negative_support
  from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private fixedProjection from D5.S3.VertexAlgebra.TwistedGround.MixedOpposite

private def actualInputBasis (D : LatticeData) (hu : IsUnit D.G.det)
    (u : paritySpace D hu (-1))
    (i : {i : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu) //
      i ∈ ((actualAmbientBasis D hu).repr u.val).support}) : paritySpace D hu (-1) :=
  ⟨actualAmbientBasis D hu i.val, by
    have odd := negative_support D hu u i.val i.property
    simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rw [basis_parity, neg_one_pow_eq_pow_mod_two, odd]
    norm_num⟩

private theorem actual_input_basis_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (u : paritySpace D hu (-1)) :
    (∑ i ∈ ((actualAmbientBasis D hu).repr u.val).support.attach,
      ((actualAmbientBasis D hu).repr u.val i.val) • actualInputBasis D hu u i) = u := by
  classical
  apply Subtype.ext
  change (∑ i ∈ ((actualAmbientBasis D hu).repr u.val).support.attach,
    ((actualAmbientBasis D hu).repr u.val i.val) • actualAmbientBasis D hu i.val) = u.val
  rw [Finset.sum_attach]
  exact (actualAmbientBasis D hu).linearCombination_repr u.val

private theorem actual_input_basis_energy (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (u : paritySpace D hu (-1))
    (i : {i : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu) //
      i ∈ ((actualAmbientBasis D hu).repr u.val).support}) :
    actualTensorL0 D hu (actualInputBasis D hu u i).val =
      (((oddWeight D i.val.1+3)/2 : ℕ) : ℂ) • (actualInputBasis D hu u i).val := by
  have odd := negative_support D hu u i.val i.property
  have energy := actual_basis_eigenvalue D hu i.val.1 i.val.2
  change actualTensorL0 D hu (actualAmbientBasis D hu i.val) = _
  rw [energy, h24]
  congr 1
  have h : oddWeight D i.val.1+3 = 2*((oddWeight D i.val.1+3)/2) := by omega
  have hc : (oddWeight D i.val.1 : ℂ)+3 =
      2*(((oddWeight D i.val.1+3)/2 : ℕ) : ℂ) := by exact_mod_cast h
  linear_combination hc / 2

private def fixedSourceInclusion (D : LatticeData) (d : ℤ) :
    fixedGrade D d →ₗ[ℂ] FixedCarrier D where
  toFun a := ⟨a.val,a.property.2⟩
  map_add' a b := rfl
  map_smul' z a := rfl

private theorem fixed_source_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (a : FixedCarrier D) :
    (∑ d ∈ stateEnergies D a.val,
      fixedSourceInclusion D d (fixedProjection D hu d a)) = a := by
  classical
  apply Subtype.ext
  change (∑ d ∈ stateEnergies D a.val,
    (2 : ℂ)⁻¹ • (gradeProjection D d a.val + theta D (gradeProjection D d a.val))) = a.val
  rw [← Finset.smul_sum, Finset.sum_add_distrib]
  change (2 : ℂ)⁻¹ • ((∑ d ∈ stateEnergies D a.val, gradeProjection D d a.val) +
    ∑ d ∈ stateEnergies D a.val, thetaLinear D (gradeProjection D d a.val)) = a.val
  rw [← map_sum, sum_gradeProjections, (mem_fixedSpace D a.val).mp a.property]
  module

private theorem mixed_residual_fixed_source (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (d m n r : ℤ) (a : fixedGrade D d) (u v : paritySpace D hu (-1)) :
    mixedResidual D hu hD m n r (⟨a.val,a.property.2⟩ : FixedCarrier D) u v = 0 := by
  classical
  rw [← actual_input_basis_expansion D hu u, ← actual_input_basis_expansion D hu v]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    RingHom.id_apply, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [mixed_residual_homogeneous D hu hD h24
    ((oddWeight D i.val.1+3)/2) ((oddWeight D j.val.1+3)/2) d m n r a
    (actualInputBasis D hu u i) (actualInputBasis D hu v j)
    (actual_input_basis_energy D hu h24 u i) (actual_input_basis_energy D hu h24 v j)]
  simp only [smul_zero]

private theorem mixed_residual_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) :
    mixedResidual D hu hD m n r a u v = 0 := by
  classical
  rw [← fixed_source_expansion D hu a]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  exact mixed_residual_fixed_source D hu hD h24 d m n r (fixedProjection D hu d a) u v

/-- The complete signed two-twisted-input mixed Jacobi law, with the actual
opposite action on the original fixed restricted dual. The three actual
families have finite support before any interchange of sums. The source and
both inputs are extended through their actual finite homogeneous expansions;
no generating-source, sign-of-mode or selected target-grade restriction is
present. This identity supplies no three-twisted crossing premise. -/
theorem mixed_jacobi (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) :
    (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j •
      normalizedCoefficient D hu (m+n-(j : ℤ))
        (((fixedParitySlice D hu (-1) a)[[r+(j : ℤ)]]) u) v) =
    ∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
      (oppositeAction D hu hD (m+r-(j : ℤ)) a
        (normalizedCoefficient D hu (n+(j : ℤ)) u v) -
       (-1 : ℂ)^r • normalizedCoefficient D hu (n+r-(j : ℤ)) u
         (((fixedParitySlice D hu (-1) a)[[m+(j : ℤ)]]) v)) := by
  have zero := mixed_residual_zero D hu hD h24 m n r a u v
  rw [mixed_residual_expansion] at zero
  obtain ⟨hl, hf, hs⟩ := mixed_families_finite D hu hD m n r a u v
  change (∑ᶠ j, mixedLeftTerm D hu m n r a u v j) = _
  calc
    _ = (∑ᶠ j, mixedFirstTerm D hu hD m n r a u v j) -
        (∑ᶠ j, mixedSecondTerm D hu m n r a u v j) := by
      apply eq_of_sub_eq_zero
      convert zero using 1 <;> abel
    _ = ∑ᶠ j, (mixedFirstTerm D hu hD m n r a u v j -
        mixedSecondTerm D hu m n r a u v j) := (finsum_sub_distrib hf hs).symm
    _ = _ := by
      apply finsum_congr
      intro j
      simp only [mixedFirstTerm, mixedSecondTerm, mixedMode, smul_sub, smul_smul]

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
