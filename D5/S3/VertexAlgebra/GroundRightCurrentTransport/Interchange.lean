/- GID: D5/S3/VertexAlgebra/GroundRightCurrentTransport/Interchange
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GroundRightCurrentTransport/Interchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete ground simple-pole residue and inverse-product interchange. -/

import D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue

/-! Complete supported residue calculus for the native ground-current consumer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct VertexOperator
open D5.S3.VertexAlgebra

namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport

universe u

namespace Calculus

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

local macro "ext_modes" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.ext_modes))
local macro "R_mode" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.R_mode))
local macro "Z_mode" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Z_mode))
local macro "R_zero" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.R_zero))
local macro "R_add" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.R_add))
local macro "R_sum" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.R_sum))
local macro "R_smul" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.R_smul))
local macro "R_Z" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.R_Z))
local macro "Q_cutoff" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_cutoff))
local macro "forward_finite" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.forward_finite))
local macro "reverse_finite" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.reverse_finite))
local macro "swap_finite" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.swap_finite))
local macro "nested_expansion" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.nested_expansion))
local macro "nested_finite" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.nested_finite))
local macro "residue_convolution" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.residue_convolution))
local macro "valid_of_locality" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.valid_of_locality))
local macro "finiteConvolution" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds.finite_convolution))

private theorem nested_cell_interchange (A A0 J B : VertexOperator ℂ M)
    (r d n : ℤ) (j k : ℕ)
    (ward : ∀ z t : ℤ, J[[z]] * A[[t]] - A[[t]] * J[[z]] = A0[[z+t]]) :
    nestedCell A J B r d n j k - nestedCell J A B d r n k j =
      -groundCorrectionCell (fun z => A0[[z]]) (fun z => B[[z]])
        r d n 0 0 0 j k := by
  have h := ground_cell_cancellation (fun z => A[[z]]) (fun z => A0[[z]])
    (fun z => B[[z]]) (fun z => J[[z]]) r d n 0 0 0 j k ward
  calc
    _ = groundLeftCell (fun z => A[[z]]) (fun z => B[[z]])
          (fun z => J[[z]]) r d n 0 0 0 j k -
        groundRightCell (fun z => A[[z]]) (fun z => B[[z]])
          (fun z => J[[z]]) r d n 0 0 0 j k := by
      simp only [nestedCell, groundLeftCell, groundRightCell,
        groundCellWeight, Nat.cast_zero, add_zero, sub_zero,
        Ring.choose_zero_right, one_mul]
      rw [mul_comm (residueWeight d k) (residueWeight r j)]
      rw [show n+(k:ℤ)+j = n+j+k by omega,
        show n+(k:ℤ)+r-j = n+r-j+k by omega,
        show n+d-(k:ℤ)+j = n+j+d-k by omega,
        show n+d+r-(k:ℤ)-j = n+r+d-j-k by omega]
      module
    _ = _ := by rw [h]; abel

private theorem R_interchange (A A0 J B : VertexOperator ℂ M) (r d : ℤ)
    (ward : ∀ z t : ℤ, J[[z]] * A[[t]] - A[[t]] * J[[z]] = A0[[z+t]]) :
    R A (R J B d) r = R J (R A B r) d - R A0 B (r+d) := by
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  have hf := nested_finite A J B r d n x
  have hg := swap_finite (nested_finite J A B d r n x)
  let v (h : ℕ) :=
    (A0 [[r+d-h]]) ((B [[n+h]]) x) -
      (-1 : ℂ)^(r+d) • (B [[n+r+d-h]]) ((A0 [[h]]) x)
  have finite : Function.HasFiniteSupport v := by
    have reverse := (reverse_finite A0 B (r+d) n x).smul_right
      (fun _ => (-1 : ℂ)^(r+d))
    simpa only [v, Pi.smul_def', Pi.sub_def, add_assoc] using
      (forward_finite A0 B (r+d) n x).sub reverse
  have convolution := residue_convolution r d v finite
  have coefficient : (∑ᶠ h : ℕ, residueWeight (r+d) h • v h) =
      ((R A0 B (r+d))[[n]]) x := by
    have reverse := (reverse_finite A0 B (r+d) n x).smul_right
      (fun h => residueWeight (r+d) h)
    have forward := (forward_finite A0 B (r+d) n x).smul_right
      (fun h => residueWeight (r+d) h)
    simp only [Pi.smul_def'] at reverse forward
    rw [R_mode]
    simp only [v, smul_sub]
    simp_rw [smul_comm (residueWeight (r+d) _) ((-1 : ℂ)^(r+d))]
    have reverseScaled := reverse.smul_right (fun _ => (-1 : ℂ)^(r+d))
    simp only [Pi.smul_def'] at reverseScaled
    rw [finsum_sub_distrib forward (by simpa only [add_assoc] using reverseScaled),
      ← smul_finsum' ((-1 : ℂ)^(r+d)) (by simpa only [add_assoc] using reverse)]
    simp only [add_assoc]
  have cell (p : ℕ × ℕ) : nestedCell A J B r d n p.1 p.2 x -
      nestedCell J A B d r n p.2 p.1 x =
      -((residueWeight r p.1 * residueWeight d p.2) • v (p.1+p.2)) := by
    have law := congrArg (fun L : Module.End ℂ M => L x)
      (nested_cell_interchange A A0 J B r d n p.1 p.2 ward)
    simp only [LinearMap.sub_apply, LinearMap.neg_apply,
      groundCorrectionCell, groundCellWeight, Nat.cast_zero,
      add_zero, sub_zero, Ring.choose_zero_right, one_mul,
      LinearMap.smul_apply, Module.End.mul_apply] at law
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)] at law
    simpa only [v, Nat.cast_add, sub_sub, add_assoc] using law
  simp only [map_sub, Pi.sub_apply, LinearMap.sub_apply]
  rw [nested_expansion, nested_expansion]
  have swapped : (∑ᶠ p : ℕ × ℕ, nestedCell J A B d r n p.1 p.2 x) =
      ∑ᶠ p : ℕ × ℕ, nestedCell J A B d r n p.2 p.1 x :=
    (finsum_comp_equiv (Equiv.prodComm ℕ ℕ)).symm
  rw [swapped]
  suffices difference :
      (∑ᶠ p : ℕ × ℕ, nestedCell A J B r d n p.1 p.2 x) -
        (∑ᶠ p : ℕ × ℕ, nestedCell J A B d r n p.2 p.1 x) =
          -((R A0 B (r+d))[[n]]) x by
    simpa only [sub_eq_add_neg, add_comm] using sub_eq_iff_eq_add.mp difference
  calc
    _ = ∑ᶠ p : ℕ × ℕ, (nestedCell A J B r d n p.1 p.2 x -
        nestedCell J A B d r n p.2 p.1 x) := (finsum_sub_distrib hf hg).symm
    _ = -(∑ᶠ p : ℕ × ℕ,
        (residueWeight r p.1 * residueWeight d p.2) • v (p.1+p.2)) := by
      simp_rw [cell]
      rw [finsum_neg_distrib]
    _ = -((R A0 B (r+d))[[n]]) x := by rw [convolution, coefficient]

private theorem Z_zero (c : ℤ) : Z c (0 : VertexOperator ℂ M) = 0 := by
  apply ext_modes
  intro n
  simp only [Z_mode, map_zero, Pi.zero_apply]

private theorem Z_sub (c : ℤ) (A B : VertexOperator ℂ M) :
    Z c (A-B) = Z c A - Z c B := by
  apply ext_modes
  intro n
  simp only [Z_mode, map_sub, Pi.sub_apply]

private theorem Z_smul (c : ℤ) (a : ℂ) (A : VertexOperator ℂ M) :
    Z c (a • A) = a • Z c A := by
  apply ext_modes
  intro n
  simp only [Z_mode, map_smul, Pi.smul_apply]

private theorem Z_sum (c : ℤ) {I : Type*} (s : Finset I) (f : I → VertexOperator ℂ M) :
    Z c (∑ i ∈ s, f i) = ∑ i ∈ s, Z c (f i) := by
  apply ext_modes
  intro n
  simp only [Z_mode, map_sum, Finset.sum_apply]

private theorem Z_Z (c e : ℤ) (A : VertexOperator ℂ M) :
    Z c (Z e A) = Z (c+e) A := by
  apply ext_modes
  intro n
  simp only [Z_mode]
  rw [show n-c-e = n-(c+e) by omega]

private theorem Q_pad (A B : VertexOperator ℂ M) (s r : ℤ) (K L : ℕ)
    (valid : Valid A B K) (length : (K : ℤ) ≤ r+L) :
    Q A B s r K = ∑ ell ∈ Finset.range L,
      Ring.choose (-(s : ℂ)/2) ell • Z ell (R A B (r+ell)) := by
  let K' := (r+(L:ℤ)).toNat
  have hle : K ≤ K' := by dsimp [K']; omega
  have valid' : Valid A B K' := fun t ht => valid t (by omega)
  rw [Q_cutoff A B s r K K' valid valid']
  have equality : ((K' : ℤ)-r).toNat = L := by dsimp [K']; omega
  simp only [Q, equality]

private theorem Q_left_valid (A A0 J B : VertexOperator ℂ M)
    (d : ℤ) (KAB KJB K0 : ℕ)
    (hAB : Valid A B KAB) (h0 : Valid A0 B K0)
    (ward : ∀ z t : ℤ, J[[z]] * A[[t]] - A[[t]] * J[[z]] = A0[[z+t]]) :
    Valid A (Q J B 1 d KJB) (max KAB ((K0 : ℤ)-d).toNat) := by
  intro r hr
  simp only [Q, R_sum, R_smul, R_Z]
  apply Finset.sum_eq_zero
  intro v hv
  rw [R_interchange A A0 J B r (d+v) ward, hAB r (by omega), R_zero,
    h0 (r+(d+v)) (by omega), sub_zero, Z_zero, smul_zero]

private theorem Q_right_valid (A A0 J B : VertexOperator ℂ M)
    (r s : ℤ) (KAB KJB K0 : ℕ)
    (hJB : Valid J B KJB) (h0 : Valid A0 B K0)
    (ward : ∀ z t : ℤ, J[[z]] * A[[t]] - A[[t]] * J[[z]] = A0[[z+t]]) :
    Valid J (Q A B s r KAB) (max KJB ((K0 : ℤ)-r).toNat) := by
  intro d hd
  simp only [Q, R_sum, R_smul, R_Z]
  apply Finset.sum_eq_zero
  intro ell hell
  have h := R_interchange A A0 J B (r+ell) d ward
  rw [hJB d (by omega), R_zero, h0 (r+ell+d) (by omega), sub_zero] at h
  rw [← h, Z_zero, smul_zero]

private theorem Q_nested (A J B : VertexOperator ℂ M) (s t r d : ℤ)
    (KO KI L : ℕ) (outerValid : Valid A (Q J B t d KI) KO)
    (innerValid : Valid J B KI)
    (outerLength : (KO : ℤ) ≤ r+L) (innerLength : (KI : ℤ) ≤ d+L) :
    Q A (Q J B t d KI) s r KO =
      ∑ ell ∈ Finset.range L, ∑ v ∈ Finset.range L,
        (Ring.choose (-(s : ℂ)/2) ell * Ring.choose (-(t : ℂ)/2) v) •
          Z ((ell+v : ℕ) : ℤ) (R A (R J B (d+v)) (r+ell)) := by
  rw [Q_pad A (Q J B t d KI) s r KO L outerValid outerLength,
    Q_pad J B t d KI L innerValid innerLength]
  simp only [R_sum, R_smul, R_Z, Z_sum, Z_smul, Z_Z, Finset.smul_sum,
    smul_smul, Nat.cast_add]

private theorem correction_convolution (A0 B : VertexOperator ℂ M)
    (s r d : ℤ) (K L : ℕ) (valid : Valid A0 B K)
    (length : (K : ℤ) ≤ r+d+L) :
    (∑ ell ∈ Finset.range L, ∑ v ∈ Finset.range L,
      (Ring.choose (-(s : ℂ)/2) ell * Ring.choose (-1/2 : ℂ) v) •
        Z ((ell+v : ℕ) : ℤ) (R A0 B (r+ell+(d+v)))) =
      Q A0 B (s+1) (r+d) K := by
  let seq (z : ℕ) := Z z (R A0 B (r+d+z))
  have tail (z : ℕ) (hz : L ≤ z) : seq z = 0 := by
    dsimp only [seq]
    rw [valid (r+d+z) (by omega), Z_zero]
  have convolution := finiteConvolution (-(s : ℂ)/2) (-1/2 : ℂ) L seq tail
  rw [show -(s : ℂ)/2 + -1/2 = -((s+1 : ℤ) : ℂ)/2 by push_cast; ring] at convolution
  rw [Q_pad A0 B (s+1) (r+d) K L valid length]
  simp only [Finset.smul_sum, smul_smul, seq, Nat.cast_add] at convolution
  convert convolution using 1
  apply Finset.sum_congr rfl
  intro ell hell
  apply Finset.sum_congr rfl
  intro v hv
  rw [show r+(ell:ℤ)+(d+v) = r+d+((ell:ℤ)+v) by omega]
  simp only [Nat.cast_add]

private theorem Q_interchange (A A0 J B : VertexOperator ℂ M) (s r d : ℤ)
    (KAB KJB K0 : ℕ) (hAB : Valid A B KAB) (hJB : Valid J B KJB)
    (h0 : Valid A0 B K0)
    (ward : ∀ z t : ℤ, J[[z]] * A[[t]] - A[[t]] * J[[z]] = A0[[z+t]]) :
    Q A (Q J B 1 d KJB) s r (max KAB ((K0 : ℤ)-d).toNat) =
      Q J (Q A B s r KAB) 1 d (max KJB ((K0 : ℤ)-r).toNat) -
        Q A0 B (s+1) (r+d) K0 := by
  let L := max (max KAB KJB)
    (max (((max KAB ((K0 : ℤ)-d).toNat : ℕ) : ℤ)-r).toNat
      (max (((max KJB ((K0 : ℤ)-r).toNat : ℕ) : ℤ)-d).toNat
        (max ((K0 : ℤ)-r-d).toNat
          (max ((KAB : ℤ)-r).toNat ((KJB : ℤ)-d).toNat))))
  have hleft := Q_left_valid A A0 J B d KAB KJB K0 hAB h0 ward
  have hright := Q_right_valid A A0 J B r s KAB KJB K0 hJB h0 ward
  have lleft : ((max KAB ((K0 : ℤ)-d).toNat : ℕ) : ℤ) ≤ r+L := by dsimp [L]; omega
  have lright : ((max KJB ((K0 : ℤ)-r).toNat : ℕ) : ℤ) ≤ d+L := by dsimp [L]; omega
  have lab : (KAB : ℤ) ≤ r+L := by dsimp [L]; omega
  have ljb : (KJB : ℤ) ≤ d+L := by dsimp [L]; omega
  have l0 : (K0 : ℤ) ≤ r+d+L := by dsimp [L]; omega
  rw [Q_nested A J B s 1 r d _ _ L hleft hJB lleft ljb,
    Q_nested J A B 1 s d r _ _ L hright hAB lright lab]
  simp only [Int.cast_one]
  simp_rw [R_interchange A A0 J B _ _ ward, Z_sub, smul_sub,
    Finset.sum_sub_distrib]
  rw [correction_convolution A0 B s r d K0 L h0 l0]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ell hell
  apply Finset.sum_congr rfl
  intro v hv
  rw [mul_comm, Nat.add_comm v ell]

private theorem R_sub (A B C : VertexOperator ℂ M) (r : ℤ) :
    R A (B-C) r = R A B r - R A C r := by
  calc
    _ = R A (B+(-1 : ℂ) • C) r := by rw [neg_one_smul, sub_eq_add_neg]
    _ = _ := by rw [R_add, R_smul, neg_one_smul, ← sub_eq_add_neg]

private theorem Q_sub (A B C : VertexOperator ℂ M) (s r : ℤ) (K : ℕ) :
    Q A (B-C) s r K = Q A B s r K - Q A C s r K := by
  simp only [Q, R_sub, Z_sub, smul_sub, Finset.sum_sub_distrib]

private theorem Q_zero (A : VertexOperator ℂ M) (s r : ℤ) (K : ℕ) :
    Q A 0 s r K = 0 := by simp only [Q, R_zero, Z_zero, smul_zero, Finset.sum_const_zero]

end Calculus
end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
