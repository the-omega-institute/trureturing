/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket
   mirror-E: none(waiver:actual-brst-odd-bracket)
   anchors: []
   utility: none
   digest: Actual odd derived-bracket identities on the full lattice BRST quotient.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State ghostB)
open LatticeBRSTCohomologyField
open LatticeBRSTZeroEnergyReduction
open D5.S3.VertexAlgebra.LatticeBRSTCohomologyBVSecondOrder
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock (ket)
open private fullBasis_apply energyWeight_basis from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private b_parity from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder
open private current_classOf quotient_current_leibniz from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder

noncomputable section

variable (D : LatticeData)
  (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26)
  (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
  (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)

theorem P0_parity_commutes :
    P0 D * LatticeMatterGhostStateField.parity D =
      LatticeMatterGhostStateField.parity D * P0 D := by
  apply (fullBasis D).ext
  intro label
  have hp : LatticeMatterGhostStateField.parity D (fullBasis D label) =
      (-1 : ℂ)^label.2.card • fullBasis D label := by
    rw [fullBasis_apply]
    simp only [LatticeMatterGhostStateField.parity, TensorProduct.map_tmul,
      LinearMap.id_apply, parity_ket, TensorProduct.tmul_smul]
  change energyWeight D (fun energy => if energy = 0 then 1 else 0)
      (LatticeMatterGhostStateField.parity D (fullBasis D label)) =
    LatticeMatterGhostStateField.parity D
      (energyWeight D (fun energy => if energy = 0 then 1 else 0)
        (fullBasis D label))
  rw [hp, map_smul, energyWeight_basis, map_smul, hp]
  simp only [smul_smul]
  rw [mul_comm]

theorem Delta_parity (a : Cohomology D H h26 hHG hGH) :
    parity D H h26 hHG hGH (Delta D H h26 hHG hGH a) =
      -Delta D H h26 hHG hGH (parity D H h26 hHG hGH a) := by
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  simp only [Delta_classOf, parity_classOf]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  change LatticeMatterGhostStateField.parity D
      (ghostB D 0 (P0 D (x : State D))) =
    -ghostB D 0 (P0 D (LatticeMatterGhostStateField.parity D x))
  have hP := LinearMap.congr_fun (P0_parity_commutes (D := D)) (x : State D)
  have hP' : P0 D (LatticeMatterGhostStateField.parity D x) =
      LatticeMatterGhostStateField.parity D (P0 D x) := by
    simpa only [Module.End.mul_apply] using hP
  rw [b_parity, ← hP']

def oddBracket : Cohomology D H h26 hHG hGH →ₗ[ℂ]
    Cohomology D H h26 hHG hGH →ₗ[ℂ] Cohomology D H h26 hHG hGH :=
  (cohomologyCurrent D H h26 hHG hGH).comp (parity D H h26 hHG hGH)

@[simp] theorem oddBracket_apply (a b : Cohomology D H h26 hHG hGH) :
    oddBracket D H h26 hHG hGH a b =
      cohomologyCurrent D H h26 hHG hGH (parity D H h26 hHG hGH a) b := rfl

theorem cohomologyCurrent_parity (a b : Cohomology D H h26 hHG hGH) :
    parity D H h26 hHG hGH (cohomologyCurrent D H h26 hHG hGH a b) =
      -cohomologyCurrent D H h26 hHG hGH
        (parity D H h26 hHG hGH a) (parity D H h26 hHG hGH b) := by
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  obtain ⟨y, rfl⟩ := classOf_surjective D H h26 hHG hGH b
  rw [current_classOf]
  simp only [parity_classOf]
  rw [current_classOf]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  change LatticeMatterGhostStateField.parity D
      (originalMode D 0 (ghostB D (-1) (x : State D)) (y : State D)) =
    -originalMode D 0
      (ghostB D (-1) (LatticeMatterGhostStateField.parity D x))
      (LatticeMatterGhostStateField.parity D y)
  have hp := LinearMap.congr_fun
    (LatticeMatterGhostStateField.stateField_parity D
      (ghostB D (-1) (x : State D)) 0) (y : State D)
  simpa only [originalMode_apply, Module.End.mul_apply, b_parity,
    map_neg, LinearMap.neg_apply, Pi.neg_apply] using hp

theorem oddBracket_parity (a b : Cohomology D H h26 hHG hGH) :
    parity D H h26 hHG hGH (oddBracket D H h26 hHG hGH a b) =
      -oddBracket D H h26 hHG hGH
        (parity D H h26 hHG hGH a) (parity D H h26 hHG hGH b) := by
  rw [oddBracket_apply, cohomologyCurrent_parity, oddBracket_apply,
    parity_involution]

theorem oddBracket_generator (a b : Cohomology D H h26 hHG hGH) (p : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ)^p • a) :
    oddBracket D H h26 hHG hGH a b =
      (-1 : ℂ)^p • Delta D H h26 hHG hGH (product D H h26 hHG hGH a b) -
        (-1 : ℂ)^p • product D H h26 hHG hGH
          (Delta D H h26 hHG hGH a) b -
        product D H h26 hHG hGH a (Delta D H h26 hHG hGH b) := by
  have hdef := Delta_product_defect D H h26 hHG hGH a b
  rw [oddBracket_apply, ha, map_smul]
  simp only [LinearMap.smul_apply]
  rw [← hdef]
  have hs : (-1 : ℂ)^p * (-1 : ℂ)^p = 1 := by
    rw [← mul_pow]
    norm_num
  rw [ha, map_smul]
  simp only [LinearMap.smul_apply]
  let s : ℂ := (-1 : ℂ)^p
  let A : Cohomology D H h26 hHG hGH :=
    Delta D H h26 hHG hGH (product D H h26 hHG hGH a b)
  let B : Cohomology D H h26 hHG hGH :=
    product D H h26 hHG hGH (Delta D H h26 hHG hGH a) b
  let C : Cohomology D H h26 hHG hGH :=
    product D H h26 hHG hGH a (Delta D H h26 hHG hGH b)
  change s • ((A - B) - s • C) = (s • A - s • B) - C
  have hs' : s * s = 1 := by simpa [s] using hs
  have hss : s • (s • C) = C := by
    calc
      s • (s • C) = (s * s) • C := smul_smul s s C
      _ = C := (congrArg (fun r : ℂ => r • C) hs').trans (one_smul ℂ C)
  calc
    s • ((A - B) - s • C) = s • (A - B) - s • (s • C) :=
      smul_sub s (A - B) (s • C)
    _ = (s • A - s • B) - C := by
      calc
        s • (A - B) - s • (s • C) =
            (s • A - s • B) - s • (s • C) := by
              exact congrArg (fun z => z - s • (s • C)) (smul_sub s A B)
        _ = (s • A - s • B) - C := by rw [hss]

theorem Delta_homogeneous (a : Cohomology D H h26 hHG hGH) (p : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ)^p • a) :
    parity D H h26 hHG hGH (Delta D H h26 hHG hGH a) =
      (-1 : ℂ)^(p + 1) • Delta D H h26 hHG hGH a := by
  calc
    parity D H h26 hHG hGH (Delta D H h26 hHG hGH a) =
        -Delta D H h26 hHG hGH (parity D H h26 hHG hGH a) :=
      Delta_parity D H h26 hHG hGH a
    _ = -Delta D H h26 hHG hGH ((-1 : ℂ)^p • a) := by rw [ha]
    _ = -((-1 : ℂ)^p • Delta D H h26 hHG hGH a) := by
      rw [map_smul]
    _ = (-1 : ℂ)^(p + 1) • Delta D H h26 hHG hGH a := by
      rw [pow_succ]
      calc
        -((-1 : ℂ)^p • Delta D H h26 hHG hGH a) =
            (-((-1 : ℂ)^p)) • Delta D H h26 hHG hGH a :=
          (neg_smul ((-1 : ℂ)^p) (Delta D H h26 hHG hGH a)).symm
        _ = ((-1 : ℂ)^p * (-1)) • Delta D H h26 hHG hGH a := by
          congr 1
          ring

theorem oddBracket_homogeneous (a b : Cohomology D H h26 hHG hGH) (p q : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ)^p • a)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ)^q • b) :
    parity D H h26 hHG hGH (oddBracket D H h26 hHG hGH a b) =
      (-1 : ℂ)^(p + q + 1) • oddBracket D H h26 hHG hGH a b := by
  rw [oddBracket_parity, ha, hb, map_smul, map_smul]
  rw [LinearMap.smul_apply,
    smul_smul ((-1 : ℂ)^q) ((-1 : ℂ)^p)
      (oddBracket D H h26 hHG hGH a b)]
  have hpq : (-1 : ℂ)^p * (-1 : ℂ)^q = (-1 : ℂ)^(p + q) := by
    rw [← pow_add]
  have hqp : (-1 : ℂ)^q * (-1 : ℂ)^p = (-1 : ℂ)^(p + q) := by
    rw [mul_comm, hpq]
  rw [hqp, pow_succ]
  calc
    -((-1 : ℂ) ^ (p + q) • oddBracket D H h26 hHG hGH a b) =
        (-((-1 : ℂ) ^ (p + q))) • oddBracket D H h26 hHG hGH a b :=
      (neg_smul ((-1 : ℂ) ^ (p + q))
        (oddBracket D H h26 hHG hGH a b)).symm
    _ = ((-1 : ℂ) ^ (p + q) * (-1)) •
        oddBracket D H h26 hHG hGH a b := by
      congr 1
      ring

theorem oddBracket_antisymm (a b : Cohomology D H h26 hHG hGH) (p q : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ)^p • a)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ)^q • b) :
    oddBracket D H h26 hHG hGH a b =
      -((-1 : ℂ)^((p + 1) * (q + 1))) •
        oddBracket D H h26 hHG hGH b a := by
  have hDa := Delta_homogeneous D H h26 hHG hGH a p ha
  have hDb := Delta_homogeneous D H h26 hHG hGH b q hb
  have hab := product_supercomm D H h26 hHG hGH a b p q ha hb
  have hDab := product_supercomm D H h26 hHG hGH
    (Delta D H h26 hHG hGH a) b (p + 1) q hDa hb
  have habD := product_supercomm D H h26 hHG hGH
    a (Delta D H h26 hHG hGH b) p (q + 1) ha hDb
  rw [oddBracket_generator D H h26 hHG hGH a b p ha,
    oddBracket_generator D H h26 hHG hGH b a q hb, hab, hDab, habD]
  rw [map_smul,
    smul_smul ((-1 : ℂ)^p) ((-1 : ℂ)^(p * q))
      (Delta D H h26 hHG hGH (product D H h26 hHG hGH b a))]
  have expand (u : ℂ) (x y z : Cohomology D H h26 hHG hGH) :
      u • ((x - y) - z) = (u • x - u • y) - u • z := by
    calc
      u • ((x - y) - z) = u • (x - y) - u • z :=
        smul_sub u (x - y) z
      _ = (u • x - u • y) - u • z := by
        exact congrArg (fun t => t - u • z) (smul_sub u x y)
  conv_rhs => rw [expand]
  rw [smul_smul (-((-1 : ℂ)^((p + 1) * (q + 1)))) ((-1 : ℂ)^q)
      (Delta D H h26 hHG hGH (product D H h26 hHG hGH b a))]
  rw [smul_smul (-((-1 : ℂ)^((p + 1) * (q + 1)))) ((-1 : ℂ)^q)
      (product D H h26 hHG hGH (Delta D H h26 hHG hGH b) a)]
  rw [smul_smul ((-1 : ℂ)^p) ((-1 : ℂ)^((p + 1) * q))
      (product D H h26 hHG hGH b (Delta D H h26 hHG hGH a))]
  have period (n k : ℕ) : (-1 : ℂ)^(n + 2 * k) = (-1 : ℂ)^n := by
    rw [pow_add, pow_mul]
    norm_num
  have hA : (-1 : ℂ)^p * (-1 : ℂ)^(p * q) =
      (-(-1 : ℂ)^((p + 1) * (q + 1))) * (-1 : ℂ)^q := by
    calc
      (-1 : ℂ)^p * (-1 : ℂ)^(p * q) =
          (-1 : ℂ)^(p + p * q) := by rw [← pow_add]
      _ = (-1 : ℂ)^(p + p * q + 2 * (q + 1)) := by
        symm
        exact period (p + p * q) (q + 1)
      _ = (-1 : ℂ)^((p + 1) * (q + 1) + q + 1) := by
        congr 1
        ring
      _ = (-1 : ℂ) * ((-1 : ℂ)^((p + 1) * (q + 1)) * (-1 : ℂ)^q) := by
        rw [pow_add, pow_add]
        norm_num
      _ = (-(-1 : ℂ)^((p + 1) * (q + 1))) * (-1 : ℂ)^q := by ring
  have hB : (-1 : ℂ)^p * (-1 : ℂ)^((p + 1) * q) =
      -(-1 : ℂ)^((p + 1) * (q + 1)) := by
    calc
      (-1 : ℂ)^p * (-1 : ℂ)^((p + 1) * q) =
          (-1 : ℂ)^(p + (p + 1) * q) := by rw [← pow_add]
      _ = (-1 : ℂ)^(p + (p + 1) * q + 2) := by
        symm
        exact period (p + (p + 1) * q) 1
      _ = (-1 : ℂ)^((p + 1) * (q + 1) + 1) := by
        congr 1
        ring
      _ = -(-1 : ℂ)^((p + 1) * (q + 1)) := by
        rw [pow_add]
        norm_num
  have hC : (-1 : ℂ)^(p * (q + 1)) =
      (-(-1 : ℂ)^((p + 1) * (q + 1))) * (-1 : ℂ)^q := by
    calc
      (-1 : ℂ)^(p * (q + 1)) =
          (-1 : ℂ)^(p * (q + 1) + 2 * (q + 1)) := by
        exact (period (p * (q + 1)) (q + 1)).symm
      _ = (-1 : ℂ)^((p + 1) * (q + 1) + q + 1) := by
        congr 1
        ring
      _ = (-1 : ℂ) * ((-1 : ℂ)^((p + 1) * (q + 1)) * (-1 : ℂ)^q) := by
        rw [pow_add, pow_add]
        norm_num
      _ = (-(-1 : ℂ)^((p + 1) * (q + 1))) * (-1 : ℂ)^q := by ring
  rw [hA, hB, hC]
  abel

theorem oddBracket_leibniz (a b c : Cohomology D H h26 hHG hGH) (p q : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ)^p • a)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ)^q • b) :
    oddBracket D H h26 hHG hGH a (product D H h26 hHG hGH b c) =
      product D H h26 hHG hGH (oddBracket D H h26 hHG hGH a b) c +
        (-1 : ℂ)^((p + 1) * q) •
          product D H h26 hHG hGH b (oddBracket D H h26 hHG hGH a c) := by
  have hpa : parity D H h26 hHG hGH (parity D H h26 hHG hGH a) =
      (-1 : ℂ)^p • parity D H h26 hHG hGH a := by
    rw [parity_involution, ha]
    rw [smul_smul ((-1 : ℂ)^p) ((-1 : ℂ)^p) a]
    have hs : (-1 : ℂ)^p * (-1 : ℂ)^p = 1 := by
      rw [← mul_pow]
      norm_num
    exact (one_smul ℂ a).symm.trans
      (congrArg (fun r : ℂ => r • a) hs).symm
  simpa only [oddBracket_apply] using
    quotient_current_leibniz D H h26 hHG hGH
      (parity D H h26 hHG hGH a) b c p q hpa hb

theorem cohomologyCurrent_delta (a b : Cohomology D H h26 hHG hGH) :
    Delta D H h26 hHG hGH (cohomologyCurrent D H h26 hHG hGH a b) =
      -cohomologyCurrent D H h26 hHG hGH
          (Delta D H h26 hHG hGH a) b -
        cohomologyCurrent D H h26 hHG hGH
          (parity D H h26 hHG hGH a) (Delta D H h26 hHG hGH b) := by
  have h0 := Delta_product_defect D H h26 hHG hGH a b
  have h1 := Delta_product_defect D H h26 hHG hGH
    (Delta D H h26 hHG hGH a) b
  have h2 := Delta_product_defect D H h26 hHG hGH
    (parity D H h26 hHG hGH a) (Delta D H h26 hHG hGH b)
  rw [Delta_square D H h26 hHG hGH a] at h1
  rw [Delta_square D H h26 hHG hGH b] at h2
  have h1' : Delta D H h26 hHG hGH
        (product D H h26 hHG hGH (Delta D H h26 hHG hGH a) b) =
      cohomologyCurrent D H h26 hHG hGH (Delta D H h26 hHG hGH a) b +
        product D H h26 hHG hGH
          (parity D H h26 hHG hGH (Delta D H h26 hHG hGH a))
          (Delta D H h26 hHG hGH b) := by
    have h := h1
    simp only [LinearMap.zero_apply, sub_zero] at h
    exact sub_eq_iff_eq_add.mp h
  have h2' : Delta D H h26 hHG hGH
        (product D H h26 hHG hGH (parity D H h26 hHG hGH a)
          (Delta D H h26 hHG hGH b)) =
      cohomologyCurrent D H h26 hHG hGH
          (parity D H h26 hHG hGH a) (Delta D H h26 hHG hGH b) +
        product D H h26 hHG hGH
          (Delta D H h26 hHG hGH (parity D H h26 hHG hGH a))
          (Delta D H h26 hHG hGH b) := by
    have h := h2
    simp only [sub_zero] at h
    exact sub_eq_iff_eq_add.mp h
  have hpa : Delta D H h26 hHG hGH (parity D H h26 hHG hGH a) =
      -parity D H h26 hHG hGH (Delta D H h26 hHG hGH a) := by
    have h := Delta_parity D H h26 hHG hGH a
    have h' := congrArg
      (fun z : Cohomology D H h26 hHG hGH => -z) h
    simpa only [neg_neg] using h'.symm
  rw [← h0]
  simp only [map_sub, LinearMap.sub_apply]
  rw [Delta_square D H h26 hHG hGH (product D H h26 hHG hGH a b), h1', h2', hpa,
    parity_involution]
  simp only [map_zero, LinearMap.zero_apply, map_neg, LinearMap.neg_apply,
    neg_neg]
  abel

end
end D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket
