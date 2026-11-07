/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyOddBracket
   mirror-E: none(waiver:actual-brst-odd-bracket)
   anchors: []
   utility: none
   digest: Actual odd derived-bracket identities on the full lattice BRST quotient. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder

/-! Odd derived-bracket identities for the full critical lattice BRST quotient,
including Delta compatibility and the endomorphism certificate for shifted Jacobi. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
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
    have hz : product D H h26 hHG hGH
        (0 : Cohomology D H h26 hHG hGH) =
        (0 : Module.End ℂ (Cohomology D H h26 hHG hGH)) :=
      (product D H h26 hHG hGH).map_zero
    rw [hz] at h
    change _ - (0 : Cohomology D H h26 hHG hGH) - _ = _ at h
    rw [sub_zero] at h
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
    rw [parity_involution] at h
    have hz : product D H h26 hHG hGH a
        (0 : Cohomology D H h26 hHG hGH) = 0 :=
      (product D H h26 hHG hGH a).map_zero
    rw [hz, sub_zero] at h
    exact sub_eq_iff_eq_add.mp h
  have hpa : Delta D H h26 hHG hGH (parity D H h26 hHG hGH a) =
      -parity D H h26 hHG hGH (Delta D H h26 hHG hGH a) := by
    have h := Delta_parity D H h26 hHG hGH a
    have h' := congrArg
      (fun z : Cohomology D H h26 hHG hGH => -z) h
    exact (neg_neg
      (Delta D H h26 hHG hGH (parity D H h26 hHG hGH a))).symm.trans h'.symm
  have h0d : Delta D H h26 hHG hGH (cohomologyCurrent D H h26 hHG hGH a b) =
      Delta D H h26 hHG hGH
        ((Delta D H h26 hHG hGH (product D H h26 hHG hGH a b) -
          product D H h26 hHG hGH (Delta D H h26 hHG hGH a) b) -
        product D H h26 hHG hGH
          (parity D H h26 hHG hGH a) (Delta D H h26 hHG hGH b)) := by
    exact (congrArg (fun z : Cohomology D H h26 hHG hGH =>
      Delta D H h26 hHG hGH z) h0).symm
  have h1d : Delta D H h26 hHG hGH (product D H h26 hHG hGH
        (Delta D H h26 hHG hGH a) b) =
      cohomologyCurrent D H h26 hHG hGH (Delta D H h26 hHG hGH a) b +
        product D H h26 hHG hGH
          (parity D H h26 hHG hGH (Delta D H h26 hHG hGH a))
          (Delta D H h26 hHG hGH b) := by
    exact h1'
  have h2d : Delta D H h26 hHG hGH (product D H h26 hHG hGH
        (parity D H h26 hHG hGH a) (Delta D H h26 hHG hGH b)) =
      cohomologyCurrent D H h26 hHG hGH
          (parity D H h26 hHG hGH a) (Delta D H h26 hHG hGH b) +
        product D H h26 hHG hGH
          (Delta D H h26 hHG hGH (parity D H h26 hHG hGH a))
          (Delta D H h26 hHG hGH b) := by
    exact h2'
  have hdd : Delta D H h26 hHG hGH
      (Delta D H h26 hHG hGH (product D H h26 hHG hGH a b)) = 0 := by
    exact Delta_square D H h26 hHG hGH (product D H h26 hHG hGH a b)
  let x : Cohomology D H h26 hHG hGH :=
    Delta D H h26 hHG hGH (product D H h26 hHG hGH a b) -
      product D H h26 hHG hGH (Delta D H h26 hHG hGH a) b
  let y : Cohomology D H h26 hHG hGH :=
    product D H h26 hHG hGH
      (parity D H h26 hHG hGH a) (Delta D H h26 hHG hGH b)
  rw [h0d]
  change Delta D H h26 hHG hGH (x - y) = _
  have hdouter : Delta D H h26 hHG hGH (x - y) =
      Delta D H h26 hHG hGH x - Delta D H h26 hHG hGH y :=
    by exact LinearMap.map_sub (Delta D H h26 hHG hGH) x y
  have hdinner : Delta D H h26 hHG hGH
      (Delta D H h26 hHG hGH (product D H h26 hHG hGH a b) -
      product D H h26 hHG hGH (Delta D H h26 hHG hGH a) b) =
      Delta D H h26 hHG hGH
          (Delta D H h26 hHG hGH (product D H h26 hHG hGH a b)) -
        Delta D H h26 hHG hGH
          (product D H h26 hHG hGH (Delta D H h26 hHG hGH a) b) :=
    by
      exact LinearMap.map_sub (Delta D H h26 hHG hGH)
        (Delta D H h26 hHG hGH (product D H h26 hHG hGH a b))
        (product D H h26 hHG hGH (Delta D H h26 hHG hGH a) b)
  rw [hdouter, hdinner]
  rw [hdd, h1d, h2d, hpa]
  simp only [map_zero, LinearMap.zero_apply, map_neg, LinearMap.neg_apply,
    neg_neg]
  abel


theorem Delta_bracket (a b : Cohomology D H h26 hHG hGH) :
    Delta D H h26 hHG hGH (oddBracket D H h26 hHG hGH a b) =
      oddBracket D H h26 hHG hGH (Delta D H h26 hHG hGH a) b -
        oddBracket D H h26 hHG hGH
          (parity D H h26 hHG hGH a) (Delta D H h26 hHG hGH b) := by
  rw [oddBracket_apply, cohomologyCurrent_delta, oddBracket_apply,
    oddBracket_apply, Delta_parity]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

private def leftOperator (a : Cohomology D H h26 hHG hGH) :
    Module.End ℂ (Cohomology D H h26 hHG hGH) :=
  product D H h26 hHG hGH a

private def bracketOperator (a : Cohomology D H h26 hHG hGH) :
    Module.End ℂ (Cohomology D H h26 hHG hGH) :=
  oddBracket D H h26 hHG hGH a

private abbrev L (a : Cohomology D H h26 hHG hGH) :=
  leftOperator D H h26 hHG hGH a

private abbrev T (a : Cohomology D H h26 hHG hGH) :=
  bracketOperator D H h26 hHG hGH a

private theorem bracketOperator_left (a b : Cohomology D H h26 hHG hGH)
    (p q : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ)^p • a)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ)^q • b) :
    T D H h26 hHG hGH a * L D H h26 hHG hGH b -
        (-1 : ℂ)^((p + 1) * q) •
          (L D H h26 hHG hGH b * T D H h26 hHG hGH a) =
      L D H h26 hHG hGH
        (oddBracket D H h26 hHG hGH a b) := by
  apply LinearMap.ext
  intro c
  change oddBracket D H h26 hHG hGH a
      (product D H h26 hHG hGH b c) -
      (-1 : ℂ)^((p + 1) * q) •
        product D H h26 hHG hGH b
          (oddBracket D H h26 hHG hGH a c) =
    product D H h26 hHG hGH
      (oddBracket D H h26 hHG hGH a b) c
  rw [oddBracket_leibniz D H h26 hHG hGH a b c p q ha hb]
  abel

private theorem delta_bracketOperator (a : Cohomology D H h26 hHG hGH)
    (p : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ)^p • a) :
    Delta D H h26 hHG hGH * T D H h26 hHG hGH a -
        (-1 : ℂ)^(p + 1) •
          (T D H h26 hHG hGH a * Delta D H h26 hHG hGH) =
      T D H h26 hHG hGH
        (Delta D H h26 hHG hGH a) := by
  apply LinearMap.ext
  intro c
  change Delta D H h26 hHG hGH
      (oddBracket D H h26 hHG hGH a c) -
      (-1 : ℂ)^(p + 1) •
        oddBracket D H h26 hHG hGH a
          (Delta D H h26 hHG hGH c) =
    oddBracket D H h26 hHG hGH (Delta D H h26 hHG hGH a) c
  rw [Delta_bracket, ha, map_smul]
  simp only [LinearMap.smul_apply, smul_smul, pow_succ, neg_one_smul, smul_neg]
  module

private theorem delta_leftOperator (b : Cohomology D H h26 hHG hGH) (q : ℕ)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ)^q • b) :
    Delta D H h26 hHG hGH * L D H h26 hHG hGH b -
        (-1 : ℂ)^q •
          (L D H h26 hHG hGH b * Delta D H h26 hHG hGH) =
      L D H h26 hHG hGH
        (Delta D H h26 hHG hGH b) +
        (-1 : ℂ)^q • T D H h26 hHG hGH b := by
  apply LinearMap.ext
  intro c
  change Delta D H h26 hHG hGH
      (product D H h26 hHG hGH b c) -
      (-1 : ℂ)^q • product D H h26 hHG hGH b
        (Delta D H h26 hHG hGH c) =
    product D H h26 hHG hGH (Delta D H h26 hHG hGH b) c +
      (-1 : ℂ)^q • oddBracket D H h26 hHG hGH b c
  have h := Delta_product_defect D H h26 hHG hGH b c
  rw [oddBracket_apply, hb, map_smul] at *
  simp only [LinearMap.smul_apply, smul_smul] at *
  have hs : (-1 : ℂ)^q * (-1 : ℂ)^q = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hs, one_smul]
  calc
    Delta D H h26 hHG hGH (product D H h26 hHG hGH b c) -
          (-1 : ℂ)^q • product D H h26 hHG hGH b
            (Delta D H h26 hHG hGH c) =
        (Delta D H h26 hHG hGH (product D H h26 hHG hGH b c) -
            product D H h26 hHG hGH (Delta D H h26 hHG hGH b) c -
          (-1 : ℂ)^q • product D H h26 hHG hGH b
            (Delta D H h26 hHG hGH c)) +
          product D H h26 hHG hGH (Delta D H h26 hHG hGH b) c := by abel
    _ = (cohomologyCurrent D H h26 hHG hGH b c) +
          product D H h26 hHG hGH (Delta D H h26 hHG hGH b) c := by rw [h]
    _ = product D H h26 hHG hGH (Delta D H h26 hHG hGH b) c +
          (cohomologyCurrent D H h26 hHG hGH b c) := by abel

private theorem delta_commutator_identity
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d xa lb : Module.End ℂ V) (r s t : ℂ)
    (hr : r * r = 1) :
    d * (xa * lb - t • (lb * xa)) - (r * s) •
        ((xa * lb - t • (lb * xa)) * d) =
      ((d * xa - r • (xa * d)) * lb - (s * t) •
        (lb * (d * xa - r • (xa * d)))) +
      r • (xa * (d * lb - s • (lb * d)) - (r * t) •
        ((d * lb - s • (lb * d)) * xa)) := by
  simp only [sub_mul, mul_sub, smul_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  have hrt : r * (r * t) = t := by
    rw [← mul_assoc, hr, one_mul]
  have hrts' : r * (r * t * s) = t * s := by
    rw [← mul_assoc r (r * t) s, hrt]
  rw [hrt, hrts']
  have hst' : r * s * t = s * t * r := by ring
  have hts' : t * s = s * t := by ring
  rw [hst', hts']
  noncomm_ring

private theorem bracketOperator_jacobi_operator
    (a b : Cohomology D H h26 hHG hGH) (p q : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ)^p • a)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ)^q • b) :
    T D H h26 hHG hGH a * T D H h26 hHG hGH b -
      (-1 : ℂ)^((p + 1) * (q + 1)) •
        (T D H h26 hHG hGH b * T D H h26 hHG hGH a) =
      T D H h26 hHG hGH
        (oddBracket D H h26 hHG hGH a b) := by
  have hDa := Delta_homogeneous D H h26 hHG hGH a p ha
  have hDb := Delta_homogeneous D H h26 hHG hGH b q hb
  have hBab := oddBracket_homogeneous D H h26 hHG hGH a b p q ha hb
  have hTL := bracketOperator_left D H h26 hHG hGH a b p q ha hb
  have hDTa := delta_bracketOperator D H h26 hHG hGH a p ha
  have hDTaLb := bracketOperator_left D H h26 hHG hGH
    (Delta D H h26 hHG hGH a) b (p + 1) q hDa hb
  have hDLb := delta_leftOperator D H h26 hHG hGH b q hb
  have hXaDLb := bracketOperator_left D H h26 hHG hGH
    a (Delta D H h26 hHG hGH b) p (q + 1) ha hDb
  have hDLa := delta_leftOperator D H h26 hHG hGH
    (oddBracket D H h26 hHG hGH a b) (p + q + 1) hBab
  have hrsq : (-1 : ℂ)^(p + 1) * (-1 : ℂ)^(p + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have hssq : (-1 : ℂ)^q * (-1 : ℂ)^q = 1 := by
    rw [← mul_pow]
    norm_num
  have hrs : (-1 : ℂ)^(p + 1) * (-1 : ℂ)^q =
      (-1 : ℂ)^(p + q + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hst : (-1 : ℂ)^q * (-1 : ℂ)^((p + 1) * q) =
      (-1 : ℂ)^((p + 2) * q) := by
    rw [← pow_add]
    congr 1
    ring
  have hrt : (-1 : ℂ)^(p + 1) * (-1 : ℂ)^((p + 1) * q) =
      (-1 : ℂ)^((p + 1) * (q + 1)) := by
    rw [← pow_add]
    congr 1
    ring
  have hsp : (-1 : ℂ)^p = -(-1 : ℂ)^(p + 1) := by
    rw [pow_succ]
    ring
  have hid := delta_commutator_identity
    (d := Delta D H h26 hHG hGH)
    (xa := bracketOperator D H h26 hHG hGH a)
    (lb := leftOperator D H h26 hHG hGH b)
    (r := (-1 : ℂ)^(p + 1)) (s := (-1 : ℂ)^q)
    (t := (-1 : ℂ)^((p + 1) * q)) hrsq
  rw [hTL, hrs, hDLa, hDTa, hst, hDTaLb, hDLb] at hid
  have hsplit :
      bracketOperator D H h26 hHG hGH a *
          (leftOperator D H h26 hHG hGH (Delta D H h26 hHG hGH b) +
            (-1 : ℂ)^q • bracketOperator D H h26 hHG hGH b) -
        ((-1 : ℂ)^(p + 1) * (-1 : ℂ)^((p + 1) * q)) •
          ((leftOperator D H h26 hHG hGH (Delta D H h26 hHG hGH b) +
            (-1 : ℂ)^q • bracketOperator D H h26 hHG hGH b) *
              bracketOperator D H h26 hHG hGH a) =
      (bracketOperator D H h26 hHG hGH a *
          leftOperator D H h26 hHG hGH (Delta D H h26 hHG hGH b) -
        ((-1 : ℂ)^(p + 1) * (-1 : ℂ)^((p + 1) * q)) •
          (leftOperator D H h26 hHG hGH (Delta D H h26 hHG hGH b) *
            bracketOperator D H h26 hHG hGH a)) +
      (-1 : ℂ)^q •
        (bracketOperator D H h26 hHG hGH a *
            bracketOperator D H h26 hHG hGH b -
          ((-1 : ℂ)^(p + 1) * (-1 : ℂ)^((p + 1) * q)) •
            (bracketOperator D H h26 hHG hGH b *
              bracketOperator D H h26 hHG hGH a)) := by
    simp only [mul_add, add_mul, smul_add, smul_mul_assoc, mul_smul_comm,
      smul_smul]
    module
  rw [hsplit, hrt, hXaDLb] at hid
  have hDParity : Delta D H h26 hHG hGH
      (oddBracket D H h26 hHG hGH a b) =
      oddBracket D H h26 hHG hGH (Delta D H h26 hHG hGH a) b -
        (-1 : ℂ)^p • oddBracket D H h26 hHG hGH a
          (Delta D H h26 hHG hGH b) := by
    rw [Delta_bracket, ha, map_smul]
    simp only [LinearMap.smul_apply]
  have hLDelta :
      L D H h26 hHG hGH
          (Delta D H h26 hHG hGH (oddBracket D H h26 hHG hGH a b)) =
        L D H h26 hHG hGH
            (oddBracket D H h26 hHG hGH (Delta D H h26 hHG hGH a) b) -
          (-1 : ℂ)^p • L D H h26 hHG hGH
            (oddBracket D H h26 hHG hGH a
              (Delta D H h26 hHG hGH b)) := by
    rw [hDParity]
    simp only [leftOperator, map_sub, map_smul, LinearMap.smul_apply]
  rw [hLDelta, hsp] at hid
  apply sub_eq_zero.mp
  have hcancel := congrArg
    (fun z : Module.End ℂ (Cohomology D H h26 hHG hGH) =>
      z - (L D H h26 hHG hGH
          (oddBracket D H h26 hHG hGH
            (Delta D H h26 hHG hGH a) b) +
        (-1 : ℂ)^(p + 1) • L D H h26 hHG hGH
          (oddBracket D H h26 hHG hGH a
            (Delta D H h26 hHG hGH b)))) hid
  simp only [neg_smul, smul_sub, smul_add, smul_smul] at hcancel
  abel_nf at hcancel
  have hbase : (-1 : ℤ) • (1 : ℂ) = -1 := by norm_num
  rw [hbase] at hcancel
  have hleft : (-1 : ℂ)^(p + (1 + q)) =
      (-1 : ℂ)^(p + 1) * (-1 : ℂ)^q := by
    rw [show p + (1 + q) = (p + 1) + q by omega, ← pow_add]
  have hu : (-1 : ℂ)^((p + 1) * (1 + q)) =
      (-1 : ℂ)^((p + 1) * (q + 1)) := by
    congr 1
    ring
  have hrsq' : ((-1 : ℂ)^(p + 1) * (-1 : ℂ)^q) *
      ((-1 : ℂ)^(p + 1) * (-1 : ℂ)^q) = 1 := by
    calc
      ((-1 : ℂ)^(p + 1) * (-1 : ℂ)^q) *
          ((-1 : ℂ)^(p + 1) * (-1 : ℂ)^q) =
        ((-1 : ℂ)^(p + 1) * (-1 : ℂ)^(p + 1)) *
          ((-1 : ℂ)^q * (-1 : ℂ)^q) := by ring
      _ = 1 := by rw [hrsq, hssq]; ring
  have hcoef' :
      ((-1 : ℂ)^(p + 1) * (-1 : ℂ)^q) *
          ((-1 : ℂ)^(p + 1) *
            ((-1 : ℂ)^q * (-1 : ℂ)^((p + 1) * (q + 1)))) =
        (-1 : ℂ)^((p + 1) * (q + 1)) := by
    calc
      ((-1 : ℂ)^(p + 1) * (-1 : ℂ)^q) *
          ((-1 : ℂ)^(p + 1) *
            ((-1 : ℂ)^q * (-1 : ℂ)^((p + 1) * (q + 1)))) =
        ((-1 : ℂ)^(p + 1) * (-1 : ℂ)^(p + 1)) *
          ((-1 : ℂ)^q * (-1 : ℂ)^q) *
            (-1 : ℂ)^((p + 1) * (q + 1)) := by ring
      _ = (-1 : ℂ)^((p + 1) * (q + 1)) := by rw [hrsq, hssq]; ring
  rw [hleft, hu] at hcancel
  have hcancel2 := congrArg
    (fun z : Module.End ℂ (Cohomology D H h26 hHG hGH) =>
      ((-1 : ℂ)^(p + 1) * (-1 : ℂ)^q) • z) hcancel
  simp only [smul_add, smul_sub, smul_smul, hrsq', one_smul,
    neg_smul, smul_neg] at hcancel2
  rw [hcoef'] at hcancel2
  have hEq : T D H h26 hHG hGH (oddBracket D H h26 hHG hGH a b) =
      T D H h26 hHG hGH a * T D H h26 hHG hGH b -
        (-1 : ℂ)^((p + 1) * (q + 1)) •
          (T D H h26 hHG hGH b * T D H h26 hHG hGH a) := by
    simpa only [T, bracketOperator, sub_eq_add_neg, neg_smul, smul_sub,
      smul_smul] using hcancel2
  rw [hEq]
  abel

theorem oddBracket_jacobi (a b c : Cohomology D H h26 hHG hGH) (p q : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ)^p • a)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ)^q • b) :
    oddBracket D H h26 hHG hGH a
        (oddBracket D H h26 hHG hGH b c) =
      oddBracket D H h26 hHG hGH
          (oddBracket D H h26 hHG hGH a b) c +
        (-1 : ℂ)^((p + 1) * (q + 1)) •
          oddBracket D H h26 hHG hGH b
            (oddBracket D H h26 hHG hGH a c) := by
  have h := LinearMap.congr_fun
    (bracketOperator_jacobi_operator D H h26 hHG hGH a b p q ha hb) c
  change oddBracket D H h26 hHG hGH a
      (oddBracket D H h26 hHG hGH b c) -
      (-1 : ℂ)^((p + 1) * (q + 1)) •
        oddBracket D H h26 hHG hGH b
          (oddBracket D H h26 hHG hGH a c) =
    oddBracket D H h26 hHG hGH
      (oddBracket D H h26 hHG hGH a b) c at h
  exact sub_eq_iff_eq_add.mp h


end
end D5.S3.VertexAlgebra.LatticeBRSTCohomologyOddBracket
