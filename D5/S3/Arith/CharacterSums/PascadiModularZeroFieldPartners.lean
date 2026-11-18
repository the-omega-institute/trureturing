/- GID: D5/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiModularZeroFieldPartners
   mirror-E: none(waiver:symbolic-field-partner-classification)
   anchors: []
   utility: none
   digest: Formal cubic pencil identities have at most six nondividing field partners. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalCoefficients

/-! # Field geometry of nondividing modular-zero partners

The homogeneous determinant and formal polynomial classification are shared by
both branches of the actual integer partner count. All coefficient fields,
including characteristic two, are retained.
-/

open Polynomial

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

attribute [local instance] Classical.propDecidable

def fieldDet {K : Type*} [CommRing K] (x y : K × K) : K :=
  x.1 * y.2 - x.2 * y.1

theorem fieldDet_zero_scalar {K : Type*} [Field K]
    (b z : K × K) (hb : b.1 ≠ 0 ∨ b.2 ≠ 0)
    (hd : fieldDet b z = 0) :
    ∃ k : K, z.1 = k * b.1 ∧ z.2 = k * b.2 := by
  rcases hb with hb | hb
  · refine ⟨z.1 / b.1, ?_, ?_⟩
    · field_simp
    · have h : b.1 * z.2 = b.2 * z.1 := by
        dsimp [fieldDet] at hd
        linear_combination hd
      field_simp
      linear_combination h
  · refine ⟨z.2 / b.2, ?_, ?_⟩
    · have h : b.1 * z.2 = b.2 * z.1 := by
        dsimp [fieldDet] at hd
        linear_combination hd
      field_simp
      linear_combination -h
    · field_simp

private theorem linear_triple_coeff_three {K : Type*} [CommRing K]
    (x y z : K × K) :
    (PrimeCube.linear x.1 x.2 * PrimeCube.linear y.1 y.2 *
      PrimeCube.linear z.1 z.2).coeff 3 = x.2 * y.2 * z.2 := by
  have hn : PrimeCube.linear x.1 x.2 * PrimeCube.linear y.1 y.2 *
        PrimeCube.linear z.1 z.2 =
      C (x.1 * y.1 * z.1) +
        C (x.1 * y.1 * z.2 + x.1 * y.2 * z.1 + x.2 * y.1 * z.1) * X +
        C (x.1 * y.2 * z.2 + x.2 * y.1 * z.2 + x.2 * y.2 * z.1) * X^2 +
        C (x.2 * y.2 * z.2) * X^3 := by
    simp only [PrimeCube.linear, Polynomial.C_mul, Polynomial.C_add]
    ring
  rw [hn]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

private theorem nondividing_first_factor {K : Type*} [Field K]
    (a b d q z v : K × K) (hα : fieldDet a d ≠ 0)
    (hpoly : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear z.1 z.2 * PrimeCube.linear v.1 v.2 =
      (PrimeCube.linear z.1 z.2 + PrimeCube.linear v.1 v.2 -
        PrimeCube.linear q.1 q.2) *
          PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2) :
    fieldDet a z = 0 ∨ fieldDet a v = 0 := by
  by_cases ha2 : a.2 = 0
  · have ha1 : a.1 ≠ 0 := by
      intro hz
      apply hα
      simp [fieldDet, hz, ha2]
    have hd2 : d.2 ≠ 0 := by
      intro hz
      apply hα
      simp [fieldDet, ha2, hz]
    have h3 := congrArg (fun P : K[X] => P.coeff 3) hpoly
    have hright :
        ((PrimeCube.linear z.1 z.2 + PrimeCube.linear v.1 v.2 -
          PrimeCube.linear q.1 q.2) *
            PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2).coeff 3 = 0 := by
      rw [ha2]
      have hn : (PrimeCube.linear z.1 z.2 + PrimeCube.linear v.1 v.2 -
            PrimeCube.linear q.1 q.2) * PrimeCube.linear a.1 0 *
            PrimeCube.linear b.1 b.2 =
          C ((z.1 + v.1 - q.1) * a.1 * b.1) +
            C ((z.1 + v.1 - q.1) * a.1 * b.2 +
              (z.2 + v.2 - q.2) * a.1 * b.1) * X +
            C ((z.2 + v.2 - q.2) * a.1 * b.2) * X^2 := by
        simp [PrimeCube.linear, Polynomial.C_mul, Polynomial.C_add,
          Polynomial.C_sub]
        ring
      rw [hn]
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
      norm_num
    rw [linear_triple_coeff_three, hright] at h3
    have hprod : z.2 * v.2 = 0 := by
      rw [mul_assoc] at h3
      exact (mul_eq_zero.mp h3).resolve_left hd2
    rcases mul_eq_zero.mp hprod with hz | hv
    · left
      simp [fieldDet, ha2, hz]
    · right
      simp [fieldDet, ha2, hv]
  · let t : K := -a.1 / a.2
    have ha : a.1 + a.2 * t = 0 := by
      dsimp [t]
      field_simp
      ring
    have hd : d.1 + d.2 * t ≠ 0 := by
      intro hz
      apply hα
      dsimp [fieldDet]
      dsimp [t] at hz
      field_simp at hz
      linear_combination -hz
    have heval := congrArg (fun P : K[X] => P.eval t) hpoly
    simp only [eval_mul, eval_sub, eval_add, PrimeCube.linear,
      eval_C, eval_X, eval_mul] at heval
    rw [ha] at heval
    simp only [mul_zero, zero_mul] at heval
    have hprod : (z.1 + z.2 * t) * (v.1 + v.2 * t) = 0 := by
      rw [mul_assoc] at heval
      exact (mul_eq_zero.mp heval).resolve_left hd
    rcases mul_eq_zero.mp hprod with hz | hv
    · left
      have h := congrArg (fun x : K => a.2 * x) hz
      dsimp [t] at h
      field_simp at h
      dsimp [fieldDet]
      linear_combination -h
    · right
      have h := congrArg (fun x : K => a.2 * x) hv
      dsimp [t] at h
      field_simp at h
      dsimp [fieldDet]
      linear_combination -h

private theorem linear_eq_zero_iff {K : Type*} [Field K] (z : K × K) :
    PrimeCube.linear z.1 z.2 = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have h0 := congrArg (fun P : K[X] => P.coeff 0) hz
    have h1 := congrArg (fun P : K[X] => P.coeff 1) hz
    simp [PrimeCube.linear] at h0 h1
    exact Prod.ext h0 h1
  · intro hz
    subst z
    simp [PrimeCube.linear]

private theorem linear_injective {K : Type*} [Field K] (z v : K × K)
    (h : PrimeCube.linear z.1 z.2 = PrimeCube.linear v.1 v.2) : z = v := by
  have h0 := congrArg (fun P : K[X] => P.coeff 0) h
  have h1 := congrArg (fun P : K[X] => P.coeff 1) h
  simp [PrimeCube.linear] at h0 h1
  exact Prod.ext h0 h1

private theorem nondividing_second_factor {K : Type*} [Field K]
    (b d r v : K × K) (k : K) (hk : k ≠ 0)
    (hβ : fieldDet d b ≠ 0)
    (hpoly : C k * PrimeCube.linear d.1 d.2 * PrimeCube.linear v.1 v.2 =
      PrimeCube.linear r.1 r.2 * PrimeCube.linear b.1 b.2) :
    fieldDet b v = 0 := by
  by_cases hb2 : b.2 = 0
  · have hb1 : b.1 ≠ 0 := by
      intro hz
      apply hβ
      simp [fieldDet, hz, hb2]
    have hd2 : d.2 ≠ 0 := by
      intro hz
      apply hβ
      simp [fieldDet, hb2, hz]
    have h2 := congrArg (fun P : K[X] => P.coeff 2) hpoly
    have hl : (C k * PrimeCube.linear d.1 d.2 *
        PrimeCube.linear v.1 v.2).coeff 2 = k * d.2 * v.2 := by
      have hn : C k * PrimeCube.linear d.1 d.2 * PrimeCube.linear v.1 v.2 =
          C (k * d.1 * v.1) +
          C (k * (d.1 * v.2 + d.2 * v.1)) * X +
          C (k * d.2 * v.2) * X^2 := by
        simp [PrimeCube.linear, Polynomial.C_mul, Polynomial.C_add]
        ring
      rw [hn]
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
      norm_num
    have hr : (PrimeCube.linear r.1 r.2 *
        PrimeCube.linear b.1 b.2).coeff 2 = 0 := by
      rw [hb2]
      have hn : PrimeCube.linear r.1 r.2 * PrimeCube.linear b.1 0 =
          C (r.1 * b.1) + C (r.2 * b.1) * X := by
        simp [PrimeCube.linear, Polynomial.C_mul, Polynomial.C_add]
        ring
      rw [hn]
      simp [coeff_add, coeff_C_mul_X, coeff_C]
    rw [hl, hr] at h2
    have hv2 : v.2 = 0 := by
      rw [mul_assoc] at h2
      exact (mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hk)).resolve_left hd2
    simp [fieldDet, hb2, hv2]
  · let t : K := -b.1 / b.2
    have hb : b.1 + b.2 * t = 0 := by
      dsimp [t]
      field_simp
      ring
    have hd : d.1 + d.2 * t ≠ 0 := by
      intro hz
      apply hβ
      dsimp [fieldDet]
      dsimp [t] at hz
      field_simp at hz
      linear_combination hz
    have heval := congrArg (fun P : K[X] => P.eval t) hpoly
    simp only [eval_mul, eval_C, eval_add, eval_X, PrimeCube.linear] at heval
    rw [hb] at heval
    simp only [mul_zero] at heval
    have hv : v.1 + v.2 * t = 0 := by
      rw [mul_assoc] at heval
      exact (mul_eq_zero.mp ((mul_eq_zero.mp heval).resolve_left hk)).resolve_left hd
    have h := congrArg (fun x : K => b.2 * x) hv
    dsimp [t] at h
    field_simp at h
    dsimp [fieldDet]
    linear_combination -h

private theorem nondividing_oriented_vectors {K : Type*} [Field K]
    (a b d q v : K × K) (k : K) (hk : k ≠ 0)
    (hα : fieldDet a d ≠ 0) (hβ : fieldDet d b ≠ 0)
    (hpoly : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear (k * a.1) (k * a.2) *
          PrimeCube.linear v.1 v.2 =
      (PrimeCube.linear (k * a.1) (k * a.2) +
          PrimeCube.linear v.1 v.2 - PrimeCube.linear q.1 q.2) *
        PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2) :
    ∃ l : K, v = (l * b.1, l * b.2) ∧
      k * l * d.1 = k * a.1 + l * b.1 - q.1 ∧
      k * l * d.2 = k * a.2 + l * b.2 - q.2 := by
  let A := PrimeCube.linear a.1 a.2
  let B := PrimeCube.linear b.1 b.2
  let D := PrimeCube.linear d.1 d.2
  let V := PrimeCube.linear v.1 v.2
  let R := PrimeCube.linear (k * a.1 + v.1 - q.1)
      (k * a.2 + v.2 - q.2)
  have ha : a ≠ 0 := by
    intro hz
    apply hα
    simp [fieldDet, hz]
  have hb : b ≠ 0 := by
    intro hz
    apply hβ
    simp [fieldDet, hz]
  have hA : A ≠ 0 := by
    intro hz
    exact ha ((linear_eq_zero_iff a).mp hz)
  have hB : B ≠ 0 := by
    intro hz
    exact hb ((linear_eq_zero_iff b).mp hz)
  have hred : C k * D * V = R * B := by
    apply mul_left_cancel₀ hA
    convert hpoly using 1 <;>
      simp [A, B, D, V, R, PrimeCube.linear, Polynomial.C_mul,
        Polynomial.C_add, Polynomial.C_sub] <;> ring
  have hdet : fieldDet b v = 0 :=
    nondividing_second_factor b d
      (k * a.1 + v.1 - q.1, k * a.2 + v.2 - q.2)
      v k hk hβ hred
  have hb_nonzero : b.1 ≠ 0 ∨ b.2 ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hb (Prod.ext hn.1 hn.2)
  obtain ⟨l, hv1, hv2⟩ := fieldDet_zero_scalar b v hb_nonzero hdet
  have hv : v = (l * b.1, l * b.2) := Prod.ext hv1 hv2
  have hlin : C (k * l) * D = R := by
    apply mul_left_cancel₀ hB
    convert hred using 1 <;>
      simp [B, D, V, R, hv1, hv2, PrimeCube.linear,
        Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub] <;> ring
  have hvec : (k * l * d.1, k * l * d.2) =
      (k * a.1 + l * b.1 - q.1, k * a.2 + l * b.2 - q.2) := by
    apply linear_injective
    convert hlin using 1 <;>
      simp [D, R, hv1, hv2, PrimeCube.linear,
        Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub] <;> ring
  exact ⟨l, hv, congrArg Prod.fst hvec, congrArg Prod.snd hvec⟩

private theorem nondividing_scalar_candidates {K : Type*} [Field K]
    (a b d q : K × K) (k l : K)
    (hq : q.1 = a.1 + b.1 - d.1 ∧
      q.2 = a.2 + b.2 - d.2)
    (hα : fieldDet a d ≠ 0) (hβ : fieldDet d b ≠ 0)
    (h1 : k * l * d.1 = k * a.1 + l * b.1 - q.1)
    (h2 : k * l * d.2 = k * a.2 + l * b.2 - q.2) :
    (k = 1 ∧ l = 1) ∨
      (k = (fieldDet a b - fieldDet d b) / fieldDet a d ∧
       l = (fieldDet a b - fieldDet a d) / fieldDet d b) := by
  let α := fieldDet a d
  let β := fieldDet d b
  let Δ := fieldDet a b
  have hr1 : (k * l - 1) * d.1 - (k - 1) * a.1 - (l - 1) * b.1 = 0 := by
    linear_combination h1 - hq.1
  have hr2 : (k * l - 1) * d.2 - (k - 1) * a.2 - (l - 1) * b.2 = 0 := by
    linear_combination h2 - hq.2
  have heq1 : β * (l - 1) = α * (k - 1) := by
    dsimp [α, β, fieldDet]
    linear_combination -(d.1 * hr2 - d.2 * hr1)
  have heq2 : β * (k * l - 1) = Δ * (k - 1) := by
    dsimp [β, Δ, fieldDet]
    linear_combination b.2 * hr1 - b.1 * hr2
  have hfactor : (k - 1) * (α * k + β - Δ) = 0 := by
    linear_combination heq2 - k * heq1
  rcases mul_eq_zero.mp hfactor with hk | hk
  · left
    have hk1 : k = 1 := sub_eq_zero.mp hk
    have hl1 : l = 1 := by
      rw [hk1] at heq1
      have hz : β * (l - 1) = 0 := by simpa using heq1
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hβ)
    exact ⟨hk1, hl1⟩
  · right
    have hk' : k = (Δ - β) / α := by
      apply (eq_div_iff hα).2
      linear_combination hk
    have hl' : l = (Δ - α) / β := by
      apply (eq_div_iff hβ).2
      linear_combination heq1 + hk
    exact ⟨hk', hl'⟩

def nondividingLambda {K : Type*} [Field K] (a b d : K × K) : K :=
  (fieldDet a b - fieldDet d b) / fieldDet a d

def nondividingMu {K : Type*} [Field K] (a b d : K × K) : K :=
  (fieldDet a b - fieldDet a d) / fieldDet d b

private theorem nondividing_oriented_cover {K : Type*} [Field K]
    (a b d q z v : K × K)
    (hq : q.1 = a.1 + b.1 - d.1 ∧ q.2 = a.2 + b.2 - d.2)
    (hα : fieldDet a d ≠ 0) (hβ : fieldDet d b ≠ 0)
    (hz0 : z ≠ 0) (hz : fieldDet a z = 0)
    (hpoly : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear z.1 z.2 * PrimeCube.linear v.1 v.2 =
      (PrimeCube.linear z.1 z.2 + PrimeCube.linear v.1 v.2 -
        PrimeCube.linear q.1 q.2) *
          PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2) :
    (z, v) = (a, b) ∨
      (z, v) = ((nondividingLambda a b d * a.1,
        nondividingLambda a b d * a.2),
        (nondividingMu a b d * b.1, nondividingMu a b d * b.2)) := by
  have ha : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hα
    simp [fieldDet, hn.1, hn.2]
  obtain ⟨k, hz1, hz2⟩ := fieldDet_zero_scalar a z ha hz
  have hk : k ≠ 0 := by
    intro hzero
    apply hz0
    exact Prod.ext (by simpa [hzero] using hz1) (by simpa [hzero] using hz2)
  have hp : PrimeCube.linear d.1 d.2 *
      PrimeCube.linear (k * a.1) (k * a.2) *
        PrimeCube.linear v.1 v.2 =
    (PrimeCube.linear (k * a.1) (k * a.2) +
        PrimeCube.linear v.1 v.2 - PrimeCube.linear q.1 q.2) *
      PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2 := by
    simpa only [hz1, hz2] using hpoly
  obtain ⟨l, hv, heq1, heq2⟩ :=
    nondividing_oriented_vectors a b d q v k hk hα hβ hp
  rcases nondividing_scalar_candidates a b d q k l hq hα hβ heq1 heq2 with
    ⟨hk1, hl1⟩ | ⟨hkAlt, hlAlt⟩
  · left
    apply Prod.ext
    · exact Prod.ext (by simpa [hk1] using hz1) (by simpa [hk1] using hz2)
    · simpa [hl1] using hv
  · right
    apply Prod.ext
    · exact Prod.ext (by simpa [nondividingLambda, hkAlt] using hz1)
        (by simpa [nondividingLambda, hkAlt] using hz2)
    · simpa [nondividingMu, hlAlt] using hv

private theorem nondividing_zero_endpoint {K : Type*} [Field K]
    (a b d q v : K × K)
    (hα : fieldDet a d ≠ 0) (hβ : fieldDet d b ≠ 0)
    (hpoly : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear (0 : K) 0 * PrimeCube.linear v.1 v.2 =
      (PrimeCube.linear (0 : K) 0 + PrimeCube.linear v.1 v.2 -
        PrimeCube.linear q.1 q.2) *
          PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2) :
    v = q := by
  have ha : a ≠ 0 := by
    intro hz
    apply hα
    simp [fieldDet, hz]
  have hb : b ≠ 0 := by
    intro hz
    apply hβ
    simp [fieldDet, hz]
  have hA : PrimeCube.linear a.1 a.2 ≠ 0 := by
    intro hz
    exact ha ((linear_eq_zero_iff a).mp hz)
  have hB : PrimeCube.linear b.1 b.2 ≠ 0 := by
    intro hz
    exact hb ((linear_eq_zero_iff b).mp hz)
  have hzero : (PrimeCube.linear v.1 v.2 - PrimeCube.linear q.1 q.2) *
      PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2 = 0 := by
    simpa [PrimeCube.linear] using hpoly.symm
  have hlin : PrimeCube.linear v.1 v.2 - PrimeCube.linear q.1 q.2 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hB)).resolve_right hA
  exact linear_injective v q (sub_eq_zero.mp hlin)

/-- Every nondividing formal pencil partner lies among six ordered field pairs. -/
theorem nondividing_field_partner_cover {K : Type*} [Field K]
    (a b d q z v : K × K)
    (hq : q.1 = a.1 + b.1 - d.1 ∧ q.2 = a.2 + b.2 - d.2)
    (hα : fieldDet a d ≠ 0) (hβ : fieldDet d b ≠ 0)
    (hpoly : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear z.1 z.2 * PrimeCube.linear v.1 v.2 =
      (PrimeCube.linear z.1 z.2 + PrimeCube.linear v.1 v.2 -
        PrimeCube.linear q.1 q.2) *
          PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2) :
    (z, v) = (0, q) ∨ (z, v) = (q, 0) ∨
    (z, v) = (a, b) ∨ (z, v) = (b, a) ∨
    (z, v) = ((nondividingLambda a b d * a.1,
      nondividingLambda a b d * a.2),
      (nondividingMu a b d * b.1, nondividingMu a b d * b.2)) ∨
    (z, v) = ((nondividingMu a b d * b.1,
      nondividingMu a b d * b.2),
      (nondividingLambda a b d * a.1,
        nondividingLambda a b d * a.2)) := by
  by_cases hz0 : z = 0
  · left
    subst z
    exact congrArg (fun w : K × K => ((0, 0), w))
      (nondividing_zero_endpoint a b d q v hα hβ hpoly)
  by_cases hv0 : v = 0
  · right; left
    subst v
    have hs : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear (0 : K) 0 * PrimeCube.linear z.1 z.2 =
      (PrimeCube.linear (0 : K) 0 + PrimeCube.linear z.1 z.2 -
        PrimeCube.linear q.1 q.2) *
          PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2 := by
      simpa [PrimeCube.linear] using hpoly
    exact congrArg (fun w : K × K => (w, (0, 0)))
      (nondividing_zero_endpoint a b d q z hα hβ hs)
  rcases nondividing_first_factor a b d q z v hα hpoly with hz | hv
  · rcases nondividing_oriented_cover a b d q z v hq hα hβ hz0 hz hpoly with
      h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · have hs : PrimeCube.linear d.1 d.2 *
        PrimeCube.linear v.1 v.2 * PrimeCube.linear z.1 z.2 =
      (PrimeCube.linear v.1 v.2 + PrimeCube.linear z.1 z.2 -
        PrimeCube.linear q.1 q.2) *
          PrimeCube.linear a.1 a.2 * PrimeCube.linear b.1 b.2 := by
      convert hpoly using 1 <;> ring
    rcases nondividing_oriented_cover a b d q v z hq hα hβ hv0 hv hs with
      h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg Prod.swap h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (congrArg Prod.swap h)))))

end
end D5.S3.Arith.CharacterSums.Original
