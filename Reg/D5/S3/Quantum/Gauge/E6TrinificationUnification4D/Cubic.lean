import Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Common

/-! Typed source observations and whole-family interventions. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.E6TrinificationUnification4D
open _root_.Reg.Support.SingleDependentReadout (signature)
open LeanInformationAudit
open scoped BigOperators InnerProductSpace

namespace Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Cubic
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section


abbrev invariantSignature : Signature := signature (Σ _ : TrinifMatrix, TrinifMatrix) (fun _ => TrinifMatrix) (fun _ => ℂ)

abbrev invariantArena : Arena where
  signature := invariantSignature
  Law R := ∀ (Q L Qc a b c : TrinifMatrix)
    (ha : a.det = 1) (hb : b.det = 1) (hc : c.det = 1),
    freudenthalCubic (a * Q * b⁻¹) (b * L * c⁻¹) (c * Qc * a⁻¹) =
      R.readout () ⟨Q, L⟩ Qc

def invariantFamily : Registration invariantArena (type_of% (@freudenthalCubic_sl3_cubed_invariant)) :=
  e6Family% invariantArena (@freudenthalCubic_sl3_cubed_invariant) (realize invariantSignature (fun _ p Qc => freudenthalCubic p.1 p.2 Qc) (fun e => nomatch e))
    (by
      refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
      norm_num [realize, freudenthalCubic, OmegaMath.CyclicMatrixCubic.cubic])
    (realize invariantSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      have hh := h 1 0 0 1 1 1 (by simp) (by simp) (by simp)
      norm_num [realize, freudenthalCubic, OmegaMath.CyclicMatrixCubic.cubic] at hh)

def invariantRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@freudenthalCubic_sl3_cubed_invariant) (Realization invariantSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.freudenthalCubic_sl3_cubed_invariant.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Cubic.invariantFamily
    invariantArena invariantFamily (realize invariantSignature (fun _ p Qc => freudenthalCubic p.1 p.2 Qc) (fun e => nomatch e))
    #[0, 1] (e6Path% freudenthalCubic_sl3_cubed_invariant freudenthalCubic 3 1) 2 false none

abbrev cyclicSignature : Signature := signature (Σ _ : TrinifMatrix, TrinifMatrix) (fun _ => TrinifMatrix) (fun _ => ℂ)

abbrev cyclicArena : Arena where
  signature := cyclicSignature
  Law R := ∀ (Q L Qc : TrinifMatrix),
    freudenthalCubic L Qc Q = R.readout () ⟨Q, L⟩ Qc

def cyclicFamily : Registration cyclicArena (type_of% (@freudenthalCubic_z3_cyclic_invariant)) :=
  e6Family% cyclicArena (@freudenthalCubic_z3_cyclic_invariant) (realize cyclicSignature (fun _ p Qc => freudenthalCubic p.1 p.2 Qc) (fun e => nomatch e))
    (by
      refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
      norm_num [realize, freudenthalCubic, OmegaMath.CyclicMatrixCubic.cubic])
    (realize cyclicSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      have hh := h 1 0 0
      norm_num [realize, freudenthalCubic, OmegaMath.CyclicMatrixCubic.cubic, Fin.sum_univ_three] at hh)

def cyclicRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@freudenthalCubic_z3_cyclic_invariant) (Realization cyclicSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.freudenthalCubic_z3_cyclic_invariant.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Cubic.cyclicFamily
    cyclicArena cyclicFamily (realize cyclicSignature (fun _ p Qc => freudenthalCubic p.1 p.2 Qc) (fun e => nomatch e))
    #[0, 1] (e6Path% freudenthalCubic_z3_cyclic_invariant freudenthalCubic 3 1) 2 false none

abbrev homogeneitySignature : Signature := signature (Σ _ : TrinifMatrix, TrinifMatrix) (fun _ => TrinifMatrix) (fun _ => ℂ)

abbrev homogeneityArena : Arena where
  signature := homogeneitySignature
  Law R := ∀ (z : ℂ) (Q L Qc : TrinifMatrix),
    freudenthalCubic (z • Q) (z • L) (z • Qc) = z ^ 3 * R.readout () ⟨Q, L⟩ Qc

def homogeneityFamily : Registration homogeneityArena (type_of% (@freudenthalCubic_homogeneous_degree_3)) :=
  e6Family% homogeneityArena (@freudenthalCubic_homogeneous_degree_3) (realize homogeneitySignature (fun _ p Qc => freudenthalCubic p.1 p.2 Qc) (fun e => nomatch e))
    (by
      refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
      norm_num [realize, freudenthalCubic, OmegaMath.CyclicMatrixCubic.cubic])
    (realize homogeneitySignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      have hh := h 1 1 0 0
      norm_num [realize, freudenthalCubic, OmegaMath.CyclicMatrixCubic.cubic] at hh)

def homogeneityRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@freudenthalCubic_homogeneous_degree_3) (Realization homogeneitySignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.freudenthalCubic_homogeneous_degree_3.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Cubic.homogeneityFamily
    homogeneityArena homogeneityFamily (realize homogeneitySignature (fun _ p Qc => freudenthalCubic p.1 p.2 Qc) (fun e => nomatch e))
    #[1, 2] (e6Path% freudenthalCubic_homogeneous_degree_3 freudenthalCubic 3 1) 3 false none

abbrev yukawaSignature : Signature := signature (Σ _ : TrinifMatrix, TrinifMatrix) (fun _ => TrinifMatrix) (fun _ => ℂ)

abbrev yukawaArena : Arena where
  signature := yukawaSignature
  Law R := ∀ (Q L Qc : TrinifMatrix),
    R.readout () ⟨Q, L⟩ Qc =
      Q.det + Qc.det
      - (∑ i : Fin 3, (Q i 0 * L 0 0 + Q i 1 * L 1 0) * Qc 0 i)
      - (∑ i : Fin 3, (Q i 0 * L 0 1 + Q i 1 * L 1 1) * Qc 1 i)
      - (∑ i : Fin 3, (
        (Q i 0 * L 0 2 + Q i 1 * L 1 2 + Q i 2 * L 2 2) * Qc 2 i +
        Q i 2 * (L 2 0 * Qc 0 i + L 2 1 * Qc 1 i)))
      + (L 0 1 * L 1 2 - L 0 2 * L 1 1) * L 2 0
      + (L 0 2 * L 1 0 - L 0 0 * L 1 2) * L 2 1
      + (L 0 0 * L 1 1 - L 0 1 * L 1 0) * L 2 2

def yukawaFamily : Registration yukawaArena (type_of% (@freudenthalCubic_contains_sm_yukawa)) :=
  e6Family% yukawaArena (@freudenthalCubic_contains_sm_yukawa) (realize yukawaSignature (fun _ p Qc => freudenthalCubic p.1 p.2 Qc) (fun e => nomatch e))
    (by
      refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
      norm_num [realize, freudenthalCubic, OmegaMath.CyclicMatrixCubic.cubic])
    (realize yukawaSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      have hh := h 1 0 0
      norm_num [realize, freudenthalCubic, OmegaMath.CyclicMatrixCubic.cubic, Fin.sum_univ_three] at hh)

def yukawaRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@freudenthalCubic_contains_sm_yukawa) (Realization yukawaSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.freudenthalCubic_contains_sm_yukawa.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Cubic.yukawaFamily
    yukawaArena yukawaFamily (realize yukawaSignature (fun _ p Qc => freudenthalCubic p.1 p.2 Qc) (fun e => nomatch e))
    #[0, 1] (e6Path% freudenthalCubic_contains_sm_yukawa freudenthalCubic 3 0) 2 false none

abbrev equivarianceSignature : Signature := signature TrinifGroup (fun _ => Trinif27) (fun _ => Trinif27)

abbrev equivarianceArena : Arena where
  signature := equivarianceSignature
  Law R := ∀ (g : TrinifGroup) (x : Trinif27),
    R.readout () g x = OmegaMath.CyclicMatrixCubic.rotateGroup g • cyc x ∧
    cyc (cyc (cyc x)) = x

def equivarianceFamily : Registration equivarianceArena (type_of% (@trinif_cyclic_equivariance)) :=
  e6Family% equivarianceArena (@trinif_cyclic_equivariance) (realize equivarianceSignature (fun _ g x => cyc (g • x)) (fun e => nomatch e))
    (by
      refine ⟨1, 0, (1, 0, 0), ?_⟩
      intro h
      have he := congrArg (fun x : Trinif27 => x.2.2 0 0) h
      norm_num [realize, cyc, OmegaMath.CyclicMatrixCubic.rotate] at he)
    (realize equivarianceSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      have hh := (h 1 (1, 0, 0)).1
      have hc := (trinif_cyclic_equivariance 1 (1, 0, 0)).1
      have hz : cyc ((1 : TrinifGroup) • ((1, 0, 0) : Trinif27)) = 0 := hc.trans hh.symm
      have he := congrArg (fun x : Trinif27 => x.2.2 0 0) hz
      norm_num [cyc, OmegaMath.CyclicMatrixCubic.rotate] at he)

def equivarianceRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trinif_cyclic_equivariance) (Realization equivarianceSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.trinif_cyclic_equivariance.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Cubic.equivarianceFamily
    equivarianceArena equivarianceFamily (realize equivarianceSignature (fun _ g x => cyc (g • x)) (fun e => nomatch e))
    #[0] (e6Path% trinif_cyclic_equivariance cyc 1 0) 1 false none

abbrev kernelSignature : Signature := signature TrinifGroup (fun _ => Trinif27) (fun _ => Trinif27)

abbrev kernelArena : Arena where
  signature := kernelSignature
  Law R := ∀ (g : TrinifGroup),
    (∀ x : Trinif27, R.readout () g x = x) ↔
      ∃ z : ℂ, z ^ 3 = 1 ∧ (g.1 : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.scalar (Fin 3) z ∧
        (g.2.1 : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.scalar (Fin 3) z ∧
        (g.2.2 : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.scalar (Fin 3) z

def kernelFamily : Registration kernelArena (type_of% (@trinif_action_kernel)) :=
  e6Family% kernelArena (@trinif_action_kernel) (realize kernelSignature (fun _ g x => g • x) (fun e => nomatch e))
    (by
      refine ⟨1, 0, (1, 0, 0), ?_⟩
      intro h
      have he := congrArg (fun x : Trinif27 => x.1 0 0) h
      norm_num [realize] at he)
    (realize kernelSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      have hid := (trinif_action_kernel 1).mp (fun x => one_smul _ x)
      have hh := (h 1).mpr hid ((1, 0, 0) : Trinif27)
      have he := congrArg (fun x : Trinif27 => x.1 0 0) hh
      norm_num [realize] at he)

def kernelRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trinif_action_kernel) (Realization kernelSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.trinif_action_kernel.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Cubic.kernelFamily
    kernelArena kernelFamily (realize kernelSignature (fun _ g x => g • x) (fun e => nomatch e))
    #[0] (e6Path% trinif_action_kernel HSMul.hSMul 6 0) 1 false none

abbrev cartanAnomalySignature : Signature := signature (Σ _ : Fin 3 → ℝ, Σ _ : Fin 3 → ℝ, Fin 3 → ℝ) (fun _ => OmegaMath.CyclicMatrixCubic.Entry) (fun _ => ℝ)

abbrev cartanAnomalyArena : Arena where
  signature := cartanAnomalySignature
  Law R := ∀ (a b c : Fin 3 → ℝ)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0) (hc : ∑ i, c i = 0),
    (∑ x : OmegaMath.CyclicMatrixCubic.Entry,
      R.readout () ⟨a, b, c⟩ x ^ 3) = 0

def cartanAnomalyFamily : Registration cartanAnomalyArena (type_of% (@trinif_cartan_cubic_anomaly)) :=
  e6Family% cartanAnomalyArena (@trinif_cartan_cubic_anomaly) (realize cartanAnomalySignature (fun _ p x => OmegaMath.CyclicMatrixCubic.differenceWeight p.1 p.2.1 p.2.2 x) (fun e => nomatch e))
    (by
      refine ⟨⟨![1, -1, 0], 0, 0⟩, Sum.inl (0, 0), Sum.inl (1, 0), ?_⟩
      norm_num [realize, OmegaMath.CyclicMatrixCubic.differenceWeight])
    (realize cartanAnomalySignature (fun _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      have hh := h 0 0 0 (by simp) (by simp) (by simp)
      change (∑ _ : OmegaMath.CyclicMatrixCubic.Entry, (1 : ℝ)^3) = 0 at hh
      norm_num [OmegaMath.CyclicMatrixCubic.Entry, Fintype.card_sum] at hh)

def cartanAnomalyRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trinif_cartan_cubic_anomaly) (Realization cartanAnomalySignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.trinif_cartan_cubic_anomaly.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Cubic.cartanAnomalyFamily
    cartanAnomalyArena cartanAnomalyFamily (realize cartanAnomalySignature (fun _ p x => OmegaMath.CyclicMatrixCubic.differenceWeight p.1 p.2.1 p.2.2 x) (fun e => nomatch e))
    #[0, 1, 2] (e6Path% trinif_cartan_cubic_anomaly OmegaMath.CyclicMatrixCubic.differenceWeight 6 0) 6 false none

end
end Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Cubic
