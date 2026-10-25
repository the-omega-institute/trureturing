import D5.S3.Geometry.Hyperideal.CFMPPlaneDualConormal435Transient
import CFMPPairedSupportConormal230Transient
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open CFMPReflectedCoefficientSection435Transient
open CFMPPlaneEdgeCofactor435Transient CFMPPlaneDualConormal435Transient
open CFMPPairedSupportConormal230Transient

namespace CFMPConormalIdentification231Transient

abbrev Space := Fin 4 → ℝ
abbrev Three := Fin 3 → ℝ

def faceMap (V0 b c : Space) : Three →ₗ[ℝ] Space where
  toFun := basisPoint V0 b c
  map_add' x y := by
    ext i
    simp [basisPoint, smul_eq_mul]
    ring
  map_smul' r x := by
    ext i
    simp [basisPoint, smul_eq_mul]
    ring

theorem readout_expand (V0 b c Q : Space) (x : Three) :
    lorentz (basisPoint V0 b c x) Q =
      x 0 * lorentz V0 Q + x 1 * lorentz b Q + x 2 * lorentz c Q := by
  simp [basisPoint, lorentz, Fin.sum_univ_four, smul_eq_mul]
  ring

theorem faceMap_injective (V0 b c : Space)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0) :
    Function.Injective (faceMap V0 b c) := by
  intro x y hxy
  apply Matrix.mulVec_injective_of_det_ne_zero hG
  ext i
  change basisPoint V0 b c x = basisPoint V0 b c y at hxy
  have h := congrArg (fun Q => lorentz (basisPoint V0 b c (Pi.single i 1)) Q) hxy
  simpa only [basis_pairing, single_one_dotProduct] using h

-- A nondegenerate three-vector face frame fills the kernel of its unit normal.
theorem face_span (V0 b c N : Space)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0)
    (hN : lorentz N N = 1)
    (h0 : lorentz V0 N = 0) (hb : lorentz b N = 0) (hc : lorentz c N = 0)
    (Q : Space) (hQ : lorentz Q N = 0) :
    ∃ x : Three, basisPoint V0 b c x = Q := by
  have hne : pairing N ≠ 0 := by
    intro hz
    have h := congrArg (fun f : Space →ₗ[ℝ] ℝ => f N) hz
    simpa [pairing_apply, hN] using h
  have hker : Module.finrank ℝ (LinearMap.ker (pairing N)) = 3 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hne
    norm_num [Coeff] at h
    omega
  have hrange : Module.finrank ℝ (LinearMap.range (faceMap V0 b c)) = 3 := by
    simpa [Three] using LinearMap.finrank_range_of_inj (faceMap_injective V0 b c hG)
  have hle : LinearMap.range (faceMap V0 b c) ≤ LinearMap.ker (pairing N) := by
    rintro Q ⟨x, rfl⟩
    change pairing N (faceMap V0 b c x) = 0
    rw [pairing_apply]
    change lorentz N (basisPoint V0 b c x) = 0
    rw [lorentz_symm, readout_expand, h0, hb, hc]
    ring
  have heq := Submodule.eq_of_le_of_finrank_eq hle (hrange.trans hker.symm)
  have hmem : Q ∈ LinearMap.ker (pairing N) := by
    change pairing N Q = 0
    rw [pairing_apply, lorentz_symm]
    exact hQ
  rw [← heq] at hmem
  exact hmem

theorem face_readout_ext (V0 b c N Q R : Space)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0)
    (hN : lorentz N N = 1)
    (h0 : lorentz V0 N = 0) (hb : lorentz b N = 0) (hc : lorentz c N = 0)
    (hQ : lorentz Q N = 0) (hR : lorentz R N = 0)
    (hread : ∀ x : Three,
      lorentz (basisPoint V0 b c x) Q = lorentz (basisPoint V0 b c x) R) : Q = R := by
  obtain ⟨x, hx⟩ := face_span V0 b c N hG hN h0 hb hc Q hQ
  obtain ⟨y, hy⟩ := face_span V0 b c N hG hN h0 hb hc R hR
  have hxy : x = y := by
    apply Matrix.mulVec_injective_of_det_ne_zero hG
    ext i
    have h := hread (Pi.single i 1)
    rw [← hx, ← hy, basis_pairing, basis_pairing,
      single_one_dotProduct, single_one_dotProduct] at h
    exact h
  rw [← hx, ← hy, hxy]

def normalize (Q : Space) : Space := (Real.sqrt (lorentz Q Q))⁻¹ • Q

theorem normalize_positive_smul (Q : Space) (r : ℝ) (hr : 0 < r) :
    normalize (r • Q) = normalize Q := by
  have he : lorentz (r • Q) (r • Q) = r^2 * lorentz Q Q := by
    simp [lorentz, Fin.sum_univ_four, smul_eq_mul]
    ring
  simp only [normalize, he, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le,
    mul_inv_rev, smul_smul]
  simp [mul_assoc, hr.ne']

theorem projected_eq_positive_dual (V0 b c N P : Space) (e : Fin 3) (r : ℝ)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0)
    (hN : lorentz N N = 1)
    (h0 : lorentz V0 N = 0) (hb : lorentz b N = 0) (hc : lorentz c N = 0)
    (hread : ∀ x : Three, lorentz (basisPoint V0 b c x) P =
      r * dotProduct x (normalCovector e)) :
    projected N P = r • dualRaw V0 b c e := by
  have hp : lorentz (projected N P) N = 0 := by
    have he : lorentz (projected N P) N = lorentz P N - lorentz N P * lorentz N N := by
      simp [projected, lorentz, Fin.sum_univ_four, smul_eq_mul]
      ring
    rw [he, hN, lorentz_symm P N]
    ring
  have hd : lorentz (r • dualRaw V0 b c e) N = 0 := by
    unfold dualRaw
    rw [show lorentz (r • basisPoint V0 b c
          ((gram (pairingEntries V0 b c))⁻¹ *ᵥ normalCovector e)) N =
        r * lorentz (basisPoint V0 b c
          ((gram (pairingEntries V0 b c))⁻¹ *ᵥ normalCovector e)) N by
        simp [lorentz, Fin.sum_univ_four, smul_eq_mul]; ring]
    rw [readout_expand, h0, hb, hc]
    ring
  apply face_readout_ext V0 b c N _ _ hG hN h0 hb hc hp hd
  intro x
  have hn : lorentz (basisPoint V0 b c x) N = 0 := by
    rw [readout_expand, h0, hb, hc]
    ring
  have he : lorentz (basisPoint V0 b c x) (projected N P) =
      lorentz (basisPoint V0 b c x) P -
        lorentz N P * lorentz (basisPoint V0 b c x) N := by
    simp [projected, lorentz, Fin.sum_univ_four, smul_eq_mul]
    ring
  have hs : lorentz (basisPoint V0 b c x) (r • dualRaw V0 b c e) =
      r * lorentz (basisPoint V0 b c x) (dualRaw V0 b c e) := by
    simp [lorentz, Fin.sum_univ_four, smul_eq_mul]
    ring
  rw [he, hn, hs, dual_pairing V0 b c hG, hread]
  ring

theorem dualUnit_eq_support_conormal (V0 b c N P : Space) (e : Fin 3) (r : ℝ)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0)
    (hN : lorentz N N = 1) (hP : lorentz P P = 1) (hr : 0 < r)
    (h0 : lorentz V0 N = 0) (hb : lorentz b N = 0) (hc : lorentz c N = 0)
    (hread : ∀ x : Three, lorentz (basisPoint V0 b c x) P =
      r * dotProduct x (normalCovector e)) :
    dualUnit V0 b c e = conormal N P := by
  have hp := projected_eq_positive_dual V0 b c N P e r hG hN h0 hb hc hread
  calc
    _ = normalize (dualRaw V0 b c e) := rfl
    _ = normalize (r • dualRaw V0 b c e) := (normalize_positive_smul _ r hr).symm
    _ = normalize (projected N P) := congrArg normalize hp.symm
    _ = _ := by rw [normalize, projected_norm N P hN hP]; rfl

def triangleVertex (V0 b c : Space) : Fin 3 → Space := ![V0, V0+b, V0+c]
def startIndex : Fin 3 → Fin 3 := ![0, 0, 1]
def endIndex : Fin 3 → Fin 3 := ![2, 1, 2]
def otherIndex : Fin 3 → Fin 3 := ![1, 2, 0]

theorem positive_readout_of_edge_support (V0 b c P : Space) (e : Fin 3)
    (hstart : lorentz (triangleVertex V0 b c (startIndex e)) P = 0)
    (hend : lorentz (triangleVertex V0 b c (endIndex e)) P = 0)
    (hinside : lorentz (triangleVertex V0 b c (otherIndex e)) P < 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : Three,
      lorentz (basisPoint V0 b c x) P = r * dotProduct x (normalCovector e) := by
  refine ⟨-lorentz (triangleVertex V0 b c (otherIndex e)) P, neg_pos.mpr hinside, ?_⟩
  intro x
  rw [readout_expand]
  have hadd (X Y : Space) : lorentz (X+Y) P = lorentz X P + lorentz Y P := by
    simp [lorentz, Fin.sum_univ_four]
    ring
  fin_cases e <;>
    simp [triangleVertex, startIndex, endIndex, otherIndex, normalCovector,
      dotProduct, Fin.sum_univ_three, hadd] at hstart hend ⊢
  · linear_combination (x 0-x 1-x 2)*hstart + x 2*hend
  · linear_combination (x 0-x 2-x 1)*hstart + x 1*hend
  · linear_combination x 1*hstart + x 2*hend

-- This identifies the existing inverse-Gram dualUnit, including its outward sign.
-- Concrete original faces still have to discharge the endpoint support conditions.
theorem dualUnit_eq_of_edge_support (V0 b c N P : Space) (e : Fin 3)
    (hG : (gram (pairingEntries V0 b c)).det ≠ 0)
    (hN : lorentz N N = 1) (hP : lorentz P P = 1)
    (h0 : lorentz V0 N = 0) (hb : lorentz b N = 0) (hc : lorentz c N = 0)
    (hstart : lorentz (triangleVertex V0 b c (startIndex e)) P = 0)
    (hend : lorentz (triangleVertex V0 b c (endIndex e)) P = 0)
    (hinside : lorentz (triangleVertex V0 b c (otherIndex e)) P < 0) :
    dualUnit V0 b c e = conormal N P := by
  obtain ⟨r, hr, hread⟩ := positive_readout_of_edge_support V0 b c P e hstart hend hinside
  exact dualUnit_eq_support_conormal V0 b c N P e r hG hN hP hr h0 hb hc hread

end CFMPConormalIdentification231Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPConormalIdentification231Transient.face_span,
      ``CFMPConormalIdentification231Transient.positive_readout_of_edge_support,
      ``CFMPConormalIdentification231Transient.dualUnit_eq_of_edge_support] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP231 target absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP231 disallowed axiom {ax} in {name}"
    Lean.logInfo m!"CFMP231 CHECKED {name} axioms={axioms}"

