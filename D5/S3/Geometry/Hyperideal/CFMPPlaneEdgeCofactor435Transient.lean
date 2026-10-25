import D5.S3.Geometry.Hyperideal.CFMPPlaneMomentDivergence435Transient
import D5.S3.Geometry.Hyperideal.CFMPNativePullbackBridge435Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix

namespace CFMPPlaneEdgeCofactor435Transient
open CFMPPlaneMomentDivergence435Transient

-- Scalar Gram entries have order 00, 01, 02, 11, 12, 22.
def gram (g : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![g 0,g 1,g 2;g 1,g 3,g 4;g 2,g 4,g 5]

def cofactor (g : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![g 3*g 5-(g 4)^2,g 2*g 4-g 1*g 5,g 1*g 4-g 2*g 3;
     g 2*g 4-g 1*g 5,g 0*g 5-(g 2)^2,g 1*g 2-g 0*g 4;
     g 1*g 4-g 2*g 3,g 1*g 2-g 0*g 4,g 0*g 3-(g 1)^2]

def normalNumerator (g : Fin 6 → ℝ) : Fin 3 → ℝ :=
  ![cofactor g 1 1,cofactor g 2 2,
    cofactor g 0 0+cofactor g 1 1+cofactor g 2 2-
      2*cofactor g 0 1-2*cofactor g 0 2+2*cofactor g 1 2]

theorem cofactor_eq_adjugate (g : Fin 6 → ℝ) : cofactor g = (gram g).adjugate := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cofactor,gram] <;> ring

def normalCovector : Fin 3 → Fin 3 → ℝ :=
  ![![0,-1,0],![0,0,-1],![-1,1,1]]

theorem normalNumerator_eq_adjugate (g : Fin 6 → ℝ) (e : Fin 3) :
    normalNumerator g e =
      dotProduct (normalCovector e) ((gram g).adjugate.mulVec (normalCovector e)) := by
  rw [← cofactor_eq_adjugate]
  fin_cases e <;>
    simp [normalNumerator,normalCovector,cofactor,Matrix.mulVec,dotProduct,
      Fin.sum_univ_three] <;> ring

-- Left edge: (0,r); bottom edge: (r,0); slant edge: (1-r,r).
def edgePoint (e : Fin 3) (r : ℝ) : ℝ × ℝ :=
  ![(0,r),(r,0),(1-r,r)] e

def edgeTangentNorm (g : Fin 6 → ℝ) : Fin 3 → ℝ :=
  ![g 5,g 3,g 3-2*g 4+g 5]

def edgePairing (g : Fin 6 → ℝ) (r : ℝ) : Fin 3 → ℝ :=
  ![g 2+r*g 5,g 1+r*g 3,
    g 2-g 1+(1-r)*(g 4-g 3)+r*(g 5-g 4)]

theorem edge_discriminant (g : Fin 6 → ℝ) (e : Fin 3) (r : ℝ) :
    Q g (edgePoint e r)*edgeTangentNorm g e+(edgePairing g r e)^2 =
      -normalNumerator g e := by
  fin_cases e <;>
    simp [Q,edgePoint,edgeTangentNorm,edgePairing,normalNumerator,cofactor] <;> ring

-- Positivity of this ratio must come from the actual spacelike dual normal.
theorem scalar_edge_speed (C q delta H : ℝ)
    (hC : 0 ≤ C) (hq : 0 < q) (hd : delta ≠ 0)
    (hC2 : C^2 = -delta) (hH : 0 ≤ H/delta) :
    Real.sqrt (-H/q^2) = C*Real.sqrt (H/delta)/q := by
  have hs : (C*Real.sqrt (H/delta)/q)^2 = -H/q^2 := by
    rw [div_pow,mul_pow,Real.sq_sqrt hH,hC2]
    field_simp [hd,hq.ne']
    <;> ring
  rw [← hs]
  exact Real.sqrt_sq (div_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hq.le)

-- The numerator is the evaluation of A against the unnormalized outward dual normal.
theorem scalar_edge_flux (C q Hdelta numerator : ℝ) (hq : q ≠ 0)
    (hH : 0 < Hdelta) :
    numerator/Real.sqrt Hdelta*(C*Real.sqrt Hdelta/q) = C*numerator/q := by
  field_simp [(Real.sqrt_pos.mpr hH).ne',hq]
  <;> ring

open D5.S3.Geometry.Hyperideal.LengthGramBody
open CFMPLorentzLiftSurface435Transient
open CFMPNativePullbackMetric435Transient CFMPNativePullbackBridge435Transient

def pairingEntries (V0 b c : W) : Fin 6 → ℝ :=
  ![lorentz V0 V0,lorentz V0 b,lorentz V0 c,lorentz b b,lorentz b c,lorentz c c]

def rawPoint (V0 b c : W) (e : Fin 3) (r : ℝ) : W :=
  V0+(edgePoint e r).1 • b+(edgePoint e r).2 • c

def rawTangent (b c : W) : Fin 3 → W := ![c,b,c-b]

theorem raw_edge_pairings (V0 b c : W) (e : Fin 3) (r : ℝ) :
    radius (rawPoint V0 b c e r) = Q (pairingEntries V0 b c) (edgePoint e r) ∧
    lorentz (rawTangent b c e) (rawTangent b c e) =
      edgeTangentNorm (pairingEntries V0 b c) e ∧
    lorentz (rawPoint V0 b c e r) (rawTangent b c e) =
      edgePairing (pairingEntries V0 b c) r e := by
  fin_cases e <;> constructor
  all_goals first
    | constructor <;>
        simp [rawPoint,rawTangent,pairingEntries,edgePoint,edgeTangentNorm,edgePairing,
          Q,radius,lorentz,Fin.sum_univ_four,smul_eq_mul] <;> ring
    | (simp [rawPoint,rawTangent,pairingEntries,edgePoint,edgeTangentNorm,edgePairing,
          Q,radius,lorentz,Fin.sum_univ_four,smul_eq_mul] <;> ring)

theorem native_edge_squared_speed (V0 b c : W) (e : Fin 3) (r : ℝ)
    (hq : 0 < radius (rawPoint V0 b c e r))
    (hd : delta (rawPoint V0 b c e r) ≠ 0) :
    let Y := rawPoint V0 b c e r
    let D := rawTangent b c e
    dotProduct ((nativeMatrix Y).mulVec D) ((nativeMatrix Y).mulVec D) /
        (nativeMap Y 2)^2 =
      -normalNumerator (pairingEntries V0 b c) e/(radius Y)^2 := by
  dsimp only
  rw [coordinate_pullback_pairing _ _ _ hq hd]
  obtain ⟨hQ,hD,hYD⟩ := raw_edge_pairings V0 b c e r
  rw [hQ,hD,hYD]
  have hqn : Q (pairingEntries V0 b c) (edgePoint e r) ≠ 0 := by
    rw [← hQ]
    exact hq.ne'
  have hdis := edge_discriminant (pairingEntries V0 b c) e r
  calc
    _ = (Q (pairingEntries V0 b c) (edgePoint e r)*
        edgeTangentNorm (pairingEntries V0 b c) e+
        (edgePairing (pairingEntries V0 b c) r e)^2) /
          (Q (pairingEntries V0 b c) (edgePoint e r))^2 := by
      field_simp [hqn]
      <;> ring
    _ = _ := by rw [hdis]

end CFMPPlaneEdgeCofactor435Transient
