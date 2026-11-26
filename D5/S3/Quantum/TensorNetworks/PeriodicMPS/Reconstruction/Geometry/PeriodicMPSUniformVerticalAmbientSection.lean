/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalAmbientSection
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalAmbientSection
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Coordinate guards for vertical sections. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameChart
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalAmbientAlgebra

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalAmbient

open Matrix PeriodicMPSUniformMovingFrame
open scoped Matrix
open PeriodicMPSUniformSpectralRadicalAlgebra
open PeriodicMPSUniformVerticalSectionRank (transverseKet)
open PeriodicMPSUniformVerticalMiddle (sectionB0 sectionB1)
open PeriodicMPSUniformVerticalSectionRank (DivisorRing divisorRoots genericSection)
open PeriodicMPSUniformVerticalPrimeExclusion (Roots rootSum pairing obstruction)
open private pairedBra from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionTrace
open private sectionBra divisorRoots_eq_zero affine_ne_zero from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionRank
open private sectionKet_trace sectionBra_trace from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameSection
open private trace_scaleCore from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameDivisor


noncomputable section

variable {F : Type*} [CommRing F]

def elementaryA (r s t u : F) : F := r*s + r*t + r*u + s*t + s*u + t*u
def elementaryB (r s t u : F) : F := r*s*t + r*s*u + r*t*u + s*t*u
def elementaryC (r s t u : F) : F := r*s*t*u

def cartesian {E : Type*} [CommRing E] [Algebra ℂ E]
    (d db e eb k : E) : Fin 5 → E :=
  ![(half E) * (d + db), k, (half E) * (e + eb),
    -(imaginary E * half E) * (d - db), -(imaginary E * half E) * (e - eb)]

variable {E : Type*} [Field E] [Algebra ℂ E]

private theorem sectionChart_formula (r s t u p τ : E) :
    let σ := (r+s+(t+u))⁻¹
    let α := σ*(r+s)
    let β := σ*(t+u)
    let q := u+(t-u)*p
    let M := σ^2*(r*(t+u-q)+s*q)
    let R := σ^2*(r*s)
    let S := σ^2*(t*u)
    sectionChart ![r,s,t,u,p] τ =
      cartesian (α*β) (R+S+M) (-τ^2)
        (τ⁻¹^2*(β^2*R+α^2*S-α*β*M)) (τ*(α-β)) := by
  have hA := sectionKet_trace (0 : E)
  have hB : traces (scaleCore (sectionTraceSum ![r,s,t,u,p])⁻¹ (sectionBra ![r,s,t,u,p])) =
      ![(r+s+(t+u))⁻¹*(r+s), (r+s+(t+u))⁻¹*(t+u)] := by
    ext i
    rw [trace_scaleCore, sectionBra_trace]
    fin_cases i <;> rfl
  unfold sectionChart sectionBalancedKetFrame sectionBalancedBraInverse
  rw [hA, hB]
  funext i
  fin_cases i <;>
    simp [-inv_pow, chartOf, cartesian, balance, traceFrame, traceFrameInverse, mix, transverseKet,
      scaleCore, sectionBra, pairedBra, sectionB0, sectionB1, sectionTraceSum, mixedTrace,
      Matrix.det_fin_two, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;>
    ring_nf <;> simp

omit [Algebra ℂ E] in
private theorem section_balance_formula (r s t u p τ : E)
    (h : τ ^ 2 * ((sectionTraceSum ![r,s,t,u,p])⁻¹ *
      sectionImbalance ![r,s,t,u,p]) =
      (sectionTraceSum ![r,s,t,u,p])⁻¹ ^ 3 *
        sectionInitialBraMixedTrace ![r,s,t,u,p]) :
    let σ := (r+s+(t+u))⁻¹
    let α := σ*(r+s)
    let β := σ*(t+u)
    let q := u+(t-u)*p
    let M := σ^2*(r*(t+u-q)+s*q)
    let R := σ^2*(r*s)
    let S := σ^2*(t*u)
    τ^2*(α-β) = β*(α^2-2*R) - α*(β^2-2*S) + (β-α)*(α*β-M) := by
  unfold sectionInitialBraMixedTrace at h
  rw [section_bra_mixedTrace] at h
  simp only [sectionTraceSum, sectionImbalance, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons] at h
  dsimp only
  rw [← mul_sub, h]
  ring

omit [Algebra ℂ E] in
private theorem section_coefficients (α β R S M v : E)
    (hσ : α+β = 1) (hv : v ≠ 0)
    (hbal : v*(α-β) = β*(α^2-2*R) - α*(β^2-2*S) + (β-α)*(α*β-M)) :
    let d := α*β
    let db := R+S+M
    let e := -v
    let eb := v⁻¹*(β^2*R+α^2*S-α*β*M)
    let kk := v*(α-β)^2
    d+db-2*(d*db+e*eb)-kk = R+S+α*β ∧
    d*db-e*eb = β*R+α*S ∧
    (β*R+α*S)^2+kk*(d+eb)*(db+e) = R*S := by
  dsimp only
  have hv' : v * v⁻¹ = 1 := mul_inv_cancel₀ hv
  constructor
  · linear_combination
      -(α-β)*hbal + 2*(β^2*R+α^2*S-α*β*M)*hv' -
        (1+α+β)*M*hσ
  constructor
  · linear_combination (β^2*R+α^2*S-α*β*M)*hv' +
      (β*R+α*S)*hσ
  · have h1 : (α-β)*(R+S+M-v) = R-S := by
      linear_combination -hbal + (R-S)*hσ
    have h2 : (α-β)*(v*(α*β)+(β^2*R+α^2*S-α*β*M)) =
        α^2*S-β^2*R := by
      linear_combination α*β*hbal + (α^2*S-β^2*R)*hσ
    calc
      _ = (β*R+α*S)^2 +
          ((α-β)*(v*(α*β)+(β^2*R+α^2*S-α*β*M))) *
          ((α-β)*(R+S+M-v)) := by
        linear_combination (α-β)^2*(β^2*R+α^2*S-α*β*M)*(R+S+M-v)*hv'
      _ = R*S := by
        rw [h1, h2]
        linear_combination (α+β+1)*R*S*hσ

/-- The literal chart equations for a normalized and balanced section. The
two nonzero pair sums and the affine determinant are exactly the conditions
used to evaluate the inverses of U and k. -/
theorem section_has_coordinateFiber {R : Type*} [CommRing R]
    (g : R →+* E) (two : Rˣ) (h₂ : (two : R) = 2) (a b c : R)
    (r s t u p τ : E) (hτ : τ ≠ 0)
    (hbal : τ ^ 2 * ((sectionTraceSum ![r,s,t,u,p])⁻¹ *
      sectionImbalance ![r,s,t,u,p]) =
      (sectionTraceSum ![r,s,t,u,p])⁻¹ ^ 3 *
        sectionInitialBraMixedTrace ![r,s,t,u,p])
    (hσ : r+s+(t+u) ≠ 0) (hα : r+s ≠ 0) (hβ : t+u ≠ 0)
    (h0 : (r+s)-(t+u) ≠ 0)
    (hdb : r*s + t*u + r*(t+u-(u+(t-u)*p)) + s*(u+(t-u)*p) ≠ 0)
    (ha : g a = (r+s+(t+u))⁻¹ ^ 2 * elementaryA r s t u)
    (hb : g b = (r+s+(t+u))⁻¹ ^ 3 * elementaryB r s t u)
    (hc : g c = (r+s+(t+u))⁻¹ ^ 4 * elementaryC r s t u) :
    ∃ U k : Eˣ, ∃ q : CoordinateFiber
        ((chartParameters two h₂ a b c).map (parameterEval g U k)),
      sectionChart ![r,s,t,u,p] τ = cartesian q.d q.db q.e q.eb (k : E) := by
  let σ := (r+s+(t+u))⁻¹
  let α := σ*(r+s)
  let β := σ*(t+u)
  let w := u+(t-u)*p
  let M := σ^2*(r*(t+u-w)+s*w)
  let P := σ^2*(r*s)
  let Q := σ^2*(t*u)
  let v := τ^2
  let d := α*β
  let db := P+Q+M
  let e := -v
  let eb := τ⁻¹^2*(β^2*P+α^2*Q-α*β*M)
  have hσ' : σ ≠ 0 := inv_ne_zero hσ
  have hsum : α+β=1 := by
    change σ*(r+s)+σ*(t+u)=1
    rw [← mul_add, inv_mul_cancel₀ hσ]
  have hdb' : db ≠ 0 := by
    have he : db = σ^2*(r*s + t*u + r*(t+u-w) + s*w) := by
      dsimp [db, P, Q, M]
      ring
    exact he ▸ mul_ne_zero (pow_ne_zero 2 hσ') hdb
  let U := Units.mk0 (d*db) (mul_ne_zero
    (mul_ne_zero (mul_ne_zero hσ' hα) (mul_ne_zero hσ' hβ)) hdb')
  let k := Units.mk0 (τ*(α-β)) (mul_ne_zero hτ (by
    change σ*(r+s) - σ*(t+u) ≠ 0
    rw [← mul_sub]
    exact mul_ne_zero hσ' h0))
  have hv : v ≠ 0 := pow_ne_zero 2 hτ
  obtain ⟨hA, hB, hC⟩ := section_coefficients α β P Q M v hsum hv
    (section_balance_formula r s t u p τ hbal)
  have hA' : P+Q+α*β = g a := by rw [ha]; dsimp [P, Q, α, β, elementaryA]; ring
  have hB' : β*P+α*Q = g b := by rw [hb]; dsimp [P, Q, α, β, elementaryB]; ring
  have hC' : P*Q = g c := by rw [hc]; dsimp [P, Q, elementaryC]; ring
  have hk : (k : E)^2 = v*(α-β)^2 := mul_pow _ _ _
  have heb : eb = v⁻¹*(β^2*P+α^2*Q-α*β*M) := by simp [eb, v, inv_pow]
  refine ⟨U, k, ⟨d, db, e, eb, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [-parameterU_val, Parameters.map, chartParameters, U]
  · simpa [-parameterU_val, -parameterK_val, Parameters.map, chartParameters, heb, hk,
      d, db, e, U] using hA.trans hA'
  · simpa [-parameterU_val, Parameters.map, chartParameters, heb, d, db, e, U] using
      hB.trans hB'
  · rw [show ((chartParameters two h₂ a b c).map (parameterEval g U k)).b = g b by
        simp [Parameters.map, chartParameters],
      show ((chartParameters two h₂ a b c).map (parameterEval g U k)).c = g c by
        simp [Parameters.map, chartParameters],
      ← hB', show (↑(((chartParameters two h₂ a b c).map (parameterEval g U k)).k) : E) =
        (k : E) by simp [-parameterK_val, Parameters.map, chartParameters],
      hk, heb]
    exact hC.trans hC'
  · exact sectionChart_formula r s t u p τ

open private imbalance from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalPrimeExclusion

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The open conditions for the two independent chart coordinates hold at
every unobstructed generic section. The last entry is the unscaled
determinant of the first aligned bra core. -/
theorem genericSection_coordinate_guards {f : Roots} [IsDomain (DivisorRing f)]
    (m : ℕ) (j : Fin 3) (hj : ¬ f ∣ obstruction m j) :
    let x := sectionFieldMap f ∘ genericSection (divisorRoots f) j
    let r := x 0
    let s := x 1
    let t := x 2
    let u := x 3
    let w := u+(t-u)*x 4
    r+s ≠ 0 ∧ t+u ≠ 0 ∧ (r+s)-(t+u) ≠ 0 ∧
      r*s+t*u+r*(t+u-w)+s*w ≠ 0 := by
  let φ := divisorRoots f
  let r := φ (MvPolynomial.X (pairing j 0))
  let s := φ (MvPolynomial.X (pairing j 1))
  let t := φ (MvPolynomial.X (pairing j 2))
  let u := φ (MvPolynomial.X (pairing j 3))
  have ho : (r+s)*(t+u)*((r+s)-(t+u))*(r^m-s^m)*(t^m-u^m) ≠ 0 := by
    have h : φ (obstruction m j) ≠ 0 := fun hz => hj ((divisorRoots_eq_zero f _).mp hz)
    simpa only [obstruction, imbalance, map_mul, map_add, map_sub, map_pow] using h
  obtain ⟨⟨⟨⟨hα, hβ⟩, h₀⟩, hrs⟩, htu⟩ :=
    mul_ne_zero_iff.mp ho |>.imp_left fun h =>
      (mul_ne_zero_iff.mp h).imp_left fun h =>
        (mul_ne_zero_iff.mp h).imp_left fun h => mul_ne_zero_iff.mp h
  let σ := sectionFieldMap f
  let C := Polynomial.C (R := FractionRing (DivisorRing f))
  have hσ (a : FractionRing (DivisorRing f)) (ha : a ≠ 0) : σ (C a) ≠ 0 :=
    (map_eq_zero_iff σ (sectionFieldMap_injective f)).not.mpr (Polynomial.C_ne_zero.mpr ha)
  let w := C u + (C t - C u) * Polynomial.X
  have hw : C r * C s + C t * C u + C r * (C t + C u - w) + C s * w ≠ 0 := by
    have he : C r * C s + C t * C u + C r * (C t + C u - w) + C s * w =
        C ((s-r)*(t-u))*Polynomial.X + C (r*s+t*u+r*t+s*u) := by
      simp only [w, map_mul, map_add, map_sub, C]
      ring
    rw [he]
    exact affine_ne_zero (mul_ne_zero
      (sub_ne_zero.mpr fun h => hrs (by rw [h, sub_self]))
      (sub_ne_zero.mpr fun h => htu (by rw [h, sub_self])))
  change σ (C r)+σ (C s) ≠ 0 ∧ σ (C t)+σ (C u) ≠ 0 ∧
    (σ (C r)+σ (C s))-(σ (C t)+σ (C u)) ≠ 0 ∧ _
  let z := σ (C u)+(σ (C t)-σ (C u))*σ Polynomial.X
  change _ ∧ _ ∧ _ ∧
    σ (C r)*σ (C s)+σ (C t)*σ (C u)+σ (C r)*(σ (C t)+σ (C u)-z)+σ (C s)*z ≠ 0
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_add] using hσ (r+s) hα
  · simpa only [map_add] using hσ (t+u) hβ
  · simpa only [map_add, map_sub] using hσ ((r+s)-(t+u)) h₀
  · simpa only [map_add, map_mul, map_sub, w, z] using
      (map_eq_zero_iff σ (sectionFieldMap_injective f)).not.mpr hw

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalAmbient
