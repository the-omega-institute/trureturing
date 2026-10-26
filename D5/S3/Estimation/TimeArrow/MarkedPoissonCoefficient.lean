/- GID: D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/MarkedPoissonCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shared actual-history transfer and signed coefficient extraction control relative masses at exact real means. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
import Mathlib.LinearAlgebra.Matrix.Notation
import D5.S3.Combinatorics.Permanental.CycleGeodesic.CycleGeodesicMidpoint
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Finset MeasureTheory
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open private CycleGeodesic.stirlingError_upper
  CycleGeodesic.stirlingError_formula from
  D5.S3.Combinatorics.Permanental.CycleGeodesic.CycleGeodesicMidpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra

/-- The product of all marked departure-row tilt factors on one edge. -/
def edgeTilt {M k : ℕ} (m : Fin k → Fin M) (zp zm : Fin k → ℂ)
    (x y : Vertex M) : ℂ :=
  ∏ j, (if x = .inl (m j) ∧ chi y = 1 then zp j else 1) *
    (if x = .inl (m j) ∧ chi y = -1 then zm j else 1)

/-- Extend a vector on the marked positive states by zero. -/
def sparse {M k : ℕ} (m : Fin k → Fin M) (a : Fin k → ℂ) (x : Vertex M) : ℂ :=
  ∑ j, if x = .inl (m j) then a j else 0

/-- Natural count powers remain edge products when a tilt is zero. -/
theorem count_monomial {M k s : ℕ} (e : Experiment) (m : Fin k → Fin M)
    (zp zm : Fin k → ℂ) (o : Obs M s e) :
    (∏ j, zp j ^ count e o (m j) 1 * zm j ^ count e o (m j) (-1)) =
      ∏ t : Fin s, edgeTilt m zp zm (edges e o t).1 (edges e o t).2 := by
  have hcount (j : Fin k) :
      zp j ^ count e o (m j) 1 * zm j ^ count e o (m j) (-1) =
      ∏ t : Fin s,
        (if (edges e o t).1 = .inl (m j) ∧ chi (edges e o t).2 = 1 then zp j else 1) *
        (if (edges e o t).1 = .inl (m j) ∧ chi (edges e o t).2 = -1 then zm j else 1) := by
    rw [prod_mul_distrib]
    simp only [prod_ite, prod_const, one_pow, mul_one, count]
  simp_rw [hcount]
  rw [prod_comm]
  rfl

/-- Distinct marks make a marked edge factor affine in the destination parity. -/
theorem edgeTilt_eq_affine {M k : ℕ} (m : Fin k → Fin M) (hm : Function.Injective m)
    (zp zm : Fin k → ℂ) (x y : Vertex M) :
    edgeTilt m zp zm x y =
      1 + sparse m (fun j => (zp j + zm j) / 2 - 1) x +
        sparse m (fun j => (zp j - zm j) / 2) x * (chi y : ℂ) := by
  classical
  let u := fun j => (zp j + zm j) / 2 - 1
  let v := fun j => (zp j - zm j) / 2
  by_cases hx : ∃ j, x = .inl (m j)
  · obtain ⟨j, hj⟩ := hx
    have hother (i : Fin k) (hi : i ≠ j) : x ≠ .inl (m i) := by
      intro he
      exact hi (hm (Sum.inl.inj (hj.symm.trans he)).symm)
    have hU : sparse m u x = u j := by
      dsimp [sparse]
      rw [sum_eq_single j (fun i _ hi => if_neg (hother i hi)) (by simp), if_pos hj]
    have hW : sparse m v x = v j := by
      dsimp [sparse]
      rw [sum_eq_single j (fun i _ hi => if_neg (hother i hi)) (by simp), if_pos hj]
    change edgeTilt m zp zm x y = 1 + sparse m u x + sparse m v x * (chi y : ℂ)
    unfold edgeTilt
    rw [prod_eq_single j (fun i _ hi => by simp [hother i hi]) (by simp), hU, hW]
    cases y <;> norm_num [hj, chi, u, v] <;> ring
  · have hnone (j : Fin k) : x ≠ .inl (m j) := fun hj => hx ⟨j, hj⟩
    simp [edgeTilt, sparse, hnone]

/-- A sparse marked extension integrates against any function by its marked values. -/
theorem sparse_sum {M k : ℕ} (m : Fin k → Fin M) (f : Vertex M → ℂ) (a : Fin k → ℂ) :
    (∑ x, f x * sparse m a x) = ∑ j, f (.inl (m j)) * a j := by
  classical
  simp only [sparse, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  simp

/-- The endpoint mass of a finite weighted path, with a fixed constant initial mass. -/
def endpointWeight {X : Type*} [Fintype X] (c : ℂ) (K : X → X → ℂ)
    (n : ℕ) (y : X) : ℂ := by
  classical
  exact c * ∑ o : Fin (n + 1) → X,
    if o (Fin.last n) = y then ∏ t : Fin n, K (o t.castSucc) (o t.succ) else 0

/-- A path with no edges has its prescribed initial mass at each state. -/
theorem endpoint_zero {X : Type*} [Fintype X] (c : ℂ) (K : X → X → ℂ) (y : X) :
    endpointWeight c K 0 y = c := by
  classical
  dsimp [endpointWeight]
  rw [sum_eq_single (fun _ : Fin 1 => y)]
  · simp
  · intro o _ ho
    have he : o (0 : Fin 1) ≠ y := by
      intro he
      apply ho
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      simpa only [hi] using he
    simp [he]
  · simp

/-- Append the last state of a complete weighted history. -/
theorem endpoint_next {X : Type*} [Fintype X] (c : ℂ) (K : X → X → ℂ)
    (n : ℕ) (y : X) :
    endpointWeight c K (n + 1) y = ∑ x, endpointWeight c K n x * K x y := by
  classical
  dsimp [endpointWeight]
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => X)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.snocEquiv, Equiv.coe_fn_mk,
    Fin.prod_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last]
  rw [sum_comm]
  simp only [sum_ite_eq', mem_univ, if_true]
  symm
  simp_rw [mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro o _
  simp [mul_ite, ite_mul, mul_assoc]

/-- Summing endpoint masses recovers the weighted sum over complete histories. -/
theorem endpoint_total {X : Type*} [Fintype X] (c : ℂ) (K : X → X → ℂ) (n : ℕ) :
    (∑ y, endpointWeight c K n y) = c *
      ∑ o : Fin (n + 1) → X, ∏ t : Fin n, K (o t.castSucc) (o t.succ) := by
  classical
  simp only [endpointWeight, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro o _
  rw [← mul_sum]
  simp

/-- Uniform norm bounds for symmetric and antisymmetric complex row tilts. -/
theorem tilt_norms {k : ℕ} (zp zm : Fin k → ℂ) (R : ℝ)
    (hp : ∀ j, ‖zp j‖ ≤ R) (hm : ∀ j, ‖zm j‖ ≤ R) :
    ∀ j, ‖(zp j + zm j) / 2 - 1‖ ≤ R + 1 ∧ ‖(zp j - zm j) / 2‖ ≤ R := by
  intro j
  constructor
  · calc
      ‖(zp j + zm j) / 2 - 1‖ ≤ ‖(zp j + zm j) / 2‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ R + 1 := by
        rw [norm_div]; norm_num
        have := norm_add_le (zp j) (zm j)
        nlinarith [hp j, hm j]
  · rw [norm_div]; norm_num
    have := norm_sub_le (zp j) (zm j)
    nlinarith [hp j, hm j]

/-- One or two marked rows cost at most twice a common norm bound. -/
theorem marked_sum_norm {k : ℕ} (hk : k = 1 ∨ k = 2) (D : ℝ) (hD : 0 ≤ D)
    (a : Fin k → ℂ) (ha : ∀ j, ‖a j‖ ≤ D) : ‖∑ j, a j‖ ≤ 2 * D := by
  calc
    ‖∑ j, a j‖ ≤ ∑ j, ‖a j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin k, D := sum_le_sum fun j _ => ha j
    _ ≤ 2 * D := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rcases hk with rfl | rfl <;> norm_num <;> linarith

/-- The compensated profile has exactly zero sum. -/
theorem profile_sum_zero {M q : ℕ} {r : ℝ} (hq : 1 ≤ q) (hqm : q < M)
    (hr : 0 < r) (hr1 : r < 1) (hc1 : compensation M q r < 1) (S : Support M q) :
    (∑ x : Vertex M, b r S x) = 0 := by
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hcol := ((finite_support_bayes (s := 0) hq hqm hr hr1 hc hc1 .path).1 S).2
  have hh := hcol (.inl ⟨0, by omega⟩)
  simp only [transition, chi, mul_one, ← sum_div, sum_add_distrib, sum_const,
    card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, mul_one] at hh
  push_cast at hh
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  apply (div_eq_iff (by positivity : (2 * (M : ℝ)) ≠ 0)).mp at hh
  linarith

end D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra


namespace D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope

/-- Half the sum of the two destination tilts, centered at one. -/
def tiltU {k : ℕ} (zp zm : Fin k → ℂ) (j : Fin k) : ℂ := (zp j + zm j)/2-1
/-- Half the difference of the two destination tilts. -/
def tiltV {k : ℕ} (zp zm : Fin k → ℂ) (j : Fin k) : ℂ := (zp j - zm j)/2
/-- The compensated total-mass drift of the marked edge tilt. -/
def driftA {M q k : ℕ} (r : ℝ) (S : Support M q) (m : Fin k → Fin M)
    (zp zm : Fin k → ℂ) : ℂ :=
  (∑ j, (tiltU zp zm j + (b r S (.inl (m j)) : ℂ)*tiltV zp zm j))/(2*M)
/-- The physical endpoint-parity drift of the marked edge tilt. -/
def driftB {M q k : ℕ} (r : ℝ) (S : Support M q) (m : Fin k → Fin M)
    (zp zm : Fin k → ℂ) : ℂ :=
  (∑ j, (tiltV zp zm j + (b r S (.inl (m j)) : ℂ)*tiltU zp zm j))/(2*M)
/-- The finite sum of native complete-history masses times actual departure count powers. -/
def actualPGF {M q k : ℕ} (r : ℝ) (S : Support M q) (m : Fin k → Fin M)
    (zp zm : Fin k → ℂ) (T : ℕ) : ℂ :=
  ∑ o : Obs M T .path, (probability r .path S o : ℂ) *
    ∏ j, (zp j)^count .path o (m j) 1 * (zm j)^count .path o (m j) (-1)

end D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope

open D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
namespace D5.S3.Estimation.TimeArrow.ForwardMarkedPathTransfer

/-- The actual tilted endpoint coefficients evolve as a row vector. -/
def forwardState (A B : ℂ) : ℕ → ℂ × ℂ :=
  fun n => Nat.rec (1, 0) (fun _ f => ((1 + A) * f.1 + A * f.2, B * f.1 + B * f.2)) n

/-- The forward two-coordinate transfer matrix. -/
def forwardMatrix (A B : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1 + A, B; A, B]

/-- Exact uniform-start path PGF and endpoint recurrence, including no steps and zero tilts. -/
theorem actual_marked_path_transfer {M q T k : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (m : Fin k → Fin M) (hm : Function.Injective m) (zp zm : Fin k → ℂ) :
    actualPGF r S m zp zm T = (forwardState (driftA r S m zp zm) (driftB r S m zp zm) T).1 ∧
    actualPGF r S m zp zm T =
      (forwardMatrix (driftA r S m zp zm) (driftB r S m zp zm) ^ T) 0 0 := by
  classical
  have hM : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hMc : (M:ℂ)≠0 := by exact_mod_cast hM.ne'
  have hN : (2*(M:ℂ))≠0 := by exact_mod_cast (ne_of_gt (show (0:ℝ)<2*M by positivity))
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  let u := tiltU zp zm
  let v := tiltV zp zm
  let A := driftA r S m zp zm
  let B := driftB r S m zp zm
  let N : ℂ := 2*M
  let U (x : Vertex M) : ℂ := ∑ j, if x=Sum.inl (m j) then u j else 0
  let W (x : Vertex M) : ℂ := ∑ j, if x=Sum.inl (m j) then v j else 0
  let K (x y : Vertex M) : ℂ := (transition r S x y:ℂ)*(1+U x+W x*(chi y:ℂ))
  have hmass (n : ℕ) (o : Obs M n .path) :
      (probability r .path S o:ℂ)*
        (∏ j, (zp j)^count .path o (m j) 1*(zm j)^count .path o (m j) (-1)) =
      N⁻¹*∏ t : Fin n, K (o t.castSucc) (o t.succ) := by
    rw [D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.count_monomial .path m zp zm o]
    simp_rw [D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.edgeTilt_eq_affine m hm zp zm]
    change (probability r .path S o : ℂ) *
      (∏ t : Fin n, (1 + U (o t.castSucc) + W (o t.castSucc) * (chi (o t.succ) : ℂ))) = _
    simp only [probability, Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_prod,
      Complex.ofReal_natCast,Complex.ofReal_ofNat,prod_mul_distrib,K,N]
    ring
  have hsumbr : ∑ x : Vertex M, b r S x = 0 :=
    D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.profile_sum_zero hq hqm hr hr1 hc1 S
  have hsumb : ∑ x : Vertex M, (b r S x:ℂ) = 0 := by exact_mod_cast hsumbr
  have hsumχ : ∑ x : Vertex M, (chi x:ℂ) = 0 := by
    simp [Fintype.sum_sum_type,chi]
  have hχb (x : Vertex M) : (chi x:ℂ)*(b r S x:ℂ)=(b r S x:ℂ) := by
    cases x <;> simp [chi,b]
  have hχU (x : Vertex M) : (chi x:ℂ)*U x=U x := by
    cases x <;> simp [chi,U]
  have hχW (x : Vertex M) : (chi x:ℂ)*W x=W x := by
    cases x <;> simp [chi,W]
  have hsparse (f : Vertex M → ℂ) (a : Fin k → ℂ) :
      (∑ x, f x * (∑ j, if x = .inl (m j) then a j else 0)) =
      ∑ j, f (.inl (m j)) * a j :=
    D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.sparse_sum m f a
  have hsumU : ∑ x, U x=∑ j, u j := by
    simpa [U] using hsparse (fun _ => 1) u
  have hsumW : ∑ x, W x=∑ j, v j := by
    simpa [W] using hsparse (fun _ => 1) v
  let α (x : Vertex M) : ℂ := 1+U x+(b r S x:ℂ)*W x
  let β (x : Vertex M) : ℂ := (b r S x:ℂ)*(1+U x)+W x
  have hα : ∑ x, α x=N*(1+A) := by
    dsimp [α]
    rw [sum_add_distrib,sum_add_distrib,hsumU,hsparse (fun x => (b r S x:ℂ)) v]
    simp only [sum_const,card_univ,Fintype.card_sum,Fintype.card_fin,nsmul_eq_mul,mul_one]
    dsimp [N,A,driftA,u,v]
    rw [sum_add_distrib]
    push_cast
    field_simp [hN,hMc]
    ring
  have hχα : ∑ x, (chi x:ℂ)*α x=N*A := by
    have he (x : Vertex M) : (chi x:ℂ)*α x=(chi x:ℂ)+U x+(b r S x:ℂ)*W x := by
      dsimp [α]; rw [mul_add,mul_add,mul_one,hχU,← mul_assoc,hχb]
    simp_rw [he]
    rw [sum_add_distrib,sum_add_distrib,hsumχ,hsumU,zero_add,
      hsparse (fun x => (b r S x:ℂ)) v]
    dsimp [N,A,driftA,u,v]
    rw [sum_add_distrib]
    field_simp [hN,hMc]
  have hβ : ∑ x, β x=N*B := by
    have he (x : Vertex M) : β x=(b r S x:ℂ)+(b r S x:ℂ)*U x+W x := by dsimp [β]; ring
    simp_rw [he]
    rw [sum_add_distrib,sum_add_distrib,hsumb,zero_add,
      hsparse (fun x => (b r S x:ℂ)) u,hsumW]
    dsimp [N,B,driftB,u,v]
    rw [sum_add_distrib]
    field_simp [hN,hMc]
    ring
  have hχβ : ∑ x, (chi x:ℂ)*β x=N*B := by
    have he (x : Vertex M) : (chi x:ℂ)*β x=β x := by
      dsimp [β]; rw [mul_add,← mul_assoc,hχb,hχW]
    simpa only [he] using hβ
  have hK (x y : Vertex M) : K x y=(α x+β x*(chi y:ℂ))/N := by
    cases y <;> dsimp [K,transition,α,β,N,chi] <;> push_cast <;>
      field_simp [hMc] <;> ring
  let p (n : ℕ) (y : Vertex M) : ℂ :=
    D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.endpointWeight N⁻¹ K n y
  have hp0 (y : Vertex M) : p 0 y = N⁻¹ :=
    D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.endpoint_zero N⁻¹ K y
  have hpnext (n : ℕ) (y : Vertex M) : p (n + 1) y = ∑ x, p n x * K x y :=
    D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.endpoint_next N⁻¹ K n y
  let R := forwardState A B
  have hR0 : R 0=(1,0) := rfl
  have hRnext (n : ℕ) : R (n+1)=((1+A)*(R n).1+A*(R n).2,B*(R n).1+B*(R n).2) := rfl
  have hpend (n : ℕ) (y : Vertex M) :
      p n y=((R n).1+(chi y:ℂ)*(R n).2)/N := by
    induction n generalizing y with
    | zero => simp [hp0,R,forwardState,div_eq_mul_inv]
    | succ n ih =>
      rw [hpnext]
      simp_rw [ih,hK]
      have hex (x : Vertex M) :
          (((R n).1+(chi x:ℂ)*(R n).2)/N)*((α x+β x*(chi y:ℂ))/N) =
          ((R n).1*α x+(R n).2*((chi x:ℂ)*α x)+
            ((R n).1*β x+(R n).2*((chi x:ℂ)*β x))*(chi y:ℂ))/N^2 := by ring
      simp_rw [hex]
      rw [← sum_div,sum_add_distrib,sum_add_distrib,← sum_mul,sum_add_distrib,
        ← mul_sum,← mul_sum,← mul_sum,← mul_sum,hα,hχα,hβ,hχβ,hRnext]
      field_simp [hN,hMc]
  have htotal (n : ℕ) : actualPGF r S m zp zm n=(R n).1 := by
    have hjoin : actualPGF r S m zp zm n = ∑ y, p n y := by
      calc
        actualPGF r S m zp zm n = N⁻¹ *
            ∑ o : Fin (n + 1) → Vertex M, ∏ t : Fin n, K (o t.castSucc) (o t.succ) := by
          dsimp only [actualPGF]
          simp_rw [hmass]
          rw [mul_sum]
          congr 1
        _ = ∑ y, p n y :=
          (D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.endpoint_total N⁻¹ K n).symm
    rw [hjoin]
    simp_rw [hpend]
    rw [← sum_div,sum_add_distrib,← sum_mul,hsumχ]
    simp only [zero_mul,add_zero,sum_const,card_univ,Fintype.card_sum,
      Fintype.card_fin,nsmul_eq_mul]
    dsimp [N]
    push_cast
    field_simp [hN,hMc]
    ring
  have hmatrix (n : ℕ) :
      (R n).1 = (forwardMatrix A B ^ n) 0 0 ∧
      (R n).2 = (forwardMatrix A B ^ n) 0 1 := by
    induction n with
    | zero => simp [R, forwardState]
    | succ n ih =>
      rw [pow_succ]
      constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, forwardMatrix, hRnext, ih] <;> ring
  exact ⟨htotal T, (htotal T).trans (hmatrix T).1⟩

end D5.S3.Estimation.TimeArrow.ForwardMarkedPathTransfer

namespace D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient

set_option maxHeartbeats 2000000 in
/-- A signed complex envelope controls relative count masses, including zero counts.
The means and observation scale are real and need not have an integral ratio. -/
theorem finite_count_poisson_relative {Ω : Type*} [Fintype Ω] {k : ℕ}
    (κ C₀ L ε : ℝ) (hκ : 0 < κ) (hC : 1 ≤ C₀) (hLr : 1 ≤ L)
    (hε : 0 ≤ ε) (hk : k = 1 ∨ k = 2)
    (w : Ω → ℝ) (cp cm : Ω → Fin k → ℕ) (μp μm : Fin k → ℝ)
    (hμp : ∀ j, 0 < μp j ∧ κ * L / 2 ≤ μp j)
    (hμm : ∀ j, 0 < μm j ∧ κ * L / 2 ≤ μm j)
    (np nm : Fin k → ℕ)
    (hn : ∀ j, (np j : ℝ) ≤ C₀ * L ∧ (nm j : ℝ) ≤ C₀ * L)
    (henv : ∀ zp zm : Fin k → ℂ,
      (∀ j, ‖zp j‖ ≤ 2 * (C₀ + 1) / κ) →
      (∀ j, ‖zm j‖ ≤ 2 * (C₀ + 1) / κ) →
      ‖(∑ o : Ω, (w o : ℂ) * ∏ j, zp j ^ cp o j * zm j ^ cm o j) -
        Complex.exp (∑ j, ((μp j : ℂ) * (zp j - 1) + (μm j : ℂ) * (zm j - 1)))‖ ≤
        ε * Real.exp (∑ j, (μp j * ((zp j).re - 1) + μm j * ((zm j).re - 1)))) :
    let P := ∑ o : Ω, if ∀ j, cp o j = np j ∧ cm o j = nm j then w o else 0
    let Q := ∏ j, (Real.exp (-μp j) * μp j ^ np j / (np j).factorial) *
      (Real.exp (-μm j) * μm j ^ nm j / (nm j).factorial)
    |P / Q - 1| ≤ ε *
      (Real.exp 2 * (Real.sqrt (2 * Real.pi) + 1)) ^ 4 * (C₀ + 1) ^ 2 * L ^ k := by
  classical
  let R : ℝ := 2 * (C₀ + 1) / κ
  let Cs : ℝ := Real.exp 2 * (Real.sqrt (2 * Real.pi) + 1)
  let P : ℝ := ∑ o : Ω, if ∀ j, cp o j = np j ∧ cm o j = nm j then w o else 0
  let Q : ℝ := ∏ j, (Real.exp (-μp j) * μp j ^ np j / (np j).factorial) *
    (Real.exp (-μm j) * μm j ^ nm j / (nm j).factorial)
  let F (zp zm : Fin k → ℂ) : ℂ :=
    ∑ o : Ω, (w o : ℂ) * ∏ j, zp j ^ cp o j * zm j ^ cm o j
  change |P / Q - 1| ≤ ε * Cs ^ 4 * (C₀ + 1) ^ 2 * L ^ k
  have hR : 0 < R := by dsimp [R]; positivity
  have hQ : 0 < Q := by
    dsimp [Q]
    exact prod_pos fun j _ => mul_pos
      (div_pos (mul_pos (Real.exp_pos _) (pow_pos (hμp j).1 _)) (by positivity))
      (div_pos (mul_pos (Real.exp_pos _) (pow_pos (hμm j).1 _)) (by positivity))
  let ρp := fun j => ((np j : ℝ) + 1) / μp j
  let ρm := fun j => ((nm j : ℝ) + 1) / μm j
  have hρp (j : Fin k) : 0 < ρp j ∧ ρp j ≤ R := by
    refine ⟨div_pos (by positivity) (hμp j).1, ?_⟩
    apply (div_le_iff₀ (hμp j).1).mpr
    have hRκ : R * κ = 2 * (C₀ + 1) := by dsimp [R]; field_simp
    have hh := mul_le_mul_of_nonneg_left (hμp j).2 hR.le
    have hn' := (hn j).1
    nlinarith
  have hρm (j : Fin k) : 0 < ρm j ∧ ρm j ≤ R := by
    refine ⟨div_pos (by positivity) (hμm j).1, ?_⟩
    apply (div_le_iff₀ (hμm j).1).mpr
    have hRκ : R * κ = 2 * (C₀ + 1) := by dsimp [R]; field_simp
    have hh := mul_le_mul_of_nonneg_left (hμm j).2 hR.le
    have hn' := (hn j).2
    nlinarith
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
  let I := Fin k × Bool
  let n (a : I) : ℕ := if a.2 then nm a.1 else np a.1
  let ρ (a : I) : ℝ := if a.2 then ρm a.1 else ρp a.1
  let c (o : Ω) (a : I) : ℕ := if a.2 then cm o a.1 else cp o a.1
  let z (t : UnitAddTorus I) (a : I) : ℂ := (ρ a : ℂ) * fourier 1 (t a)
  let W : ℂ := ∏ a : I, (ρ a : ℂ) ^ n a
  have hznorm (t : UnitAddTorus I) (a : I) : ‖z t a‖ = ρ a := by
    dsimp [z]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one]
    apply abs_of_pos
    cases a with | mk j s => cases s <;> simp only [ρ, Bool.false_eq_true, if_false, if_true]
                            <;> exact (by first | exact (hρp j).1 | exact (hρm j).1)
  have hfourierpow (t : UnitAddCircle) (N : ℕ) :
      (fourier 1 t : ℂ) ^ N = fourier (N : ℤ) t := by
    induction N with
    | zero => simp [fourier_zero]
    | succ N ih => simpa only [pow_succ, ih, Nat.cast_add, Nat.cast_one] using
        (fourier_add (m := (N : ℤ)) (n := 1) (x := t)).symm
  have hmono (v : I → ℕ) :
      (∫ t : UnitAddTorus I, UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t *
        ∏ a, z t a ^ v a) =
        if v = n then W else 0 := by
    have hchar (t : UnitAddTorus I) :
        UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t * (∏ a, z t a ^ v a) =
        (∏ a : I, (ρ a : ℂ) ^ v a) *
          ∏ a : I, (fourier (-(n a : ℤ)) (t a) * fourier (v a : ℤ) (t a)) := by
      simp only [z, mul_pow, hfourierpow, UnitAddTorus.mFourier, ContinuousMap.coe_mk]
      rw [prod_mul_distrib, prod_mul_distrib]; ring
    simp_rw [hchar]
    rw [integral_const_mul]
    rw [integral_fintype_prod_volume_eq_prod
      (fun a (t : UnitAddCircle) => fourier (-(n a : ℤ)) t * fourier (v a : ℤ) t)]
    have hi (a : I) :
        (∫ t : UnitAddCircle, fourier (-(n a : ℤ)) t * fourier (v a : ℤ) t) =
          if n a = v a then (1 : ℂ) else 0 := by
      change fourierCoeff (fourier (v a : ℤ)) (n a : ℤ) = _
      rw [fourierCoeff_fourier]
      simp [Pi.single_apply]
    simp_rw [hi]
    by_cases hv : v = n
    · subst v; simp [W]
    · obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
      rw [if_neg hv]
      have hz : (∏ a : I, if n a = v a then (1 : ℂ) else 0) = 0 := by
        apply prod_eq_zero (mem_univ a)
        exact if_neg (Ne.symm ha)
      rw [hz, mul_zero]
  have hcounts (o : Ω) : (c o = n) ↔
      (∀ j, cp o j = np j ∧ cm o j = nm j) := by
    constructor
    · intro h j
      exact ⟨congrFun h (j, false), congrFun h (j, true)⟩
    · intro h; funext a
      rcases a with ⟨j, s⟩
      cases s <;> first | exact (h j).1 | exact (h j).2
  have hproduct (o : Ω) (t : UnitAddTorus I) :
      (∏ j, z t (j, false) ^ cp o j * z t (j, true) ^ cm o j) =
        ∏ a : I, z t a ^ c o a := by
    rw [Fintype.prod_prod_type]
    apply prod_congr rfl
    intro j _
    simp only [Fintype.prod_bool, c, Bool.false_eq_true, if_false, if_true]
    exact mul_comm _ _
  have hNativeCoefficient :
      (∫ t : UnitAddTorus I, UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t *
        F (fun j => z t (j, false)) (fun j => z t (j, true))) = (P : ℂ) * W := by
    simp only [F, mul_sum]
    rw [integral_finsetSum]
    · simp_rw [hproduct]
      have hterm (o : Ω) :
          (∫ t : UnitAddTorus I, UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t *
            ((w o : ℂ) * ∏ a, z t a ^ c o a)) =
          (if c o = n then (w o : ℂ) else 0) * W := by
        simp_rw [mul_left_comm _ (w o : ℂ)]
        rw [integral_const_mul, hmono]
        split_ifs <;> simp
      simp_rw [hterm, hcounts]
      simp only [← sum_mul, P, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero]
    · intro o _
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      dsimp [z, UnitAddTorus.mFourier, F]
      fun_prop
  let G (t : UnitAddTorus I) : ℂ := Complex.exp
    (∑ j, ((μp j : ℂ) * (z t (j, false) - 1) + (μm j : ℂ) * (z t (j, true) - 1)))
  have hPoissonCoefficient :
      (∫ t : UnitAddTorus I, UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t * G t) =
        (Q : ℂ) * W := by
    let μ (a : I) : ℝ := if a.2 then μm a.1 else μp a.1
    have hsingle (a : I) :
        (∫ t : UnitAddCircle, fourier (-(n a : ℤ)) t *
          Complex.exp ((μ a : ℂ) * ((ρ a : ℂ) * fourier 1 t - 1))) =
        Complex.exp (-(μ a : ℂ)) * (μ a : ℂ) ^ n a /
          (n a).factorial * (ρ a : ℂ) ^ n a := by
      let f (N : ℕ) (t : UnitAddCircle) : ℂ :=
        fourier (-(n a : ℤ)) t * (((μ a : ℂ) * (ρ a : ℂ) * fourier 1 t) ^ N /
          (N.factorial : ℂ))
      have hf (N : ℕ) : Integrable (f N) := by
        apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
        dsimp only [f]; fun_prop
      have hnorm (N : ℕ) (t : UnitAddCircle) :
          ‖f N t‖ = ‖(μ a : ℂ) * (ρ a : ℂ)‖ ^ N / (N.factorial : ℝ) := by
        simp only [f, norm_mul, fourier_apply, Circle.norm_coe, one_mul, norm_div, norm_pow,
          mul_one, Complex.norm_natCast]
      have hsum : Summable (fun N => ∫ t : UnitAddCircle, ‖f N t‖) := by
        simp_rw [hnorm]
        simpa using Real.summable_pow_div_factorial ‖(μ a : ℂ) * (ρ a : ℂ)‖
      have hexp (t : UnitAddCircle) :
          (∑' N, f N t) = fourier (-(n a : ℤ)) t *
            Complex.exp ((μ a : ℂ) * (ρ a : ℂ) * fourier 1 t) := by
        dsimp only [f]
        rw [tsum_mul_left]
        rw [Complex.exp_eq_exp_ℂ]
        exact congrArg (fun w : ℂ => fourier (-(n a : ℤ)) t * w)
          (NormedSpace.expSeries_div_hasSum_exp _).tsum_eq
      have hterm (N : ℕ) :
          (∫ t : UnitAddCircle, f N t) =
          if N = n a then ((μ a : ℂ) * (ρ a : ℂ)) ^ n a / (n a).factorial else 0 := by
        have he (t : UnitAddCircle) : f N t =
            (((μ a : ℂ) * (ρ a : ℂ)) ^ N / (N.factorial : ℂ)) *
              (fourier (-(n a : ℤ)) t * fourier (N : ℤ) t) := by
          dsimp only [f]; rw [mul_pow, hfourierpow]; ring
        simp_rw [he]
        rw [integral_const_mul]
        change _ * fourierCoeff (fourier (N : ℤ)) (n a : ℤ) = _
        rw [fourierCoeff_fourier]
        by_cases h : N = n a
        · subst N; simp [Pi.single_apply]
        · simp [Pi.single_apply, h, Ne.symm h]
      have he (t : UnitAddCircle) :
          fourier (-(n a : ℤ)) t *
            Complex.exp ((μ a : ℂ) * ((ρ a : ℂ) * fourier 1 t - 1)) =
          Complex.exp (-(μ a : ℂ)) *
            (fourier (-(n a : ℤ)) t *
              Complex.exp ((μ a : ℂ) * (ρ a : ℂ) * fourier 1 t)) := by
        rw [show (μ a : ℂ) * ((ρ a : ℂ) * fourier 1 t - 1) =
          -(μ a : ℂ) + (μ a : ℂ) * (ρ a : ℂ) * fourier 1 t by ring,
          Complex.exp_add]; ring
      simp_rw [he]
      rw [integral_const_mul]
      simp_rw [← hexp]
      rw [← integral_tsum_of_summable_integral_norm hf hsum]
      simp_rw [hterm]
      rw [tsum_ite_eq]
      rw [mul_pow]; ring
    have hG (t : UnitAddTorus I) : G t =
        ∏ a : I, Complex.exp ((μ a : ℂ) * (z t a - 1)) := by
      dsimp [G]
      rw [← Complex.exp_sum]
      congr 1
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro j _
      simp only [Fintype.sum_bool, μ, Bool.false_eq_true, if_false, if_true]
      ring
    simp_rw [hG]
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, ← prod_mul_distrib]
    dsimp only [z]
    rw [integral_fintype_prod_volume_eq_prod
      (fun a (t : UnitAddCircle) => fourier (-(n a : ℤ)) t *
        Complex.exp ((μ a : ℂ) * ((ρ a : ℂ) * fourier 1 t - 1)))]
    simp_rw [hsingle]
    rw [prod_mul_distrib]
    congr 1
    dsimp [Q]
    rw [Fintype.prod_prod_type]
    push_cast
    apply prod_congr rfl
    intro j _
    simp only [Fintype.prod_bool, μ, n, Bool.false_eq_true, if_false, if_true]
    ring
  let H : ℝ := Real.exp (∑ j, (μp j * (ρp j - 1) + μm j * (ρm j - 1)))
  have hpoint (t : UnitAddTorus I) :
      ‖F (fun j => z t (j, false)) (fun j => z t (j, true)) - G t‖ ≤ ε * H := by
    have hp (j : Fin k) : ‖z t (j, false)‖ ≤ R := by rw [hznorm]; exact (hρp j).2
    have hm (j : Fin k) : ‖z t (j, true)‖ ≤ R := by rw [hznorm]; exact (hρm j).2
    have hh := henv (fun j => z t (j, false)) (fun j => z t (j, true)) hp hm
    have hre :
        (∑ j, (μp j * ((z t (j, false)).re - 1) + μm j * ((z t (j, true)).re - 1))) ≤
        ∑ j, (μp j * (ρp j - 1) + μm j * (ρm j - 1)) := by
      apply sum_le_sum
      intro j _
      have hp' : (z t (j, false)).re ≤ ρp j :=
        (Complex.re_le_norm _).trans_eq (hznorm t (j, false))
      have hm' : (z t (j, true)).re ≤ ρm j :=
        (Complex.re_le_norm _).trans_eq (hznorm t (j, true))
      nlinarith [(hμp j).1, (hμm j).1]
    exact hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre) hε)
  have hcharNorm (t : UnitAddTorus I) :
      ‖UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t‖ = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
      fourier_apply, Circle.norm_coe, prod_const_one]
  have herror : |P - Q| * ‖W‖ ≤ ε * H := by
    have hiF : Integrable (fun t : UnitAddTorus I =>
        UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t *
          F (fun j => z t (j, false)) (fun j => z t (j, true))) := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      dsimp only [F, z, UnitAddTorus.mFourier]; fun_prop
    have hiG : Integrable (fun t : UnitAddTorus I =>
        UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t * G t) := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      dsimp only [G, z, UnitAddTorus.mFourier]; fun_prop
    have hid : (P : ℂ) * W - (Q : ℂ) * W =
        ∫ t : UnitAddTorus I, UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t *
          (F (fun j => z t (j, false)) (fun j => z t (j, true)) - G t) := by
      simp_rw [mul_sub]
      rw [integral_sub hiF hiG, hNativeCoefficient, hPoissonCoefficient]
    have hh := norm_integral_le_of_norm_le_const
      (μ := (volume : Measure (UnitAddTorus I)))
      (C := ε * H)
      (f := fun t : UnitAddTorus I => UnitAddTorus.mFourier (fun a => -(n a : ℤ)) t *
        (F (fun j => z t (j, false)) (fun j => z t (j, true)) - G t))
      (Filter.Eventually.of_forall fun t => by
        rw [norm_mul, hcharNorm, one_mul]
        exact hpoint t)
    rw [← hid, ← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs] at hh
    simpa using hh
  have hStirling (N : ℕ) :
      Real.exp ((N : ℝ) + 1) * (N.factorial : ℝ) / ((N : ℝ) + 1) ^ N ≤
        Cs * Real.sqrt ((N : ℝ) + 1) := by
    by_cases hN0 : N = 0
    · subst N
      simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one,
        mul_one, pow_zero, div_one, Real.sqrt_one]
      dsimp only [Cs]
      have he : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      nlinarith [Real.sqrt_nonneg (2 * Real.pi), Real.exp_pos 2]
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hNp : (0 : ℝ) < N := by linarith
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hfac : (0 : ℝ) < N.factorial := by positivity
    have hupper : CycleGeodesic.stirlingError N ≤ 1 := by
      have hh := CycleGeodesic.stirlingError_upper (N - 1)
      have hi : N - 1 + 1 = N := by omega
      rw [hi] at hh
      have hj : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast hi
      rw [hj] at hh
      exact hh.trans ((div_le_iff₀ (by positivity : (0 : ℝ) < 12 * N)).mpr
        (by linarith))
    have hf := CycleGeodesic.stirlingError_formula hN0
    have hlog := Real.log_le_log hNp (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith)
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (N : ℝ) + 1 / 2 by positivity)
    let X : ℝ := Real.exp ((N : ℝ) + 1) * (N.factorial : ℝ) / ((N : ℝ) + 1) ^ N
    have hX : 0 < X := by dsimp only [X]; positivity
    have hlogX : Real.log X ≤ 2 + (1 / 2) * Real.log ((N : ℝ) + 1) +
        (1 / 2) * Real.log (2 * Real.pi) := by
      dsimp only [X]
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (Real.exp_ne_zero _) hfac.ne', Real.log_exp, Real.log_pow]
      nlinarith [hupper, hf]
    have hsqrtN : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.2 hN1
    have hsqrtpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have he := Real.exp_le_exp.mpr hlogX
    rw [Real.exp_log hX] at he
    have hs1 : (1 / 2) * Real.log ((N : ℝ) + 1) = Real.log (Real.sqrt ((N : ℝ) + 1)) := by
      rw [Real.log_sqrt hN1.le]; ring
    have hs2 : (1 / 2) * Real.log (2 * Real.pi) = Real.log (Real.sqrt (2 * Real.pi)) := by
      rw [Real.log_sqrt (by positivity : 0 ≤ 2 * Real.pi)]; ring
    rw [hs1, hs2, Real.exp_add, Real.exp_add, Real.exp_log hsqrtN, Real.exp_log hsqrtpi] at he
    dsimp only [X] at he
    exact he.trans (by dsimp only [Cs]; nlinarith [Real.exp_pos 2])
  have hweight (μ : ℝ) (hμ : 0 < μ) (N : ℕ) :
      Real.exp (μ * (((N : ℝ) + 1) / μ - 1)) ≤
        (Real.exp (-μ) * μ ^ N / (N.factorial : ℝ) *
          (((N : ℝ) + 1) / μ) ^ N) * Cs * Real.sqrt ((N : ℝ) + 1) := by
    let w := Real.exp (-μ) * μ ^ N / (N.factorial : ℝ) * (((N : ℝ) + 1) / μ) ^ N
    have hw : 0 < w := by dsimp only [w]; positivity
    have hid : Real.exp (μ * (((N : ℝ) + 1) / μ - 1)) =
        w * (Real.exp ((N : ℝ) + 1) * (N.factorial : ℝ) / ((N : ℝ) + 1) ^ N) := by
      have he : μ * (((N : ℝ) + 1) / μ - 1) = -μ + ((N : ℝ) + 1) := by
        field_simp [hμ.ne']; ring
      rw [he, Real.exp_add]
      dsimp only [w]
      rw [div_pow]
      field_simp [hμ.ne']
    rw [hid]
    exact (mul_le_mul_of_nonneg_left (hStirling N) hw.le).trans_eq (by ring)
  let B₀ : ℝ := (C₀ + 1) * L
  let w (j : Fin k) : ℝ :=
    (Real.exp (-μp j) * μp j ^ np j / (np j).factorial * ρp j ^ np j) *
      (Real.exp (-μm j) * μm j ^ nm j / (nm j).factorial * ρm j ^ nm j)
  have hwpos (j : Fin k) : 0 < w j := by
    have hp := (hμp j).1
    have hm := (hμm j).1
    have hrp := (hρp j).1
    have hrm := (hρm j).1
    dsimp only [w]; positivity
  have hWnorm : ‖W‖ = ∏ j, ρp j ^ np j * ρm j ^ nm j := by
    dsimp only [W]
    rw [norm_prod, Fintype.prod_prod_type]
    apply prod_congr rfl
    intro j _
    simp only [Fintype.prod_bool, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      ρ, n, Bool.false_eq_true, if_false, if_true]
    rw [abs_of_pos (hρp j).1, abs_of_pos (hρm j).1]
    ring
  have hWpos : 0 < ‖W‖ := by rw [hWnorm]; exact prod_pos fun j _ => mul_pos (pow_pos (hρp j).1 _) (pow_pos (hρm j).1 _)
  have hqw : Q * ‖W‖ = ∏ j, w j := by
    rw [hWnorm]
    dsimp only [Q, w]
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    ring
  have hnormalization : H ≤ Q * ‖W‖ * (Cs ^ 2 * B₀) ^ k := by
    have hHP : H = ∏ j, Real.exp (μp j * (ρp j - 1)) *
        Real.exp (μm j * (ρm j - 1)) := by
      dsimp only [H]
      rw [Real.exp_sum]
      simp_rw [Real.exp_add]
    have hp (j : Fin k) :
        Real.exp (μp j * (ρp j - 1)) * Real.exp (μm j * (ρm j - 1)) ≤
          w j * (Cs ^ 2 * B₀) := by
      have hsp := hweight (μp j) (hμp j).1 (np j)
      have hsm := hweight (μm j) (hμm j).1 (nm j)
      change Real.exp (μp j * (ρp j - 1)) ≤ _ at hsp
      change Real.exp (μm j * (ρm j - 1)) ≤ _ at hsm
      have hnp : (np j : ℝ) + 1 ≤ B₀ := by
        dsimp only [B₀]; nlinarith [(hn j).1]
      have hnm : (nm j : ℝ) + 1 ≤ B₀ := by
        dsimp only [B₀]; nlinarith [(hn j).2]
      have hs : Real.sqrt ((np j : ℝ) + 1) * Real.sqrt ((nm j : ℝ) + 1) ≤ B₀ := by
        calc
          _ ≤ Real.sqrt B₀ * Real.sqrt B₀ := by gcongr
          _ = B₀ := Real.mul_self_sqrt (by dsimp only [B₀]; positivity)
      have hc : 0 ≤ Cs := by dsimp only [Cs]; positivity
      have hmp := (hμp j).1
      have hrp := (hρp j).1
      have hh := mul_le_mul hsp hsm (Real.exp_pos _).le (by positivity)
      have hnw : 0 ≤ w j * Cs ^ 2 := mul_nonneg (hwpos j).le (sq_nonneg Cs)
      have he : (Real.exp (-μp j) * μp j ^ np j / (np j).factorial * ρp j ^ np j *
          Cs * Real.sqrt ((np j : ℝ) + 1)) *
          (Real.exp (-μm j) * μm j ^ nm j / (nm j).factorial * ρm j ^ nm j *
          Cs * Real.sqrt ((nm j : ℝ) + 1)) =
            w j * Cs ^ 2 * (Real.sqrt ((np j : ℝ) + 1) * Real.sqrt ((nm j : ℝ) + 1)) := by
        dsimp only [w]; ring
      rw [he] at hh
      exact hh.trans ((mul_le_mul_of_nonneg_left hs hnw).trans_eq (by ring))
    rw [hHP, hqw]
    have hh := prod_le_prod₀ (fun j (_ : j ∈ (univ : Finset (Fin k))) =>
      (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le) (fun j _ => hp j)
    simpa only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, mul_pow] using hh
  have hCs : 1 ≤ Cs := by
    dsimp only [Cs]
    have he : 1 ≤ Real.exp 2 := Real.one_le_exp_iff.mpr (by norm_num)
    nlinarith [Real.sqrt_nonneg (2 * Real.pi)]
  have hscale : (Cs ^ 2 * B₀) ^ k ≤ Cs ^ 4 * (C₀ + 1) ^ 2 * L ^ k := by
    dsimp only [B₀]
    rcases hk with rfl | rfl
    · simp only [pow_one]
      have hcs2 : 1 ≤ Cs ^ 2 := by nlinarith
      have hs : Cs ^ 2 ≤ Cs ^ 4 := by nlinarith [sq_nonneg (Cs ^ 2 - 1)]
      have hc : C₀ + 1 ≤ (C₀ + 1) ^ 2 := by nlinarith
      have hh := mul_le_mul hs hc (by linarith : 0 ≤ C₀ + 1) (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (le_trans (by norm_num : (0 : ℝ) ≤ 1) hLr)
    · apply le_of_eq; ring
  have hrelative : |P / Q - 1| ≤ ε * (Cs ^ 4 * (C₀ + 1) ^ 2 * L ^ k) := by
    have hn' := hnormalization.trans (mul_le_mul_of_nonneg_left hscale (by positivity))
    have he := herror.trans (mul_le_mul_of_nonneg_left hn' hε)
    rw [div_sub_one hQ.ne', abs_div, abs_of_pos hQ]
    apply (div_le_iff₀ hQ).mpr
    apply (mul_le_mul_iff_right₀ hWpos).mp
    nlinarith
  exact hrelative.trans_eq (by ring)

end D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient
