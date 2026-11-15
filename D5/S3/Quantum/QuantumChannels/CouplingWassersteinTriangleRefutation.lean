/- GID: D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.claim; result=D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.result; claim=D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.claim
   digest: The trace-distance coupling Wasserstein distance of order one fails the triangle inequality. -/

import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.QuantumStates.DensitySpan

/-! admission_basis: open-problem-resolution; preregistration: #30901.
The ground distance is the square-root expression in equation (81).
All auxiliary theorems are private and used by the terminal refutation. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.style.longLine false
open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)

noncomputable section
namespace D5.S3.Quantum.QuantumChannels.CouplingWassersteinTriangleRefutation

def UnitVector (n : ℕ) := {v : Fin n → ℂ // ∑ i, Complex.normSq (v i) = 1}

def ground {n : ℕ} (u v : UnitVector n) : ℝ :=
  Real.sqrt (1 - Complex.normSq (∑ i, star (u.val i) * v.val i))

structure Plan {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) where
  weight : ℕ → ℝ
  nonneg : ∀ j, 0 ≤ weight j
  source : ℕ → UnitVector n
  target : ℕ → UnitVector n
  left : HasSum (fun j => (weight j : ℂ) • rankOneDensity (source j).val) ρ
  right : HasSum (fun j => (weight j : ℂ) • rankOneDensity (target j).val) σ
  mass : HasSum weight 1

def cost {n : ℕ} {ρ σ : Matrix (Fin n) (Fin n) ℂ} (Q : Plan ρ σ) : ℝ :=
  ∑' j, Q.weight j * ground (Q.source j) (Q.target j)

def wasserstein {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sInf {c | ∃ Q : Plan ρ σ, cost Q = c}

def claim : Prop :=
  ∀ (n : ℕ) (ρ τ σ : Matrix (Fin n) (Fin n) ℂ),
    IsDensity ρ → IsDensity τ → IsDensity σ →
    wasserstein ρ σ ≤ wasserstein ρ τ + wasserstein τ σ

private theorem ground_bounds {n : ℕ} (u v : UnitVector n) :
    0 ≤ ground u v ∧ ground u v ≤ 1 := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  apply Real.sqrt_le_one.mpr
  linarith [Complex.normSq_nonneg (∑ i, star (u.val i) * v.val i)]

private theorem cost_summable {n : ℕ} {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (Q : Plan ρ σ) : Summable (fun j => Q.weight j * ground (Q.source j) (Q.target j)) := by
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (Q.nonneg j) (ground_bounds _ _).1)
    (fun j => mul_le_of_le_one_right (Q.nonneg j) (ground_bounds _ _).2) Q.mass.summable

private theorem cost_nonneg {n : ℕ} {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (Q : Plan ρ σ) : 0 ≤ cost Q :=
  tsum_nonneg fun j => mul_nonneg (Q.nonneg j) (ground_bounds _ _).1

private theorem distance_le_cost {n : ℕ} {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (Q : Plan ρ σ) : wasserstein ρ σ ≤ cost Q := by
  apply csInf_le
  · exact ⟨0, by rintro c ⟨Q, rfl⟩; exact cost_nonneg Q⟩
  · exact ⟨Q, rfl⟩

private def p : UnitVector 3 := ⟨![4/5,3/5,0], by norm_num [Fin.sum_univ_succ, Complex.normSq_apply]⟩
private def q : UnitVector 3 := ⟨![3/5,4/5,0], by norm_num [Fin.sum_univ_succ, Complex.normSq_apply]⟩
private def e (k : Fin 3) : UnitVector 3 :=
  ⟨Pi.single k 1, by simp [Complex.normSq_apply, Pi.single_apply]⟩
private def u : UnitVector 3 :=
  ⟨![119/169,120/169,0], by norm_num [Fin.sum_univ_succ, Complex.normSq_apply]⟩
private def rho : Matrix (Fin 3) (Fin 3) ℂ := rankOneDensity p.val
private def tau : Matrix (Fin 3) (Fin 3) ℂ := (1/2 : ℂ) • (rho + rankOneDensity q.val)
private def sigma : Matrix (Fin 3) (Fin 3) ℂ := !![49/100,12/25,0;12/25,1/2,0;0,0,1/100]

private theorem sqrt_mixing (q r t : ℝ) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (ht : 0 ≤ t) (hqt : q + t = 1) :
    Real.sqrt (q*r) + t ≤ Real.sqrt (r+t) := by
  have hs := Real.sqrt_nonneg (q*r)
  have hs2 := Real.sq_sqrt (mul_nonneg hq hr)
  have ham : 2 * Real.sqrt (q*r) ≤ q+r := by
    nlinarith [sq_nonneg (q-r)]
  apply Real.le_sqrt_of_sq_le
  have hh := mul_nonneg ht (sub_nonneg.mpr ham)
  nlinarith

private theorem pointwise (v : UnitVector 3) :
    -(9/25 : ℝ) * Complex.normSq (v.val 0) +
      (16/25 : ℝ) * Complex.normSq (v.val 1) + Complex.normSq (v.val 2) ≤ ground p v := by
  let z := v.val 0
  let w := v.val 1
  let A := Complex.normSq z
  let B := Complex.normSq w
  let t := Complex.normSq (v.val 2)
  let r := Complex.normSq (-(3/5 : ℂ)*z+(4/5 : ℂ)*w)
  let x := Complex.normSq ((4/5 : ℂ)*z+(3/5 : ℂ)*w)
  let L := -(9/25 : ℝ)*A+(16/25 : ℝ)*B
  have hunit : A+B+t=1 := by simpa [A,B,t,z,w,Fin.sum_univ_succ,add_assoc] using v.property
  have hxy : x+r=A+B := by
    dsimp [x,r,A,B]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.neg_re, Complex.neg_im]
    norm_num
    ring
  have hid : (A+B)*r-L^2 =
      ((12/25 : ℝ)*(A+B)-(z*star w).re)^2+(z*star w).im^2 := by
    dsimp [A,B,r,L]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    norm_num
    ring
  have hL : L ≤ Real.sqrt ((A+B)*r) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg ((12/25 : ℝ)*(A+B)-(z*star w).re), sq_nonneg (z*star w).im]
  have hm := sqrt_mixing (A+B) r t (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (Complex.normSq_nonneg _) (Complex.normSq_nonneg _) hunit
  have hg : ground p v = Real.sqrt (r+t) := by
    unfold ground
    have he : (∑ i, star (p.val i) * v.val i) = (4/5 : ℂ)*z+(3/5 : ℂ)*w := by
      norm_num [p,Fin.sum_univ_succ,z,w,Complex.star_def,map_ofNat]
    rw [he]
    change Real.sqrt (1-x) = Real.sqrt (r+t)
    congr 1
    linarith
  rw [hg]
  change L+t ≤ _
  linarith

private theorem four_hasSum {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : ℕ → E) (hf : ∀ j, 4 ≤ j → f j = 0) :
    HasSum f (f 0 + f 1 + f 2 + f 3) := by
  have h : HasSum f (∑ j ∈ Finset.range 4, f j) :=
    hasSum_sum_of_ne_finset_zero (s := Finset.range 4)
    (fun j hj => hf j (by simpa using hj))
  simpa [Finset.sum_range_succ, add_assoc] using h

private def extendWeights (w : Fin 4 → ℝ) : ℕ → ℝ
  | 0 => w 0 | 1 => w 1 | 2 => w 2 | _ => w 3

private def finiteWeights (w : Fin 4 → ℝ) (j : ℕ) : ℝ :=
  if j < 4 then extendWeights w j else 0

private def extendVectors (v : Fin 4 → UnitVector 3) : ℕ → UnitVector 3
  | 0 => v 0 | 1 => v 1 | 2 => v 2 | _ => v 3

private def finitePlan (ρ σ : Matrix (Fin 3) (Fin 3) ℂ)
    (w : Fin 4 → ℝ) (a b : Fin 4 → UnitVector 3)
    (hw : ∀ i, 0 ≤ w i) (hm : w 0+w 1+w 2+w 3=1)
    (ha : (w 0 : ℂ) • rankOneDensity (a 0).val +
      (w 1 : ℂ) • rankOneDensity (a 1).val +
      (w 2 : ℂ) • rankOneDensity (a 2).val +
      (w 3 : ℂ) • rankOneDensity (a 3).val = ρ)
    (hb : (w 0 : ℂ) • rankOneDensity (b 0).val +
      (w 1 : ℂ) • rankOneDensity (b 1).val +
      (w 2 : ℂ) • rankOneDensity (b 2).val +
      (w 3 : ℂ) • rankOneDensity (b 3).val = σ) : Plan ρ σ where
  weight := finiteWeights w
  source := extendVectors a
  target := extendVectors b
  nonneg j := by
    unfold finiteWeights
    split_ifs with h
    · interval_cases j <;> exact hw _
    · exact le_rfl
  mass := by
    have h := four_hasSum (finiteWeights w) (fun j hj => by simp [finiteWeights, not_lt.mpr hj])
    simpa [finiteWeights, extendWeights, hm] using h
  left := by
    have h := four_hasSum (fun j => (finiteWeights w j : ℂ) • rankOneDensity (extendVectors a j).val)
      (fun j hj => by simp [finiteWeights, not_lt.mpr hj])
    convert h using 1
    simpa only [finiteWeights, extendWeights, extendVectors, ite_true, Nat.reduceLT] using ha.symm
  right := by
    have h := four_hasSum (fun j => (finiteWeights w j : ℂ) • rankOneDensity (extendVectors b j).val)
      (fun j hj => by simp [finiteWeights, not_lt.mpr hj])
    convert h using 1
    simpa only [finiteWeights, extendWeights, extendVectors, ite_true, Nat.reduceLT] using hb.symm

private theorem ground_self (v : UnitVector 3) : ground v v = 0 := by
  have he : (∑ i, star (v.val i) * v.val i) = (1 : ℂ) := by
    calc
      _ = ∑ i, (Complex.normSq (v.val i) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Complex.normSq_eq_conj_mul_self.symm
      _ = 1 := by rw [← Complex.ofReal_sum, v.property]; norm_num
  change Real.sqrt (1 - Complex.normSq (∑ i, star (v.val i) * v.val i)) = 0
  rw [he]
  norm_num

private theorem finite_cost (ρ σ : Matrix (Fin 3) (Fin 3) ℂ)
    (w : Fin 4 → ℝ) (a b : Fin 4 → UnitVector 3)
    (hw hm ha hb) :
    cost (finitePlan ρ σ w a b hw hm ha hb) =
      w 0 * ground (a 0) (b 0) + w 1 * ground (a 1) (b 1) +
      w 2 * ground (a 2) (b 2) + w 3 * ground (a 3) (b 3) := by
  unfold cost
  have h := four_hasSum
    (fun j => finiteWeights w j * ground (extendVectors a j) (extendVectors b j))
    (fun j hj => by simp [finiteWeights, not_lt.mpr hj])
  simpa [finitePlan, finiteWeights, extendWeights, extendVectors] using h.tsum_eq

private def shortPlan : Plan rho tau :=
  finitePlan rho tau ![1/2,1/2,0,0] ![p,p,p,p] ![p,q,p,p]
    (by intro i; fin_cases i <;> norm_num) (by norm_num)
    (by
      ext i j
      simp only [rho, Matrix.add_apply, Matrix.smul_apply, rankOneDensity,
        Matrix.vecMulVec_apply, Pi.star_apply]
      fin_cases i <;> fin_cases j <;>
        norm_num [p, smul_eq_mul, map_ofNat])
    (by
      ext i j
      simp only [tau, rho, Matrix.add_apply, Matrix.smul_apply, rankOneDensity,
        Matrix.vecMulVec_apply, Pi.star_apply]
      fin_cases i <;> fin_cases j <;>
        norm_num [p, q, smul_eq_mul, map_ofNat])

private theorem short_bound : wasserstein rho tau ≤ 7/50 := by
  have h := distance_le_cost shortPlan
  have hpq : ground p q = 7/25 := by
    norm_num [ground,p,q,Fin.sum_univ_succ,Complex.normSq_apply,map_ofNat,Real.sqrt_div]
  have hc : cost shortPlan = 7/50 := by
    rw [shortPlan, finite_cost]
    simp [ground_self,hpq]
    norm_num
  rwa [hc] at h

private def sharedWeights : Fin 4 → ℝ := ![28561/29750,7/500,19/1190,1/100]
private def sharedSource : Fin 4 → UnitVector 3 := ![u,e 0,e 1,e 0]
private def sharedTarget : Fin 4 → UnitVector 3 := ![u,e 0,e 1,e 2]

private theorem shared_nonneg (i : Fin 4) : 0 ≤ sharedWeights i := by
  fin_cases i <;> norm_num [sharedWeights]

private theorem shared_mass :
    sharedWeights 0+sharedWeights 1+sharedWeights 2+sharedWeights 3=1 := by
  norm_num [sharedWeights]

private theorem shared_left :
    (sharedWeights 0 : ℂ) • rankOneDensity (sharedSource 0).val +
    (sharedWeights 1 : ℂ) • rankOneDensity (sharedSource 1).val +
    (sharedWeights 2 : ℂ) • rankOneDensity (sharedSource 2).val +
    (sharedWeights 3 : ℂ) • rankOneDensity (sharedSource 3).val = tau := by
  ext i j
  simp only [tau, rho, Matrix.add_apply, Matrix.smul_apply, rankOneDensity,
    Matrix.vecMulVec_apply, Pi.star_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [sharedWeights, sharedSource, u, e, p, q, Pi.single_apply,
      smul_eq_mul, map_ofNat]

private theorem shared_right :
    (sharedWeights 0 : ℂ) • rankOneDensity (sharedTarget 0).val +
    (sharedWeights 1 : ℂ) • rankOneDensity (sharedTarget 1).val +
    (sharedWeights 2 : ℂ) • rankOneDensity (sharedTarget 2).val +
    (sharedWeights 3 : ℂ) • rankOneDensity (sharedTarget 3).val = sigma := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, rankOneDensity,
    Matrix.vecMulVec_apply, Pi.star_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [sharedWeights, sharedTarget, u, e, sigma, Pi.single_apply,
      smul_eq_mul, map_ofNat]

private def middlePlan : Plan tau sigma :=
  finitePlan tau sigma sharedWeights sharedSource sharedTarget shared_nonneg shared_mass
    shared_left shared_right

private def longPlan : Plan rho sigma :=
  finitePlan rho sigma sharedWeights (fun _ => p) sharedTarget shared_nonneg shared_mass
    (by simp [sharedWeights,rho]; module) shared_right

private theorem middle_bound : wasserstein tau sigma ≤ 1/100 := by
  have h := distance_le_cost middlePlan
  have he : ground (e 0) (e 2) = 1 := by
    norm_num [ground,e,Fin.sum_univ_succ,Pi.single_apply,Complex.normSq_apply]
  have hc : cost middlePlan = 1/100 := by
    rw [middlePlan,finite_cost]
    norm_num [sharedWeights,sharedSource,sharedTarget,ground_self,he]
  rwa [hc] at h

open scoped MatrixOrder in
private theorem unit_density (v : UnitVector 3) : IsDensity (rankOneDensity v.val) := by
  have hv : star v.val ⬝ᵥ v.val = 1 := by
    unfold dotProduct
    simp only [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    rw [← Complex.ofReal_sum, v.property, Complex.ofReal_one]
  let density := D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity.pureDensityState v.val hv
  refine ⟨Matrix.nonneg_iff_posSemidef.mp ?_, density.property.2⟩
  exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm density.property.1

private theorem rho_density : IsDensity rho := unit_density p

private theorem tau_density : IsDensity tau := by
  refine ⟨?_, ?_⟩
  · exact ((unit_density p).1.add (unit_density q).1).smul (by norm_num [Complex.le_def])
  · simp [tau,Matrix.trace_smul,Matrix.trace_add,(unit_density p).2,(unit_density q).2,rho]
    norm_num

private theorem sigma_density : IsDensity sigma := by
  rw [← shared_right]
  constructor
  · repeat' apply Matrix.PosSemidef.add
    all_goals exact (unit_density _).1.smul (by norm_num [sharedWeights,Complex.le_def])
  · simp [Matrix.trace_add,Matrix.trace_smul,(unit_density _).2,sharedWeights]
    norm_num

private theorem entry_real {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ}
    {weight : ℕ → ℝ} {vectors : ℕ → UnitVector n}
    (h : HasSum (fun j => (weight j : ℂ) • rankOneDensity (vectors j).val) ρ)
    (i k : Fin n) :
    HasSum (fun j => weight j * ((vectors j).val i * star ((vectors j).val k)).re)
      (ρ i k).re := by
  have hh := Complex.hasSum_re (Pi.hasSum.mp (Pi.hasSum.mp h i) k)
  simpa only [rankOneDensity, Matrix.vecMulVec_apply, Matrix.smul_apply,
    smul_eq_mul, Pi.star_apply, Complex.re_ofReal_mul] using hh

private theorem entry_diagonal {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ}
    {weight : ℕ → ℝ} {vectors : ℕ → UnitVector n}
    (h : HasSum (fun j => (weight j : ℂ) • rankOneDensity (vectors j).val) ρ)
    (i : Fin n) :
    HasSum (fun j => weight j * Complex.normSq ((vectors j).val i)) (ρ i i).re := by
  simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re] using entry_real h i i

private theorem pure_source_ground (Q : Plan rho sigma) (j : ℕ)
    (hj : 0 < Q.weight j) :
    ground (Q.source j) (Q.target j) = ground p (Q.target j) := by
  have h00 : HasSum (fun k => Q.weight k * Complex.normSq ((Q.source k).val 0))
      (16/25 : ℝ) := by
    convert entry_diagonal Q.left 0 using 1 <;>
      norm_num [rho, p, rankOneDensity, Matrix.vecMulVec_apply]
  have h11 : HasSum (fun k => Q.weight k * Complex.normSq ((Q.source k).val 1))
      (9/25 : ℝ) := by
    convert entry_diagonal Q.left 1 using 1 <;>
      norm_num [rho, p, rankOneDensity, Matrix.vecMulVec_apply]
  have h01 : HasSum (fun k => Q.weight k *
      ((Q.source k).val 0 * star ((Q.source k).val 1)).re) (12/25 : ℝ) := by
    convert entry_real Q.left 0 1 using 1 <;>
      norm_num [rho, p, rankOneDensity, Matrix.vecMulVec_apply]
  have h22 : HasSum (fun k => Q.weight k * Complex.normSq ((Q.source k).val 2))
      (0 : ℝ) := by
    convert entry_diagonal Q.left 2 using 1 <;>
      norm_num [rho, p, rankOneDensity, Matrix.vecMulVec_apply]
  have hd : HasSum (fun k => Q.weight k *
      Complex.normSq ((3 : ℂ) * (Q.source k).val 0 - (4 : ℂ) * (Q.source k).val 1))
      (0 : ℝ) := by
    convert ((h00.mul_left 9).add (h11.mul_left 16)).sub (h01.mul_left 24) using 1
    · funext k
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
      norm_num
      ring
    · norm_num
  have hz2 : Q.weight j * Complex.normSq ((Q.source j).val 2) = 0 := by
    apply le_antisymm
    · exact le_hasSum h22 j (fun k _ => mul_nonneg (Q.nonneg k) (Complex.normSq_nonneg _))
    · exact mul_nonneg (Q.nonneg j) (Complex.normSq_nonneg _)
  have hzd : Q.weight j * Complex.normSq
      ((3 : ℂ) * (Q.source j).val 0 - (4 : ℂ) * (Q.source j).val 1) = 0 := by
    apply le_antisymm
    · exact le_hasSum hd j (fun k _ => mul_nonneg (Q.nonneg k) (Complex.normSq_nonneg _))
    · exact mul_nonneg (Q.nonneg j) (Complex.normSq_nonneg _)
  have h2 : (Q.source j).val 2 = 0 :=
    Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hz2).resolve_left (ne_of_gt hj))
  have hd0 : (3 : ℂ) * (Q.source j).val 0 - (4 : ℂ) * (Q.source j).val 1 = 0 :=
    Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hzd).resolve_left (ne_of_gt hj))
  have h1 : (Q.source j).val 1 = (3/4 : ℂ) * (Q.source j).val 0 := by
    linear_combination (-1/4 : ℂ) * hd0
  have hunit := (Q.source j).property
  change Complex.normSq ((Q.source j).val 0) +
    (Complex.normSq ((Q.source j).val 1) +
    (Complex.normSq ((Q.source j).val 2) + 0)) = 1 at hunit
  simp only [h1, h2, map_mul] at hunit
  norm_num at hunit
  have hn : Complex.normSq ((Q.source j).val 0) = (16/25 : ℝ) := by
    linarith
  have he : (∑ i, star ((Q.source j).val i) * (Q.target j).val i) =
      ((5/4 : ℂ) * star ((Q.source j).val 0)) *
        (∑ i, star (p.val i) * (Q.target j).val i) := by
    norm_num [Fin.sum_univ_succ, p, h1, h2, star_mul, map_ofNat]
    ring
  unfold ground
  rw [he]
  congr 2
  simp only [map_mul, Complex.star_def, Complex.normSq_conj, hn]
  norm_num

private theorem long_cost (Q : Plan rho sigma) : (96/625 : ℝ) ≤ cost Q := by
  have h0 : HasSum (fun j => Q.weight j * Complex.normSq ((Q.target j).val 0))
      (49/100 : ℝ) := by
    simpa [sigma] using entry_diagonal Q.right 0
  have h1 : HasSum (fun j => Q.weight j * Complex.normSq ((Q.target j).val 1))
      (1/2 : ℝ) := by
    simpa [sigma] using entry_diagonal Q.right 1
  have h2 : HasSum (fun j => Q.weight j * Complex.normSq ((Q.target j).val 2))
      (1/100 : ℝ) := by
    simpa [sigma] using entry_diagonal Q.right 2
  have hl : HasSum (fun j => Q.weight j *
      (-(9/25 : ℝ) * Complex.normSq ((Q.target j).val 0) +
        (16/25 : ℝ) * Complex.normSq ((Q.target j).val 1) +
        Complex.normSq ((Q.target j).val 2))) (96/625 : ℝ) := by
    convert ((h0.mul_left (-(9/25 : ℝ))).add (h1.mul_left (16/25 : ℝ))).add h2 using 1
    · funext j
      ring
    · norm_num
  have hp (j : ℕ) :
      Q.weight j * (-(9/25 : ℝ) * Complex.normSq ((Q.target j).val 0) +
        (16/25 : ℝ) * Complex.normSq ((Q.target j).val 1) +
        Complex.normSq ((Q.target j).val 2)) ≤
      Q.weight j * ground (Q.source j) (Q.target j) := by
    rcases eq_or_lt_of_le (Q.nonneg j) with hz | hj
    · simp [← hz]
    · rw [pure_source_ground Q j hj]
      exact mul_le_mul_of_nonneg_left (pointwise (Q.target j)) (Q.nonneg j)
  exact hasSum_le hp hl (cost_summable Q).hasSum

private theorem long_bound : (96/625 : ℝ) ≤ wasserstein rho sigma := by
  apply le_csInf
  · exact ⟨cost longPlan, longPlan, rfl⟩
  · rintro c ⟨Q, rfl⟩
    exact long_cost Q

theorem result : ¬ claim := by
  intro h
  have ht := h 3 rho tau sigma rho_density tau_density sigma_density
  have hs := short_bound
  have hm := middle_bound
  have hl := long_bound
  norm_num at *
  linarith

end D5.S3.Quantum.QuantumChannels.CouplingWassersteinTriangleRefutation
