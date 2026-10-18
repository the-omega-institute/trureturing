/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Nonnegative halfspace combinations reduce to signed two-generator cancellations. -/

/-
proof_shape: halfspace_transfer: content
escape_witness: halfspace_transfer; the explicit positive-negative mass decomposition
  reconstructs the given combination using two-generator cancellation terms.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only)
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 4000000
/- The following shared interfaces are consumed auxiliary declarations, relocated
without changing their namespace or proofs. They supply the live two-row
uniform_spectral_bound and three-row structural_fixed_good / three_row_scalar_bound
proofs. They provide no new admission basis for this existing cone module.
proof_shape: spectralGood_zero: bind-only
proof_shape: spectralGood_add: bind-only
proof_shape: spectralGood_smul: bind-only
proof_shape: spectralGood_of_square: bind-only
proof_shape: spectralGood_square: bind-only
proof_shape: sum_step: bind-only
proof_shape: sum_step_mul: bind-only
proof_shape: mass_synth: bind-only
proof_shape: square_synth: bind-only
proof_shape: spectralGap_nonneg: bind-only
proof_shape: gap_telescope: bind-only
proof_shape: gap_reconstruct: bind-only
proof_shape: sum_mem_of_closed: bind-only
proof_shape: mixture_transfer: bind-only
The norm laws supply the spectral endpoints; sum_step_mul supplies square_synth;
sum_step supplies mass_synth; gap_telescope supplies gap_reconstruct;
sum_mem_of_closed supplies mixture_transfer; mixture_transfer supplies the original
uniform_spectral_bound. The unfinished source-bound audits are tracked by #17891.
-/
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSpectralBound
open Finset

/- Shared norm, step-synthesis, full-gap and mixture identities for the
two-row and three-row spectral consumers. -/
namespace SharedSpectral
noncomputable section
def spectralGood {d : ℕ} (c : ℝ) (x : Fin d → ℝ) : Prop :=
  ‖WithLp.toLp 2 x‖ ≤ c * ∑ i, x i

theorem spectralGood_zero (d : ℕ) (c : ℝ) : spectralGood c (0 : Fin d → ℝ) := by
  simp [spectralGood]

theorem spectralGood_add {d : ℕ} (c : ℝ) (x y : Fin d → ℝ)
    (hx : spectralGood c x) (hy : spectralGood c y) : spectralGood c (x+y) := by
  unfold spectralGood at *
  have he : WithLp.toLp 2 (x+y) = WithLp.toLp 2 x + WithLp.toLp 2 y := rfl
  rw [he]
  calc
    _ ≤ ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖ := norm_add_le _ _
    _ ≤ c*(∑ i,x i) + c*(∑ i,y i) := add_le_add hx hy
    _ = c*(∑ i,(x+y) i) := by simp [Finset.sum_add_distrib,mul_add]

theorem spectralGood_smul {d : ℕ} (c t : ℝ) (x : Fin d → ℝ)
    (ht : 0≤t) (hx : spectralGood c x) : spectralGood c (t • x) := by
  unfold spectralGood at *
  have he : WithLp.toLp 2 (t • x) = t • WithLp.toLp 2 x := rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
  calc
    _ ≤ t*(c*∑ i,x i) := mul_le_mul_of_nonneg_left hx ht
    _ = c*∑ i,(t • x) i := by simp [Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm]

theorem spectralGood_of_square {d : ℕ} (c : ℝ) (x : Fin d → ℝ) (hc : 0≤c)
    (hs : 0≤∑ i,x i) (hb : ∑ i,(x i)^2 ≤ c^2*(∑ i,x i)^2) : spectralGood c x := by
  unfold spectralGood
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc hs)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa [mul_pow] using hb

theorem spectralGood_square {d : ℕ} (c : ℝ) (x : Fin d → ℝ) (hc : 0≤c)
    (hs : 0≤∑ i,x i) (hb : spectralGood c x) : ∑ i,(x i)^2 ≤ c^2*(∑ i,x i)^2 := by
  unfold spectralGood at hb
  have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc hs)).mpr hb
  rw [EuclideanSpace.real_norm_sq_eq] at h
  simpa [mul_pow] using h

def step (d j : ℕ) : Fin d → ℝ := fun k => if k.val<j then 1 else 0

theorem sum_step (d j : ℕ) (hj : j≤d) : ∑ k, step d j k = (j : ℝ) := by
  simp only [step]
  rw [Fin.sum_univ_eq_sum_range (f := fun k : ℕ => if k<j then (1 : ℝ) else 0)]
  rw [sum_ite]
  simp only [sum_const_zero,add_zero,sum_const,mul_one]
  have he : (Finset.range d).filter (fun k => k<j) = Finset.range j := by
    ext k
    simp only [mem_filter,mem_range]
    omega
  rw [he,card_range]
  simp

theorem sum_step_mul (d i j : ℕ) (hi : i≤d) (hj : j≤d) :
    ∑ k, step d i k * step d j k = (min i j : ℕ) := by
  have he : ∀ k, step d i k*step d j k = step d (min i j) k := by
    intro k
    simp only [step,lt_min_iff]
    split_ifs <;> simp_all
  simp_rw [he]
  exact sum_step _ _ (le_trans (min_le_left _ _) hi)

def synth {d m : ℕ} (p : Fin m → ℕ) : (Fin m → ℝ) →ₗ[ℝ] (Fin d → ℝ) := {
  toFun x := ∑ j, x j • step d (p j)
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' t x := by simp [Finset.smul_sum,smul_smul] }

theorem mass_synth {d m : ℕ} (p : Fin m → ℕ) (hp : ∀ j,p j≤d) (x : Fin m → ℝ) :
    ∑ k : Fin d, synth p x k = ∑ j,x j*(p j : ℝ) := by
  simp only [synth,LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← mul_sum,sum_step _ _ (hp j)]

theorem square_synth {d m : ℕ} (p : Fin m → ℕ) (hp : ∀ j,p j≤d) (x : Fin m → ℝ) :
    ∑ k : Fin d, (synth p x k)^2 = ∑ i,∑ j, x i*x j*(min (p i) (p j) : ℕ) := by
  simp only [synth,LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pow_two]
  simp_rw [sum_mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp_rw [show ∀ k, (x i * step d (p i) k)*(x j*step d (p j) k) = (x i*x j)*(step d (p i) k*step d (p j) k) from fun k => by ring]
  rw [← mul_sum,sum_step_mul _ _ _ (hp i) (hp j)]

def extend {d : ℕ} (l : Fin d → ℝ) (j : ℕ) : ℝ := if h:j<d then l ⟨j,h⟩ else 0

def spectralGap {d : ℕ} (l : Fin d → ℝ) (j : Fin d) : ℝ := extend l j.val-extend l (j.val+1)

theorem spectralGap_nonneg {d : ℕ} (l : Fin d → ℝ) (ho : Antitone l) (hn : ∀ j,0≤l j) :
    ∀ j, 0 ≤ spectralGap l j := by
  intro j
  unfold spectralGap extend
  simp only [dif_pos j.isLt]
  split_ifs with h
  · exact sub_nonneg.mpr (ho (by change j.val ≤ j.val+1;omega))
  · simpa using hn j

theorem gap_telescope {d : ℕ} (l : Fin d → ℝ) (a b : ℕ) (hab : a≤b) :
    ∑ j ∈ Ico a b, (extend l j-extend l (j+1)) = extend l a-extend l b := by
  have h := Finset.sum_Ico_sub (f := extend l) hab
  calc
    _ = -(∑ j ∈ Ico a b, (extend l (j+1)-extend l j)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [h];ring

theorem gap_reconstruct {d : ℕ} (l : Fin d → ℝ) :
    (∑ j, spectralGap l j • step d (j.val+1)) = l := by
  ext k
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,step]
  have he : ∀ j : Fin d, spectralGap l j*(if k.val<j.val+1 then 1 else 0) =
      (fun j : ℕ => if k.val≤j then extend l j-extend l (j+1) else 0) j.val := by
    intro j
    simp only [spectralGap]
    by_cases h : k.val≤j.val
    · simp [h,show k.val<j.val+1 from by omega]
    · simp [h,show ¬k.val<j.val+1 from by omega]
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (f := fun j : ℕ => if k.val≤j then extend l j-extend l (j+1) else 0)]
  rw [sum_ite]
  simp only [sum_const_zero,add_zero]
  have hf : (range d).filter (fun j => k.val≤j) = Ico k.val d := by
    ext j
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [hf,gap_telescope l _ _ (le_of_lt k.isLt)]
  simp [extend,k.isLt]


theorem sum_mem_of_closed {I E : Type*} [AddCommMonoid E]
    (Good : E → Prop) (hzero : Good 0) (hadd : ∀ u v, Good u → Good v → Good (u+v))
    (s : Finset I) (f : I → E) (hf : ∀ i ∈ s, Good (f i)) : Good (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hzero
  | @insert i s hi ih =>
    rw [sum_insert hi]
    exact hadd _ _ (hf i (mem_insert_self _ _)) (ih (fun j hj => hf j (mem_insert_of_mem hj)))

theorem mixture_transfer {I E : Type*} [AddCommGroup E] [Module ℝ E]
    (Good : E → Prop) (hzero : Good 0)
    (hadd : ∀ u v, Good u → Good v → Good (u+v))
    (hsmul : ∀ (t : ℝ) u, 0≤t → Good u → Good (t • u))
    (s : Finset I) (hs : s.Nonempty) (x : I → ℝ) (v : I → E) (b : E)
    (hx : ∀ i ∈ s,0≤x i) (hb : ∀ i ∈ s, Good (b+(∑ j ∈ s,x j) • v i)) :
    Good (b+∑ i ∈ s,x i • v i) := by
  classical
  let m := ∑ j ∈ s,x j
  have hm : 0 ≤ m := sum_nonneg hx
  by_cases hz : m=0
  · obtain ⟨i,hi⟩ := hs
    have hxi : ∀ i ∈ s,x i=0 := (sum_eq_zero_iff_of_nonneg hx).mp hz
    have he : (∑ i ∈ s,x i • v i)=0 := sum_eq_zero (fun i hi => by rw [hxi i hi,zero_smul])
    have h := hb i hi
    change Good (b+m • v i) at h
    simpa only [he,hz,zero_smul,add_zero] using h
  · have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
    have hmem : Good (∑ i ∈ s,(x i/m) • (b+m • v i)) := by
      apply sum_mem_of_closed Good hzero hadd s
      intro i hi
      exact hsmul _ _ (div_nonneg (hx i hi) hm) (hb i hi)
    have he : (∑ i ∈ s,(x i/m) • (b+m • v i)) = b+∑ i ∈ s,x i • v i := by
      simp only [smul_add,smul_smul,sum_add_distrib]
      rw [← sum_smul,← sum_div]
      change (m/m) • b + (∑ i ∈ s,(x i/m*m) • v i) = b+∑ i ∈ s,x i • v i
      simp only [div_self hz,one_smul,div_mul_cancel₀ _ hz]
    rwa [he] at hmem


end
end SharedSpectral

end D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSpectralBound


namespace D5.S3.Quantum.Entanglement.AbsolutePPT.HalfspaceConeTransfer
open Finset UniformSpectralBound.SharedSpectral

theorem halfspace_transfer {I E : Type*} [Fintype I] [AddCommGroup E] [Module ℝ E]
    (Good : E → Prop) (hzero : Good 0)
    (hadd : ∀ u v, Good u → Good v → Good (u+v))
    (hsmul : ∀ (t : ℝ) u, 0 ≤ t → Good u → Good (t • u))
    (v : I → E) (a x : I → ℝ) (hx : ∀ i, 0 ≤ x i)
    (ha : 0 ≤ ∑ i, x i * a i)
    (hpos : ∀ i, 0 ≤ a i → Good (v i))
    (hpair : ∀ i j, 0 < a i → a j < 0 → Good ((-a j) • v i + a i • v j)) :
    Good (∑ i, x i • v i) := by

  classical
  let p := univ.filter (fun i => 0 < a i)
  let n := univ.filter (fun i => a i < 0)
  let z := univ.filter (fun i => a i = 0)
  let A := ∑ i ∈ p, x i * a i
  let B := ∑ i ∈ n, x i * (-a i)
  have hp (i) (hi : i ∈ p) : 0 < a i := (mem_filter.mp hi).2
  have hn (i) (hi : i ∈ n) : a i < 0 := (mem_filter.mp hi).2
  have hz (i) (hi : i ∈ z) : a i = 0 := (mem_filter.mp hi).2
  have splitR (f : I → ℝ) :
      ∑ i, f i = (∑ i ∈ p, f i) + (∑ i ∈ n, f i) + ∑ i ∈ z, f i := by
    simp only [p,n,z,sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rcases lt_trichotomy (a i) 0 with h|h|h
    · simp [h,not_lt_of_ge (le_of_lt h),ne_of_lt h]
    · simp [h]
    · simp [h,not_lt_of_ge (le_of_lt h),ne_of_gt h]
  have splitE (f : I → E) :
      ∑ i, f i = (∑ i ∈ p, f i) + (∑ i ∈ n, f i) + ∑ i ∈ z, f i := by
    simp only [p,n,z,sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rcases lt_trichotomy (a i) 0 with h|h|h
    · simp [h,not_lt_of_ge (le_of_lt h),ne_of_lt h]
    · simp [h]
    · simp [h,not_lt_of_ge (le_of_lt h),ne_of_gt h]
  have hAB : B ≤ A := by
    rw [splitR (fun i => x i * a i)] at ha
    have hz0 : (∑ i ∈ z, x i * a i) = 0 := sum_eq_zero (fun i hi => by rw [hz i hi,mul_zero])
    have hB : (∑ i ∈ n, x i * a i) = -B := by simp [B, mul_neg, sum_neg_distrib]
    rw [hz0,hB] at ha
    dsimp only [A]
    linarith
  have hA : 0 ≤ A := sum_nonneg (fun i hi => mul_nonneg (hx i) (le_of_lt (hp i hi)))
  have hB : 0 ≤ B := sum_nonneg (fun i hi => mul_nonneg (hx i) (neg_nonneg.mpr (le_of_lt (hn i hi))))
  have gz : Good (∑ i ∈ z, x i • v i) :=
    sum_mem_of_closed Good hzero hadd z _ (fun i hi => hsmul _ _ (hx i) (hpos i (le_of_eq (hz i hi).symm)))
  by_cases hAz : A = 0
  · have hBz : B = 0 := le_antisymm (by simpa [hAz] using hAB) hB
    have hnx : ∀ i ∈ n, x i = 0 := by
      intro i hi
      have ht : x i * (-a i) = 0 := (sum_eq_zero_iff_of_nonneg (fun j hj => mul_nonneg (hx j) (neg_nonneg.mpr (le_of_lt (hn j hj))))).mp hBz i hi
      exact (mul_eq_zero.mp ht).resolve_right (ne_of_gt (neg_pos.mpr (hn i hi)))
    rw [splitE (fun i => x i • v i)]
    have he : (∑ i ∈ n, x i • v i) = 0 := sum_eq_zero (fun i hi => by rw [hnx i hi,zero_smul])
    rw [he,add_zero]
    apply hadd _ _ _ gz
    exact sum_mem_of_closed Good hzero hadd p _ (fun i hi => hsmul _ _ (hx i) (hpos i (le_of_lt (hp i hi))))
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hres : 0 ≤ 1-B/A := by apply sub_nonneg.mpr; exact (div_le_one hAp).mpr hAB
    have gp : Good ((1-B/A) • (∑ i ∈ p, x i • v i)) := by
      apply hsmul _ _ hres
      exact sum_mem_of_closed Good hzero hadd p _ (fun i hi => hsmul _ _ (hx i) (hpos i (le_of_lt (hp i hi))))
    have gpair : Good (∑ i ∈ p, ∑ j ∈ n, (x i*x j/A) • ((-a j) • v i+a i • v j)) := by
      apply sum_mem_of_closed Good hzero hadd p
      intro i hi
      apply sum_mem_of_closed Good hzero hadd n
      intro j hj
      exact hsmul _ _ (div_nonneg (mul_nonneg (hx i) (hx j)) hA) (hpair i j (hp i hi) (hn j hj))
    have he : (∑ i ∈ p, ∑ j ∈ n, (x i*x j/A) • ((-a j) • v i+a i • v j)) =
        (B/A) • (∑ i ∈ p, x i • v i) + ∑ j ∈ n, x j • v j := by
      simp only [smul_add,smul_smul,sum_add_distrib]
      congr 1
      · simp_rw [show ∀ i j, (x i*x j/A)*(-a j) = (x i/A)*(x j*(-a j)) from fun i j => by ring]
        simp_rw [← sum_smul,← mul_sum]
        rw [smul_sum]
        apply sum_congr rfl
        intro i _
        rw [smul_smul]
        congr 1
        dsimp only [B]
        ring
      · rw [sum_comm]
        apply sum_congr rfl
        intro j _
        simp_rw [show ∀ i, (x i*x j/A)*a i = (x j/A)*(x i*a i) from fun i => by ring]
        rw [← sum_smul,← mul_sum]
        change ((x j/A)*A) • v j = x j • v j
        rw [div_mul_cancel₀ _ hAz]
    rw [he] at gpair
    have gf := hadd _ _ (hadd _ _ gp gpair) gz
    have eq : (1-B/A) • (∑ i ∈ p, x i • v i) +
        ((B/A) • (∑ i ∈ p, x i • v i) + ∑ j ∈ n, x j • v j) + ∑ i ∈ z, x i • v i = ∑ i, x i • v i := by
      rw [← add_assoc,← add_smul]
      simp only [sub_add_cancel,one_smul]
      exact (splitE _).symm
    rwa [eq] at gf

#print axioms halfspace_transfer
end D5.S3.Quantum.Entanglement.AbsolutePPT.HalfspaceConeTransfer
