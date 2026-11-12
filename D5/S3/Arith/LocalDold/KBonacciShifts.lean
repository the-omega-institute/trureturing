/- GID: D5/S3/Arith/LocalDold/KBonacciShifts
   generality: G
   mirror-B: D5/B/S3/Arith/LocalDold/KBonacciShifts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive k-bonacci seeds with an adjacent doubling admit no local Dold repair, at any shift. -/
import D5.S3.Arith.LocalDold.BackwardZero
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.LocalDold.KBonacciShifts
open D5.S3.Arith.LocalDold.BackwardZero
noncomputable section

/-- The bilateral k-bonacci equation, including the backwards extension. -/
def Recurs (k : ℕ) (a : ℤ → ℤ) : Prop :=
  ∀ t : ℤ, a (t+k) = ∑ j : Fin k, a (t+(j:ℕ))

private def step (n : ℕ) : (Fin (n+1) → ℤ) ≃ₗ[ℤ] (Fin (n+1) → ℤ) where
  toFun v := Fin.snoc (fun j => v j.succ) (∑ j, v j)
  invFun v := Fin.cons (v (Fin.last n) - ∑ j : Fin n, v j.castSucc)
    (fun j => v j.castSucc)
  left_inv v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Fin.sum_univ_succ]
    · simp
  right_inv v := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.sum_univ_succ]
    · simp
  map_add' v w := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [Finset.sum_add_distrib]
  map_smul' c v := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [Finset.mul_sum]

private def companion (n : ℕ) : Matrix.GeneralLinearGroup (Fin (n+1)) ℤ :=
  Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv (step n))

private theorem companion_action (n : ℕ) (v : Fin (n+1) → ℤ) :
    (companion n).val.mulVec v = step n v := by
  change (LinearMap.toMatrix' (step n).toLinearMap).mulVec v = _
  rw [← Matrix.toLin'_apply,Matrix.toLin'_toMatrix']
  rfl

private def state (n : ℕ) (a : ℤ → ℤ) (t : ℤ) : Fin (n+1) → ℤ :=
  fun j => a (t+(j:ℕ))

private theorem state_step (n : ℕ) (a : ℤ → ℤ) (ha : Recurs (n+1) a) (t : ℤ) :
    step n (state n a t) = state n a (t+1) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [step,LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,Fin.snoc_last,state]
    change (∑ j : Fin (n+1), a (t+(j:ℕ))) = a (t+1+(Fin.last n:ℕ))
    rw [← ha]
    congr 1
    simp
    ring
  · simp only [step,LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,Fin.snoc_castSucc,state]
    change a (t+(j.succ:ℕ)) = a (t+1+(j.castSucc:ℕ))
    congr 1
    simp
    ring

private theorem state_orbit (n : ℕ) (a : ℤ → ℤ) (ha : Recurs (n+1) a)
    (t : ℤ) (q : ℕ) :
    ((companion n).val^q).mulVec (state n a t) = state n a (t+q) := by
  induction q with
  | zero => simp [state]
  | succ q ih =>
    rw [pow_succ',← Matrix.mulVec_mulVec,ih,companion_action,state_step n a ha]
    congr 1
    push_cast
    ring

private theorem recurrence_difference (n : ℕ) (a : ℤ → ℤ) (ha : Recurs (n+1) a)
    (t : ℤ) : a (t+(n+1)+1) = 2*a (t+(n+1))-a t := by
  have h0 := ha t
  have h1 := ha (t+1)
  rw [Fin.sum_univ_succ] at h0
  rw [Fin.sum_univ_castSucc] at h1
  have hs : (∑ j : Fin n, a (t+(j.succ:ℕ))) =
      ∑ j : Fin n, a (t+1+(j.castSucc:ℕ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    simp
    ring
  simp only [Fin.val_zero, Nat.cast_zero,add_zero] at h0
  simp only [Fin.val_last] at h1
  rw [hs] at h0
  push_cast at h0 h1 ⊢
  have he : t+1+(n+1) = t+(n+1)+1 := by ring
  have he' : t+1+(n:ℤ) = t+(n+1) := by push_cast; ring
  rw [he,he'] at h1
  linarith

private theorem forward_positive (n : ℕ) (a : ℤ → ℤ) (ha : Recurs (n+1) a)
    (hseed : ∀ i : ℕ, 0 < i → i ≤ n+1 → 0<a i) :
    ∀ i : ℕ, 0 < i → 0<a i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases hik : i ≤ n+1
    · exact hseed i hi hik
    · have ht : 0 < i-(n+1) := by omega
      have he : ((i-(n+1):ℕ):ℤ)+((n+1:ℕ):ℤ) = i := by omega
      rw [← he,ha]
      apply Finset.sum_pos
      · intro j hj
        have hjlt := j.isLt
        have hjp : 0 < i-(n+1)+(j:ℕ) := by omega
        have hjn : i-(n+1)+(j:ℕ) < i := by omega
        simpa only [Nat.cast_add] using ih _ hjn hjp
      · exact Finset.univ_nonempty

/-- Every positive-seeded bilateral k-bonacci recurrence with an adjacent
seed doubling has no fixed positive local Dold repair at any nonnegative
shift. The backward zero is deduced from the recurrence, not assumed. -/
theorem adjacent_doubling_no_repair (n : ℕ) (a : ℤ → ℤ)
    (ha : Recurs (n+1) a)
    (hseed : ∀ i : ℕ, 0 < i → i ≤ n+1 → 0<a i)
    (i : ℕ) (hi : 0 < i) (hik : i < n+1) (hd : a (i+1) = 2*a i)
    (p : ℕ) (hp : p.Prime) :
    ∀ s c : ℕ, 0 < c → ¬ Dold (fun q => (c:ℤ)*localPart p (fun q => a q) (q+s)) := by
  let A := (companion n).val
  let h := n+1-i
  let t : ℤ := -(h:ℤ)
  let y := state n a t
  let l : Fin (n+1) → ℤ := Pi.single 0 1
  have hz : a t = 0 := by
    have hr := recurrence_difference n a ha t
    have he : t+(n+1) = i := by dsimp [t,h]; omega
    rw [he,hd] at hr
    linarith
  have hzero : dotProduct l y = 0 := by
    simpa [l,y,state,single_one_dotProduct] using hz
  have hobs : ∀ q, observation A y l (q+h) = a q := by
    intro q
    dsimp [observation,A,y]
    rw [state_orbit n a ha]
    simp only [l,single_one_dotProduct,state,Fin.val_zero,Nat.cast_zero,add_zero]
    congr 1
    dsimp [t]
    push_cast
    ring
  have hdet : ¬ (p:ℤ) ∣ A.det := by
    have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp (companion n).isUnit
    intro hdv
    have hunit := isUnit_of_dvd_unit hdv hu
    exact (Nat.prime_iff_prime_int.mp hp).not_unit hunit
  have hpos := forward_positive n a ha hseed
  intro s c hc hD
  have hns : ∀ q : ℕ, 0 < q → observation A y l (q+(h+s)) ≠ 0 := by
    intro q hq
    rw [show q+(h+s)=(q+s)+h by omega,hobs]
    exact (hpos (q+s) (by omega)).ne'
  apply kernel_orbit_no_repair A y l (h+s) (by dsimp [h]; omega) hzero p hp hdet hns c hc
  unfold Dold mobiusSum at *
  simpa only [show ∀ q : ℕ, observation A y l (q+(h+s)) = a ((q+s:ℕ):ℤ) from
    fun q => by rw [show q+(h+s)=(q+s)+h by omega,hobs],localPart] using hD

/-- The seeds 1,...,1,2 of every order k>=3, and all their nonnegative
shifts, have empty local almost-Dold prime sets. -/
theorem one_two_seeds_no_repair (k : ℕ) (hk : 3 ≤ k) (a : ℤ → ℤ)
    (ha : Recurs k a)
    (hones : ∀ i : ℕ, 0 < i → i < k → a i=1) (htwo : a k=2)
    (p : ℕ) (hp : p.Prime) :
    ∀ s c : ℕ, 0 < c → ¬ Dold (fun q => (c:ℤ)*localPart p (fun q => a q) (q+s)) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  apply adjacent_doubling_no_repair n a ha ?_ n (by omega) (by omega) ?_ p hp
  · intro i hi hik
    by_cases hin : i < n+1
    · rw [hones i hi hin]; norm_num
    · have : i=n+1 := by omega
      rw [this,htwo]; norm_num
  · have ht : a ((n:ℤ)+1)=2 := by exact_mod_cast htwo
    rw [ht,hones n (by omega) (by omega)]
    norm_num

end
end D5.S3.Arith.LocalDold.KBonacciShifts
