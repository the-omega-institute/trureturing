/- GID: D5/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetFiniteIntegralDefect
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Integral kernel, image and cokernel of identity plus the original reset transition. -/
import D5.S1.Recurrence.FiniteCompanionDefect
import D5.S3.ConceptDynamics.Coding.ResetNativeOddObstruction
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect

open Multiplicative
open scoped BigOperators Matrix
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
  (VertexModule integerMatrix transition)
open D5.S1.Recurrence.FiniteCompanionDefect

private abbrev tau : Sign := ofAdd true
private abbrev RingRow := MonoidAlgebra ℤ Sign

private theorem tau_inv : tau⁻¹ = tau := by decide
private theorem tau_mul : tau * tau = (1 : Sign) := by decide
private theorem tau_ne_one : tau ≠ (1 : Sign) := by decide

/-- Both integer coefficients are swapped by actual right multiplication by tau. -/
def resetFlip : RingRow →+ RingRow where
  toFun x := x * MonoidAlgebra.single tau 1
  map_zero' := zero_mul _
  map_add' x y := add_mul x y _

/-- Identity plus the original integer right-row transition. -/
def resetDefect (q : ℕ) : Module.End ℤ (VertexModule Sign q) :=
  LinearMap.id + transition (resetMatrix q)

theorem flip_coeff (x : RingRow) (h : Sign) :
    (resetFlip x).coeff h = x.coeff (h * tau) := by
  change (x * MonoidAlgebra.single tau 1).coeff h = _
  simp only [MonoidAlgebra.coeff_mul_single_apply, mul_one, tau_inv]

theorem sign_cases (h : Sign) : h = 1 ∨ h = tau := by
  rcases Bool.dichotomy (toAdd h) with hb | hb
  · exact Or.inl (congrArg (fun b : Bool => (ofAdd b : Sign)) hb)
  · exact Or.inr (congrArg (fun b : Bool => (ofAdd b : Sign)) hb)

/-- Exact identification of the original right-row defect with the additive companion. -/
theorem reset_defect_companion (n : ℕ) (v : VertexModule Sign (n + 1)) :
    resetDefect (n + 1) v = companion resetFlip n v := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · change v 0 + transition (resetMatrix (n + 1)) v 0 =
      v 0 + resetFlip (∑ i, v i)
    simpa only [resetLabel, oddTau, resetFlip, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      using congrArg (v 0 + ·) (transition_zero n v)
  · change v k.succ + transition (resetMatrix (n + 1)) v k.succ =
      v k.succ + v k.castSucc
    exact congrArg (v k.succ + ·) (transition_succ n v k)

/-- The primitive integer obstruction: identity coefficient minus tau coefficient,
summed over even suffix indices. -/
def resetCharacter (q : ℕ) : VertexModule Sign q →ₗ[ℤ] ℤ where
  toFun y := ∑ i : Fin q, if Even i.val then (y i).coeff 1 - (y i).coeff tau else 0
  map_add' y z := by
    simp only [Pi.add_apply, MonoidAlgebra.coeff_add, Finsupp.add_apply,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; split_ifs <;> ring
  map_smul' c y := by
    simp only [Pi.smul_apply, MonoidAlgebra.coeff_smul_apply, smul_eq_mul,
      Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _; split_ifs <;> ring

private theorem residual_character (n : ℕ) (ho : Odd (n + 1))
    (y : VertexModule Sign (n + 1)) :
    ((codomainEquiv resetFlip n y).1).coeff 1 -
      ((codomainEquiv resetFlip n y).1).coeff tau = resetCharacter (n + 1) y := by
  classical
  change (y 0 - resetFlip (tailSum n (fun j => y j.succ))).coeff 1 -
    (y 0 - resetFlip (tailSum n (fun j => y j.succ))).coeff tau = _
  simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, flip_coeff, one_mul]
  have htt : tau * tau = (1 : Sign) := by decide
  rw [htt]
  simp only [tailSum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  have hs : (∑ j : Fin n, ((if Odd (n - j.val) then y j.succ else 0).coeff 1 -
      (if Odd (n - j.val) then y j.succ else 0).coeff tau)) =
      ∑ j : Fin n, if Even (j.val + 1) then
        (y j.succ).coeff 1 - (y j.succ).coeff tau else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    have hp : Odd (n - j.val) ↔ Even (j.val + 1) := by
      have hj := j.isLt
      simp only [Nat.odd_iff, Nat.even_iff] at *
      omega
    simp only [hp]
    split_ifs <;> simp
  change (y 0).coeff 1 - (∑ j : Fin n, (if Odd (n - j.val) then y j.succ else 0).coeff tau) -
    ((y 0).coeff tau - (∑ j : Fin n, (if Odd (n - j.val) then y j.succ else 0).coeff 1)) = _
  change _ = ∑ i : Fin (n + 1), if Even i.val then (y i).coeff 1 - (y i).coeff tau else 0
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Even.zero, if_true, Fin.val_succ]
  rw [← hs, Finset.sum_sub_distrib]
  ring

private theorem residual_eliminate (n : ℕ) (v : VertexModule Sign (n + 1)) :
    codomainEquiv resetFlip n (resetDefect (n + 1) v) =
      ((domainEquiv n v).1 + resetFlip
        (if Odd (n + 1) then (domainEquiv n v).1 else 0), (domainEquiv n v).2) := by
  rw [reset_defect_companion]
  exact eliminate resetFlip n v

/-- Explicit integral solver: solve the residual head, then all adjacent tails.
The odd branch uses just the identity basis vector, never half an eigenvector. -/
def resetPreimage (q : ℕ) (hq : 0 < q) (y : VertexModule Sign q) : VertexModule Sign q :=
  match q with
  | 0 => False.elim (Nat.not_lt_zero 0 hq)
  | n + 1 =>
      let z := codomainEquiv resetFlip n y
      (domainEquiv n).symm
        (if Odd (n + 1) then MonoidAlgebra.single 1 (z.1.coeff 1) else z.1, z.2)

/-- Every positive even carrier has exactly one integral solution, supplied by
resetPreimage. No divisibility or rational extension is required. -/
theorem reset_even_unique_solution (q : ℕ) (hq : 0 < q) (he : Even q)
    (y : VertexModule Sign q) :
    resetDefect q (resetPreimage q hq y) = y ∧
      ∀ v, resetDefect q v = y ↔ v = resetPreimage q hq y := by
  cases q with
  | zero => omega
  | succ n =>
      have hn : ¬ Odd (n + 1) := by simp only [Nat.odd_iff, Nat.even_iff] at *; omega
      have hsolve : resetDefect (n + 1) (resetPreimage (n + 1) hq y) = y := by
        apply (codomainEquiv resetFlip n).injective
        rw [residual_eliminate]
        simp only [resetPreimage, hn, if_false, AddEquiv.apply_symm_apply,
          map_zero, add_zero, Prod.mk.eta]
      refine ⟨hsolve, fun v => ⟨fun hv => ?_, fun hv => hv ▸ hsolve⟩⟩
      apply (domainEquiv n).injective
      have hh := congrArg (codomainEquiv resetFlip n) (hv.trans hsolve.symm)
      simpa only [residual_eliminate, hn, if_false, map_zero, add_zero,
        Prod.mk.eta] using hh

private theorem odd_preimage (n : ℕ) (ho : Odd (n + 1)) (y : VertexModule Sign (n + 1))
    (hy : resetCharacter (n + 1) y = 0) :
    resetDefect (n + 1) (resetPreimage (n + 1) (Nat.succ_pos n) y) = y := by
  classical
  apply (codomainEquiv resetFlip n).injective
  rw [residual_eliminate]
  simp only [resetPreimage, ho, if_true, AddEquiv.apply_symm_apply]
  apply Prod.ext
  · let z := (codomainEquiv resetFlip n y).1
    have hz : z.coeff 1 = z.coeff tau := by
      have hc := residual_character n ho y
      rw [hy] at hc
      exact sub_eq_zero.mp hc
    change MonoidAlgebra.single 1 (z.coeff 1) +
      resetFlip (MonoidAlgebra.single 1 (z.coeff 1)) = z
    ext h
    rcases sign_cases h with rfl | rfl <;>
      simp [flip_coeff, MonoidAlgebra.coeff_single, hz, tau_mul]
  · rfl

/-- The obstruction is onto the integers, including the deterministic q=1 boundary. -/
theorem reset_character_surjective (q : ℕ) (hq : 0 < q) :
    Function.Surjective (resetCharacter q) := by
  cases q with
  | zero => omega
  | succ n =>
      intro k
      refine ⟨Fin.cons (MonoidAlgebra.single (1 : Sign) k) (0 : Fin n → RingRow), ?_⟩
      simp [resetCharacter, Fin.sum_univ_succ, MonoidAlgebra.coeff_single]

/-- Exact constructive image criterion on the original two-coefficient lattice. -/
theorem reset_odd_image (q : ℕ) (hq : 0 < q) (ho : Odd q)
    (y : VertexModule Sign q) :
    (∃ v, resetDefect q v = y) ↔ resetCharacter q y = 0 := by
  cases q with
  | zero => omega
  | succ n =>
      constructor
      · rintro ⟨v, rfl⟩
        rw [← residual_character n ho, show
          (codomainEquiv resetFlip n (resetDefect (n + 1) v)).1 =
            v 0 + resetFlip (v 0) from by
              have hh := congrArg Prod.fst (residual_eliminate n v)
              change _ = v 0 + resetFlip (if Odd (n + 1) then v 0 else 0) at hh
              simpa only [ho, if_true] using hh]
        simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, flip_coeff, one_mul]
        have htt : tau * tau = (1 : Sign) := by decide
        rw [htt]; ring
      · intro hy
        exact ⟨resetPreimage (n + 1) (Nat.succ_pos n) y, odd_preimage n ho y hy⟩

/-- The entire odd kernel is the primitive cyclic lattice generated by the
existing resetOddVector, with a unique integer coefficient. -/
theorem reset_odd_kernel (q : ℕ) (hq : 0 < q) (ho : Odd q)
    (v : VertexModule Sign q) :
    resetDefect q v = 0 ↔ ∃! k : ℤ, v = k • resetOddVector q := by
  cases q with
  | zero => omega
  | succ n =>
      have hw : resetDefect (n + 1) (resetOddVector (n + 1)) = 0 := by
        simp only [resetDefect, LinearMap.add_apply, LinearMap.id_apply,
          reset_odd_transition (n + 1) hq ho, add_neg_cancel]
      have hc (k : ℤ) : ((k • resetOddVector (n + 1)) 0).coeff 1 = k := by
        change (k • (resetOddVector (n + 1) 0)).coeff 1 = k
        rw [MonoidAlgebra.coeff_smul_apply]
        simp [resetOddVector, MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single]
      constructor
      · intro hv
        have hvcoord := residual_eliminate n v
        rw [hv, map_zero] at hvcoord
        have hhead : v 0 + resetFlip (v 0) = 0 := by
          have hh := (congrArg Prod.fst hvcoord).symm
          change v 0 + resetFlip (if Odd (n + 1) then v 0 else 0) = 0 at hh
          simpa only [ho, if_true] using hh
        have htail : (domainEquiv n v).2 = 0 :=
          (congrArg Prod.snd hvcoord).symm
        let k : ℤ := (v 0).coeff 1
        have ha : v 0 = k • (resetOddVector (n + 1) 0) := by
          have hx := congrArg (fun x : RingRow => x.coeff 1) hhead
          have hx' : (v 0).coeff 1 + (v 0).coeff tau = 0 := by
            simpa only [MonoidAlgebra.coeff_add, Finsupp.add_apply, flip_coeff,
              one_mul, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hx
          have hcw (h : Sign) : (k • resetOddVector (n + 1) 0).coeff h =
              k * (if h = 1 then 1 else if h = tau then -1 else 0) := by
            rw [MonoidAlgebra.coeff_smul_apply]
            simp only [resetOddVector, Fin.val_zero, pow_zero, one_smul,
              MonoidAlgebra.coeff_sub, Finsupp.sub_apply, MonoidAlgebra.coeff_single,
              Finsupp.single_apply, smul_eq_mul]
            rcases sign_cases h with rfl | rfl <;> simp [Ne.symm tau_ne_one]
          ext h
          rw [hcw]
          rcases sign_cases h with rfl | rfl
          · simp [k]
          · simp [k]; omega
        refine ⟨k, ?_, ?_⟩
        · apply (domainEquiv n).injective
          apply Prod.ext
          · exact ha
          · rw [htail]
            have hkzero : resetDefect (n + 1) (k • resetOddVector (n + 1)) = 0 := by
              rw [map_smul, hw, smul_zero]
            have ht := congrArg Prod.snd (residual_eliminate n (k • resetOddVector (n + 1)))
            rw [hkzero, map_zero] at ht
            exact ht
        · intro l hl
          have hh := congrArg (fun u : VertexModule Sign (n + 1) => (u 0).coeff 1) hl
          rw [hc] at hh
          exact hh.symm
      · rintro ⟨k, rfl, _⟩
        rw [map_smul, hw, smul_zero]

/-- Every solution is the chosen particular solution plus a unique multiple of
resetOddVector. This also specifies failure when the obstruction is nonzero. -/
theorem reset_odd_all_solutions (q : ℕ) (hq : 0 < q) (ho : Odd q)
    (y : VertexModule Sign q) (hy : resetCharacter q y = 0)
    (v : VertexModule Sign q) :
    resetDefect q v = y ↔
      ∃! k : ℤ, v = resetPreimage q hq y + k • resetOddVector q := by
  have hs : resetDefect q (resetPreimage q hq y) = y := by
    cases q with
    | zero => omega
    | succ n => exact odd_preimage n ho y hy
  have hv : resetDefect q v = y ↔ resetDefect q (v - resetPreimage q hq y) = 0 := by
    rw [map_sub, hs, sub_eq_zero]
  rw [hv, reset_odd_kernel q hq ho]
  apply existsUnique_congr
  intro k
  constructor
  · intro hk
    exact (sub_eq_iff_eq_add.mp hk).trans (add_comm _ _)
  · intro hk
    exact sub_eq_iff_eq_add.mpr (hk.trans (add_comm _ _))

/-- The image is the kernel of a primitive integer character. -/
theorem reset_odd_range (q : ℕ) (hq : 0 < q) (ho : Odd q) :
    LinearMap.range (resetDefect q) = LinearMap.ker (resetCharacter q) := by
  ext y
  exact reset_odd_image q hq ho y

/-- The full integral odd cokernel is Z, with no hidden order-two torsion. -/
def resetOddCokernelEquiv (q : ℕ) (hq : 0 < q) (ho : Odd q) :
    (VertexModule Sign q ⧸ LinearMap.range (resetDefect q)) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (reset_odd_range q hq ho)).trans
    ((resetCharacter q).quotKerEquivOfSurjective (reset_character_surjective q hq))

end D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
