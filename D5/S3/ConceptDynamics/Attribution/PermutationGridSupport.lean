/- GID: D5/S3/ConceptDynamics/Attribution/PermutationGridSupport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/PermutationGridSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp finite seed budgets for exact calibration under all outcome permutations. -/

import D5.S3.ConceptDynamics.Attribution.GridReadoutConstruction
import D5.S3.Combinatorics.Partitions.StabilizerFactorialDivisibility
import D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness
import D5.S3.ConceptDynamics.Attribution.ThreeOutcomeGridSupport
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic.Group

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.PermutationGridSupport

open Finset
open scoped Nat
open PermutationGrid (Profile relabel)
open D5.S3.ConceptDynamics.Attribution.GridReadoutConstruction (law_of_scaled_block_allocations)

private def flag {I : Type*} [DecidableEq I] (a i : I) : ℕ := if i = a then 0 else 1

private theorem flag_stabilizer {I : Type*} [DecidableEq I] (a : I) :
    ProfileStabilizer.Preserving (flag a) = MulAction.stabilizer (Equiv.Perm I) a := by
  ext g
  change flag a ∘ g = flag a ↔ g a = a
  constructor
  · intro preserves
    have eq := congrFun preserves a
    change flag a (g a) = flag a a at eq
    by_contra h
    simp [flag, h] at eq
  · intro fixes
    funext i
    change flag a (g i) = flag a i
    have eq : g i = a ↔ i = a := g.injective.eq_iff' fixes
    simp [flag, eq]

private theorem flag_size {I : Type*} [Fintype I] [DecidableEq I] (a b : I) (ne : b ≠ a) :
    ProfileStabilizer.size (flag a) (ProfileStabilizer.groupOf (flag a) b) = Fintype.card I - 1 := by
  have eq (i : I) : flag a i = flag a b ↔ i ≠ a := by
    by_cases hi : i = a <;> simp [flag, hi, ne]
  change Fintype.card {i : I // flag a i = flag a b} = _
  let e : {i : I // flag a i = flag a b} ≃ {i : I // i ≠ a} :=
    Equiv.subtypeEquiv (Equiv.refl I) eq
  rw [Fintype.card_congr e]
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

private theorem flag_card {I : Type*} [Fintype I] [DecidableEq I] (a : I) :
    Fintype.card (ProfileStabilizer.Preserving (flag a)) = (Fintype.card I - 1)! := by
  classical
  let k := Fintype.card I
  have kpos : 0 < k := Fintype.card_pos_iff.mpr ⟨a⟩
  let _ : Fintype (MulAction.orbit (Equiv.Perm I) a) := Fintype.ofFinite _
  have orbitAll : MulAction.orbit (Equiv.Perm I) a = Set.univ := MulAction.orbit_eq_univ (Equiv.Perm I) a
  have orbitCard : Fintype.card (MulAction.orbit (Equiv.Perm I) a) = k :=
    Fintype.card_congr ((Set.equivOfEq orbitAll).trans (Equiv.Set.univ I))
  have stabCard : Fintype.card (MulAction.stabilizer (Equiv.Perm I) a) = (k - 1)! := by
    apply Nat.eq_of_mul_eq_mul_left kpos
    have c := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Equiv.Perm I) a
    rw [orbitCard, Fintype.card_perm] at c
    rw [c]
    exact (Nat.mul_factorial_pred kpos.ne').symm
  let e : ProfileStabilizer.Preserving (flag a) ≃ MulAction.stabilizer (Equiv.Perm I) a :=
    Set.equivOfEq (congrArg (fun H : Subgroup (Equiv.Perm I) => (H : Set (Equiv.Perm I)))
      (flag_stabilizer a))
  exact (Fintype.card_congr e).trans stabCard

private theorem flag_inner_card {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I) (ne : b ≠ a) (two : 2 ≤ Fintype.card I) :
    Fintype.card (MulAction.stabilizer (ProfileStabilizer.Preserving (flag a)) b) = (Fintype.card I - 2)! := by
  let k := Fintype.card I
  apply Nat.eq_of_mul_eq_mul_left (show 0 < k - 1 by omega)
  have eq := ProfileStabilizer.stabilizer_count_product (flag a) b
  rw [flag_size a b ne, flag_card] at eq
  rw [eq]
  simpa only [show k - 1 - 1 = k - 2 by omega] using
    (Nat.mul_factorial_pred (n := k - 1) (by omega)).symm

private def tied {I : Type*} [Fintype I] [DecidableEq I] (a : I) {m : ℕ}
    (level : ℕ) (bound : (Fintype.card I - 1) * level ≤ m) : Profile I m :=
  ⟨fun i => if i = a then m - (Fintype.card I - 1) * level else level, by
    classical
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    simp only [ite_true]
    have sum : (∑ i ∈ (Finset.univ : Finset I).erase a, if i = a then
        m - (Fintype.card I - 1) * level else level) =
        ∑ _i ∈ (Finset.univ : Finset I).erase a, level := by
      exact Finset.sum_congr rfl fun i hi => ite_eq_right (Finset.ne_of_mem_erase hi)
    rw [sum, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      nsmul_eq_mul, Nat.cast_id, Nat.add_sub_of_le bound]⟩

/-- Tied profiles require a whole interval of integer masses from one family of bounded orbit digits. -/
theorem weighted_orbit_spectrum {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]
    [MulAction (Equiv.Perm I) S] (two : 2 ≤ Fintype.card I)
    {m : ℕ} (free : ∀ s : S, MulAction.stabilizer (Equiv.Perm I) s = ⊥)
    (w : S → ℝ)
    (invariant : ∀ (g : Equiv.Perm I) s, w (g • s) = w s)
    (f : Profile I m → S → I)
    (calibrated : ∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ))
    (covariant : ∀ g p s, f (relabel g p) (g • s) = g (f p s)) :
    ∃ (r : ℕ) (weights : Fin r → ℝ),
      Fintype.card S = (Fintype.card I)! * r ∧
      ((Fintype.card I)! : ℝ) * (∑ j, weights j) =
        ((Fintype.card I-2)! : ℝ) * ∑ s, w s ∧
      ∀ l : Fin (m/(Fintype.card I-1)+1), ∃ d : Fin r → Fin (Fintype.card I+1),
        ∑ j, (d j).val * weights j = (l.val : ℝ) := by
  classical
  let k := Fintype.card I
  have kpos : 0 < k := by omega
  have prevPos : 0 < k-1 := by omega
  let _ : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨b, a, distinct⟩ := exists_pair_ne I
  let P := Equiv.Perm I
  let H := ProfileStabilizer.Preserving (flag a)
  let J := MulAction.orbitRel.Quotient P S
  let _ : Fintype J := Fintype.ofFinite J
  let e := (MulAction.selfEquivOrbitsQuotientProd free).symm
  have cardS : Fintype.card S = k ! * Fintype.card J := by
    simpa only [Fintype.card_prod, Fintype.card_perm, Nat.mul_comm] using Fintype.card_congr e.symm
  let L := Fin (m/(k-1)+1)
  let p (l : L) : Profile I m := tied a l.val (Nat.le_trans
    (Nat.mul_le_mul_left (k-1) (show l.val ≤ m/(k-1) from Nat.lt_succ_iff.mp l.isLt))
    (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _))
  have tieVal (l : L) : (p l).val b = l.val := ite_eq_right distinct
  have fixed (l : L) (g : H) : relabel g.val (p l) = p l := by
    apply Subtype.ext
    funext i
    have ga : g.val a = a := by
      have h : g.val ∈ ProfileStabilizer.Preserving (flag a) := g.property
      rw [flag_stabilizer] at h
      exact MulAction.mem_stabilizer_iff.mp h
    have eq : g.val.symm i = a ↔ i = a := by rw [Equiv.symm_apply_eq, ga]
    change (if g.val.symm i = a then m-(k-1)*l.val else l.val) =
      if i = a then m-(k-1)*l.val else l.val
    simp only [eq]
  have permQuot : Fintype.card P / Fintype.card H = k := by
    change (Fintype.card (Equiv.Perm I)) / Fintype.card H = k
    change (Fintype.card (Equiv.Perm I)) / Fintype.card (ProfileStabilizer.Preserving (flag a)) = k
    rw [Fintype.card_perm, flag_card]
    change k ! / (k-1)! = k
    have fact : k ! = k * (k-1)! := (Nat.mul_factorial_pred kpos.ne').symm
    rw [fact, Nat.mul_div_cancel _ (Nat.factorial_pos _)]
  have chooseDigit (l : L) (j : J) :
      ∃ d : Fin (k+1),
        (univ.filter fun g : P => f (p l) (g • j.out) = b).card =
          d.val * (k-2)! := by
    let F (g : P) := f (p l) (g • j.out)
    have equivariant (h : H) (g : P) : F (h • g) = h • F g := by
      change f (p l) ((h.val * g) • j.out) = h.val (f (p l) (g • j.out))
      simpa only [fixed l h, mul_smul] using covariant h.val (p l) (g • j.out)
    obtain ⟨d, le, eq⟩ := FreeActionAllocations.equivariant_fiber_size
      (ProfileStabilizer.regular_subgroup_free (flag a)) F equivariant b
    rw [permQuot] at le
    rw [flag_inner_card a b distinct two, Finset.sum_boole] at eq
    exact ⟨⟨d, Nat.lt_succ_of_le le⟩, eq⟩
  choose digit count using chooseDigit
  have weighted (l : L) :
      ∑ j : J, ((digit l j).val : ℝ) * ((k-2)! : ℝ) * w j.out = (l.val : ℝ) := by
    have eq := calibrated (p l) b
    rw [tieVal] at eq
    rw [← e.sum_comp, Fintype.sum_prod_type] at eq
    rw [← eq]
    apply Finset.sum_congr rfl
    intro j _
    change ((digit l j).val : ℝ) * ((k-2)! : ℝ) * w j.out =
      ∑ g : P, (if f (p l) (g • j.out) = b then w (g • j.out) else 0)
    simp only [invariant, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [count l j, Nat.cast_mul]
  let eJ := Fintype.equivFin J
  let weight (j : J) := ((k-2)! : ℝ) * w j.out
  have reindexed : (∑ s, w s) = ((k ! : ℕ) : ℝ) * ∑ j : J, w j.out := by
    rw [← e.sum_comp, Fintype.sum_prod_type]
    simp only [show ∀ (j : J) (g : P), e (j,g) = g • j.out from fun _ _ => rfl,
      invariant, Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul,
      ← Finset.mul_sum]
    rfl
  refine ⟨Fintype.card J, weight ∘ eJ.symm, cardS, ?_, ?_⟩
  · simp only [Function.comp_apply]
    rw [Equiv.sum_comp eJ.symm weight, reindexed]
    simp only [weight, ← Finset.mul_sum]
    ring
  · intro l
    refine ⟨digit l ∘ eJ.symm, ?_⟩
    have h := Equiv.sum_comp eJ.symm (fun j => ((digit l j).val : ℝ) * weight j)
    calc
      _ = ∑ j : J, ((digit l j).val : ℝ) * weight j := h
      _ = _ := by simpa only [weight, mul_assoc] using weighted l

private theorem grid_lower {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]
    [MulAction (Equiv.Perm I) S] (two : 2 ≤ Fintype.card I)
    {m : ℕ} (divisible : ∀ d : ℕ, 0 < d → d ≤ Fintype.card I → d ∣ m)
    (w : S → ℝ) (positive : ∀ s, 0 < w s)
    (invariant : ∀ (g : Equiv.Perm I) s, w (g • s) = w s)
    (f : Profile I m → S → I)
    (calibrated : ∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ))
    (covariant : ∀ g p s, f (relabel g p) (g • s) = g (f p s)) :
    ∃ r, Fintype.card S = (Fintype.card I)! * r ∧
      m / (Fintype.card I - 1) + 1 ≤ (Fintype.card I + 1) ^ r := by
  classical
  have free :=
    PermutationGrid.trivial_seed_stabilizers divisible w positive f calibrated covariant
  obtain ⟨r, weights, support, _, cover⟩ := weighted_orbit_spectrum two free w invariant f calibrated covariant
  choose digits value using cover
  have inj : Function.Injective digits := by
    intro x y same
    have equality : (x.val : ℝ) = (y.val : ℝ) := by
      rw [← value x, ← value y, same]
    exact Fin.ext (by exact_mod_cast equality)
  exact ⟨r, support, by
    simpa only [Fintype.card_fin, Fintype.card_fun] using Fintype.card_le_of_injective digits inj⟩


open Finset
open scoped Nat
open PermutationGrid (Profile relabel)

/-- A positive invariant seed law and pointwise equivariant readout that reproduce the
coordinates of every integer profile normalized by the denominator. -/
def CalibratingLaw {k m : ℕ} (S : Type*) [Fintype S] [MulAction (Equiv.Perm (Fin k)) S]
    (w : S → ℝ) (f : Profile (Fin k) m → S → Fin k) : Prop :=
  (∀ s, 0 < w s) ∧ (∑ s, w s = 1) ∧
    (∀ (g : Equiv.Perm (Fin k)) s, w (g • s) = w s) ∧
    (∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ) / m) ∧
    (∀ g p s, f (relabel g p) (g • s) = g (f p s))

/-- On the complete k - outcome grid, the capacity of a budget of n regular seed orbits
is exactly the range of n digits from zero to k. The divisibility hypothesis forces every
positive seed orbit to be regular. -/
theorem grid_support_budget_iff {k q : ℕ} (two : 2 ≤ k) (positive : 0 < q)
    (divisible : ∀ d : ℕ, 0 < d → d ≤ k → d ∣ k * (k - 1) * q) (n : ℕ) :
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin k)) S) (w : S → ℝ)
      (f : Profile (Fin k) (k * (k - 1) * q) → S → Fin k),
      CalibratingLaw S w f ∧ Fintype.card S ≤ k ! * n) ↔ k * q + 1 ≤ (k + 1) ^ n := by
  classical
  let I := Fin k
  let m := k * (k - 1) * q
  have mpos : 0 < m := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) positive
  have cardI : Fintype.card I = k := Fintype.card_fin k
  constructor
  · rintro ⟨S, _, _, w, f, ⟨wp, _, wi, mass, covariance⟩, bound⟩
    have realPos : 0 < (m : ℝ) := by exact_mod_cast mpos
    let v (s : S) := (m : ℝ) * w s
    have scaled (p : Profile I m) (i : I) :
        (∑ s, if f p s = i then v s else 0) = (p.val i : ℝ) := by
      have term (s : S) :
          (if f p s = i then v s else 0) = (m : ℝ) * (if f p s = i then w s else 0) := by
        by_cases h : f p s = i <;> simp [h, v]
      rw [Finset.sum_congr rfl (fun s _ => term s), ← Finset.mul_sum, mass]
      change (m : ℝ) * ((p.val i : ℝ) / m) = (p.val i : ℝ)
      rw [mul_comm, div_mul_cancel₀ _ realPos.ne']
    obtain ⟨r, support, digit⟩ := grid_lower (I := I) (by rwa [cardI])
      (by simpa only [cardI] using divisible) v (fun s => mul_pos realPos (wp s))
      (fun g s => congrArg ((m : ℝ)*·) (wi g s)) f scaled covariance
    simp only [cardI] at support digit
    rw [support] at bound
    have le : r ≤ n := Nat.le_of_mul_le_mul_left bound (Nat.factorial_pos _)
    have div : m / (k - 1) = k * q := by
      change k * (k - 1) * q / (k - 1) = _
      rw [Nat.mul_right_comm, Nat.mul_div_cancel _ (show 0 < k - 1 by omega)]
    rw [div] at digit
    exact digit.trans (Nat.pow_le_pow_right (by omega) le)
  · intro bound
    obtain ⟨w, total, cover⟩ :=
      D5.S3.Combinatorics.Partitions.CommonBlockWeights.common_weights_for_allocations
        (show 0 < k by omega) bound
    have cardScale : 0 < k * (k - 1) := Nat.mul_pos (by omega) (by omega)
    have divide : k - 1 ∣ m := ⟨k * q, by dsimp [m]; ac_rfl⟩
    have weights : k * (k - 1) * (∑ j, w j) = 1 * m := by
      simp [total, m]
    have allocation (t U : ℕ) (tpos : 0 < t) (enough : k * (t - 1) ≤ U) (x : Fin t → ℕ)
        (balance : k * (k - 1) * (∑ i, x i) = U * m) :
        ∃ a : Fin n → Fin t → ℕ, (∀ j, ∑ i, a j i = U) ∧
          (∀ i, ∑ j, a j i * w j = 1 * x i) := by
      have sum : (∑ i, x i) = U * q := by
        apply Nat.eq_of_mul_eq_mul_left cardScale
        rw [balance]
        dsimp [m]
        ac_rfl
      simpa only [Nat.one_mul] using cover t U tpos enough x sum
    obtain ⟨S, fs, action, v, f, pos, total, inv, mass, equiv, card⟩ :=
      law_of_scaled_block_allocations two mpos zero_lt_one divide w weights allocation
    exact ⟨S, fs, action, v, f, ⟨pos, total, inv, mass, equiv⟩, card⟩

end D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
