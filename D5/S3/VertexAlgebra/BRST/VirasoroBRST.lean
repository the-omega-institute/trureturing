/- GID: D5/S3/VertexAlgebra/BRST/VirasoroBRST
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/VirasoroBRST
   mirror-E: none(waiver:algebraic-virasoro-brst-anomaly)
   anchors: []
   utility: none
   digest: Original integer bc BRST square for arbitrary lower-truncated Virasoro matter. -/

import D5.S3.Quantum.Fermionic.BcGhostSquare
import D5.S3.Quantum.Fermionic.BcGhostBRSTDegree
import D5.S3.Quantum.Fermionic.BcGhostChargeTensor
import D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Tactic.NoncommRing

/-! The original integer bc BRST charge on arbitrary lower-truncated
Virasoro matter. Every infinite-index sum is taken after evaluation on a
state and has genuine finite support. The matter datum stores only modes,
central charge, the original Virasoro relation and positive-mode truncation.
The signed square uses the native ghost square and charged tensor commutant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostCharge
open private lift_mul from D5.S3.Quantum.Fermionic.BcGhostChargeTensor
open private cc_c squareAnomaly_b squareAnomaly_c from D5.S3.Quantum.Fermionic.BcGhostSquare

noncomputable section
namespace D5.S3.VertexAlgebra.VirasoroBRST

/-- The sole arbitrary-matter input: literal Virasoro modes and lower
truncation.  No BRST, Ward, covariance, degree, square, vacuum, positivity,
or finite-dimensional assumption is stored here. -/
class MatterDatum (V : Type*) [AddCommGroup V] [Module ℂ V] where
  mode : ℤ → Module.End ℂ V
  centralCharge : ℂ
  virasoro : ∀ m n : ℤ,
    mode m * mode n - mode n * mode m =
      ((m-n : ℤ) : ℂ) • mode (m+n) +
        (if m+n = 0 then (centralCharge / 12) * ((m : ℂ)^3-m) else 0) •
          (1 : Module.End ℂ V)
  positive_mode_truncation : ∀ v : V, ∃ B : ℤ, ∀ n : ℤ, B < n → mode n v = 0

abbrev State (V : Type*) [AddCommGroup V] [Module ℂ V] := V ⊗[ℂ] Fock

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (A : MatterDatum V)

/-- Original integer ghost modes lifted through the identity on arbitrary matter. -/
abbrev ghostB (_A : MatterDatum V) (r : ℤ) : Module.End ℂ (State V) :=
  BcGhostChargeTensor.B (M := V) r
abbrev ghostC (_A : MatterDatum V) (r : ℤ) : Module.End ℂ (State V) :=
  BcGhostChargeTensor.C (M := V) r
abbrev number : Module.End ℂ (State V) :=
  BcGhostChargeTensor.number (M := V)

abbrev matterMode (r : ℤ) : Module.End ℂ (State V) :=
  TensorProduct.map (A.mode r) LinearMap.id
abbrev ghostVirasoro (_A : MatterDatum V) (r : ℤ) : Module.End ℂ (State V) :=
  TensorProduct.map LinearMap.id (BcGhostVirasoro.L r)
abbrev ghostR (_A : MatterDatum V) (r : ℤ) : Module.End ℂ (State V) :=
  TensorProduct.map LinearMap.id (BcGhostBRST.R r)
abbrev ghostCharge (_A : MatterDatum V) : Module.End ℂ (State V) :=
  BcGhostChargeTensor.liftGhost (M := V) BcGhostBRST.Qg
abbrev ghostSquareAnomaly (_A : MatterDatum V) : Module.End ℂ (State V) :=
  BcGhostChargeTensor.liftGhost (M := V) BcGhostBRST.squareAnomaly

/-- The shifted quadratic family used in the finite covariance cancellation. -/
def paired (r k : ℤ) : Module.End ℂ (State V) :=
  TensorProduct.map (A.mode k) (BcGhostFock.c (r-k))

def summand (m : ℤ) : Module.End ℂ (State V) :=
  TensorProduct.map (A.mode m) (BcGhostFock.c (-m))

private theorem summand_product (m : ℤ) :
    summand A m = matterMode A m * ghostC A (-m) := by
  apply TensorProduct.ext'
  intro v w
  simp only [summand, matterMode, ghostC, BcGhostChargeTensor.C,
    BcGhostChargeTensor.liftGhost, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]

/-- The positive c-tail is supplied by the original occupation-radius theorem. -/
private theorem c_tail (w : Fock) :
    ∃ B : ℤ, ∀ n : ℤ, B < n → BcGhostFock.c n w = 0 := by
  obtain ⟨B, hB, hw⟩ := BcGhostOccupationRadius.exists_radius w
  exact ⟨(B : ℤ), fun n hn => (BcGhostOccupationRadius.high_modes hB hw n hn).2⟩

/-- Genuine statewise local finiteness of the matter/c summand. -/
theorem summand_finite (x : State V) :
    Function.HasFiniteSupport (fun m : ℤ => summand A m x) := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      obtain ⟨B, hB⟩ := A.positive_mode_truncation v
      obtain ⟨C, hC⟩ := c_tail w
      apply (Set.finite_Icc (-C) B).subset
      intro m hm
      by_contra hn
      have ht : m < -C ∨ B < m := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hn
      apply hm
      simp only [summand, TensorProduct.map_tmul]
      rcases ht with ht | ht
      · rw [hC (-m) (by omega), TensorProduct.tmul_zero]
      · rw [hB m ht, TensorProduct.zero_tmul]
  | add x y hx hy =>
      apply (hx.union hy).subset
      intro m hm
      by_contra hn
      have hzx : summand A m x = 0 := by
        by_contra hz
        exact hn (Or.inl hz)
      have hzy : summand A m y = 0 := by
        by_contra hz
        exact hn (Or.inr hz)
      exact hm (by simp only [map_add, hzx, hzy, add_zero])

/-- Statewise finite charge, with no infinite operator-family definition. -/
def T : Module.End ℂ (State V) where
  toFun x := ∑ᶠ m : ℤ, summand A m x
  map_add' x y := by
    simp only [map_add]
    exact finsum_add_distrib (summand_finite A x) (summand_finite A y)
  map_smul' a x := by
    simp only [map_smul]
    exact (smul_finsum' a (summand_finite A x)).symm

@[simp] theorem T_apply (x : State V) :
    T A x = ∑ᶠ m : ℤ, (matterMode A m * ghostC A (-m)) x := by
  simp only [T, LinearMap.coe_mk, AddHom.coe_mk, summand_product]

/-- Any finite capture computes T on that state. -/
theorem finite_capture (x : State V) (s : Finset ℤ)
    (hs : Function.support (fun m : ℤ => summand A m x) ⊆ (s : Set ℤ)) :
    T A x = ∑ m ∈ s, summand A m x := by
  rw [T_apply]
  simp_rw [← summand_product]
  exact finsum_eq_sum_of_support_subset _ hs

/-- One finite union captures every prescribed finite collection of transformed
states.  This is the common-capture mechanism used by all Ward proofs. -/
theorem common_capture (X : Finset (State V)) :
    ∃ s : Finset ℤ, ∀ x ∈ X,
      Function.support (fun m : ℤ => summand A m x) ⊆ (s : Set ℤ) := by
  classical
  refine ⟨X.biUnion (fun x => (summand_finite A x).toFinset), ?_⟩
  intro x hx m hm
  exact Finset.mem_biUnion.mpr ⟨x, hx, by simpa using hm⟩

private theorem summand_b (m r : ℤ) :
    summand A m * ghostB A r + ghostB A r * summand A m =
      if m = r then matterMode A m else 0 := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun (BcGhostFock.ghost_mixed_car r (-m)) w
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  simp only [summand, ghostB, BcGhostChargeTensor.B, BcGhostChargeTensor.liftGhost,
    matterMode, LinearMap.add_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rw [← TensorProduct.tmul_add, add_comm (BcGhostFock.c (-m)
    (BcGhostFock.b r w)), h]
  by_cases hm : m = r
  · subst m; simp
  · have hz : r + -m ≠ 0 := by omega
    simp [hm, hz]

private theorem summand_c (m r : ℤ) :
    summand A m * ghostC A r + ghostC A r * summand A m = 0 := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun (BcGhostFock.ghost_c_car (-m) r) w
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  simp only [summand, ghostC, BcGhostChargeTensor.C, BcGhostChargeTensor.liftGhost,
    LinearMap.add_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply]
  rw [← TensorProduct.tmul_add, h, TensorProduct.tmul_zero]

private theorem summand_ghost_number (m : ℤ) :
    number (V := V) * summand A m - summand A m * number (V := V) = summand A m := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun (ghost_number_relations.2.2 (-m)) w
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [number, BcGhostChargeTensor.number, BcGhostChargeTensor.liftGhost,
    summand, LinearMap.sub_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rw [← TensorProduct.tmul_sub, h]

/-- Degree one of T, proved with one common finite capture of x and N x. -/
theorem number_T :
    number (V := V) * T A - T A * number (V := V) = T A := by
  classical
  apply LinearMap.ext
  intro x
  obtain ⟨s, hs⟩ := common_capture A {x, number (V := V) x}
  have hx := hs x (by simp)
  have hNx := hs (number (V := V) x) (by simp)
  change number (V := V) (T A x) - T A (number (V := V) x) = T A x
  calc
    _ = ∑ m ∈ s, (number (V := V) (summand A m x) -
        summand A m (number (V := V) x)) := by
      rw [finite_capture A x s hx, finite_capture A _ s hNx, map_sum,
        Finset.sum_sub_distrib]
    _ = ∑ m ∈ s, summand A m x := by
      apply Finset.sum_congr rfl
      intro m hm
      exact LinearMap.congr_fun (summand_ghost_number A m) x
    _ = T A x := (finite_capture A x s hx).symm

private theorem number_ghostCharge :
    number (V := V) * ghostCharge A - ghostCharge A * number (V := V) = ghostCharge A := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun BcGhostBRST.ghost_number_Qg w
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [number, ghostCharge, BcGhostChargeTensor.number,
    BcGhostChargeTensor.liftGhost, LinearMap.sub_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rw [← TensorProduct.tmul_sub, h]

/-- All-integer b Ward identity, with a finite capture of x and b_r x. -/
theorem ward_b (r : ℤ) :
    T A * ghostB A r + ghostB A r * T A = matterMode A r := by
  classical
  apply LinearMap.ext
  intro x
  obtain ⟨s₀, hs₀⟩ := common_capture A {x, ghostB A r x}
  let s := insert r s₀
  have hsx : Function.support (fun m : ℤ => summand A m x) ⊆ (s : Set ℤ) := by
    intro m hm; exact Finset.mem_insert_of_mem (hs₀ x (by simp) hm)
  have hsb : Function.support (fun m : ℤ => summand A m (ghostB A r x)) ⊆
      (s : Set ℤ) := by
    intro m hm; exact Finset.mem_insert_of_mem (hs₀ (ghostB A r x) (by simp) hm)
  change T A (ghostB A r x) + ghostB A r (T A x) = _
  rw [finite_capture A _ s hsb, finite_capture A _ s hsx, map_sum,
    ← Finset.sum_add_distrib]
  calc
    _ = ∑ m ∈ s, if m = r then matterMode A m x else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      have h := LinearMap.congr_fun (summand_b A m r) x
      by_cases he : m = r <;>
        simpa only [LinearMap.add_apply, Module.End.mul_apply, he, ite_true,
          ite_false, LinearMap.zero_apply] using h
    _ = _ := by simp [s]

/-- All-integer c Ward identity. -/
theorem ward_c (r : ℤ) :
    T A * ghostC A r + ghostC A r * T A = 0 := by
  classical
  apply LinearMap.ext
  intro x
  have hx := summand_finite A x
  have hy := summand_finite A (ghostC A r x)
  change (∑ᶠ m : ℤ, summand A m (ghostC A r x)) +
      ghostC A r (∑ᶠ m : ℤ, summand A m x) = 0
  rw [map_finsum (ghostC A r) hx,
    ← finsum_add_distrib hy (hx.fun_comp (map_zero (ghostC A r)))]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  exact LinearMap.congr_fun (summand_c A m r) x

private theorem paired_finite (r : ℤ) (x : State V) :
    Function.HasFiniteSupport (fun k : ℤ => paired A r k x) := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      obtain ⟨B, hB⟩ := A.positive_mode_truncation v
      obtain ⟨C, hC⟩ := c_tail w
      apply (Set.finite_Icc (r-C) B).subset
      intro k hk
      by_contra hn
      have ht : k < r-C ∨ B < k := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hn
      apply hk
      simp only [paired, TensorProduct.map_tmul]
      rcases ht with ht | ht
      · rw [hC (r-k) (by omega), TensorProduct.tmul_zero]
      · rw [hB k ht, TensorProduct.zero_tmul]
  | add x y hx hy =>
      apply (hx.union hy).subset
      intro k hk
      by_contra hn
      have hzx : paired A r k x = 0 := by
        by_contra hz; exact hn (Or.inl hz)
      have hzy : paired A r k y = 0 := by
        by_contra hz; exact hn (Or.inr hz)
      exact hk (by simp only [map_add, hzx, hzy, add_zero])

private theorem weighted_finite (r : ℤ) (x : State V) (a : ℤ → ℂ) :
    Function.HasFiniteSupport (fun k : ℤ => a k • paired A r k x) := by
  apply (paired_finite A r x).subset
  intro k hk hn
  exact hk (by simp [hn])

private theorem matter_commutator (m r : ℤ) :
    summand A m * matterMode A r - matterMode A r * summand A m =
      ((m-r : ℤ) : ℂ) • paired A r (m+r) +
        (if m+r = 0 then (A.centralCharge / 12) * ((m : ℂ)^3-m) else 0) •
          ghostC A (-m) := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun (A.virasoro m r) v
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply] at h
  simp only [summand, matterMode, paired, ghostC, BcGhostChargeTensor.C,
    BcGhostChargeTensor.liftGhost, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, show r-(m+r) = -m by omega]
  rw [← TensorProduct.sub_tmul, h, TensorProduct.add_tmul]
  rfl

private theorem ghost_commutator (m r : ℤ) :
    summand A m * ghostVirasoro A r - ghostVirasoro A r * summand A m =
      ((2*r-m : ℤ) : ℂ) • paired A r m := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun (BcGhostVirasoro.ward_c r (-m)) w
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply] at h
  have hr : BcGhostFock.c (-m) (BcGhostVirasoro.L r w) -
      BcGhostVirasoro.L r (BcGhostFock.c (-m) w) =
        ((2*r-m : ℤ) : ℂ) • BcGhostFock.c (r-m) w := by
    calc
      _ = -(BcGhostVirasoro.L r (BcGhostFock.c (-m) w) -
        BcGhostFock.c (-m) (BcGhostVirasoro.L r w)) := by abel
      _ = _ := by
        rw [h, ← neg_smul]
        congr 1
        push_cast
        ring
  simp only [summand, ghostVirasoro, paired, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.mul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply]
  rw [← TensorProduct.tmul_sub, hr, TensorProduct.tmul_smul]

private theorem central_finite (r : ℤ) (x : State V) :
    Function.HasFiniteSupport (fun m : ℤ =>
      (if m+r = 0 then (A.centralCharge / 12) * ((m : ℂ)^3-m) else 0) •
        ghostC A (-m) x) := by
  apply (Set.finite_singleton (-r)).subset
  intro m hm
  by_contra hn
  have hne : m+r ≠ 0 := by
    intro he
    apply hn
    exact Set.mem_singleton_iff.mpr (by omega)
  exact hm (by simp only [hne, ite_false, zero_smul])

private theorem central_sum (r : ℤ) (x : State V) :
    (∑ᶠ m : ℤ, (if m+r = 0 then (A.centralCharge / 12) * ((m : ℂ)^3-m) else 0) •
      ghostC A (-m) x) =
      (-((A.centralCharge / 12) * ((r : ℂ)^3-r))) • ghostC A r x := by
  rw [finsum_eq_single _ (-r) (fun m hm => by
    simp [show m+r ≠ 0 by omega])]
  simp only [neg_add_cancel, ite_true, neg_neg, Int.cast_neg]
  congr 1
  ring

/-- Matter covariance is pointwise, with finite support on both input states
and on the translated paired family. Only state vectors are summed. -/
theorem matter_covariance_apply (r : ℤ) (x : State V) :
    (T A * matterMode A r - matterMode A r * T A) x =
      (∑ᶠ k : ℤ, ((k-2*r : ℤ) : ℂ) • paired A r k x) +
      (-((A.centralCharge / 12) * ((r : ℂ)^3-r))) • ghostC A r x := by
  let f : ℤ → State V := fun k => ((k-2*r : ℤ) : ℂ) • paired A r k x
  have hf : Function.HasFiniteSupport f := weighted_finite A r x _
  have hshift : Function.HasFiniteSupport (fun m : ℤ => f (m+r)) :=
    hf.fun_comp_of_injective (Equiv.addRight r).injective
  have hx := summand_finite A x
  have hMx := summand_finite A (matterMode A r x)
  have hmap := hx.fun_comp (map_zero (matterMode A r))
  change (∑ᶠ m : ℤ, summand A m (matterMode A r x)) -
      matterMode A r (∑ᶠ m : ℤ, summand A m x) = _
  rw [map_finsum (matterMode A r) hx, ← finsum_sub_distrib hMx hmap]
  calc
    _ = ∑ᶠ m : ℤ, (f (m+r) +
        (if m+r = 0 then (A.centralCharge / 12) * ((m : ℂ)^3-m) else 0) •
          ghostC A (-m) x) := by
      apply finsum_congr
      intro m
      simpa only [f, show m+r-2*r = m-r by omega, LinearMap.sub_apply,
        LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply] using
        LinearMap.congr_fun (matter_commutator A m r) x
    _ = (∑ᶠ m : ℤ, f (m+r)) +
        (∑ᶠ m : ℤ, (if m+r = 0 then
          (A.centralCharge / 12) * ((m : ℂ)^3-m) else 0) • ghostC A (-m) x) :=
      finsum_add_distrib hshift (central_finite A r x)
    _ = _ := by
      have hreindex : (∑ᶠ m : ℤ, f (m+r)) = ∑ᶠ k : ℤ, f k := by
        exact finsum_comp_equiv (Equiv.addRight r) (f := f)
      rw [hreindex, central_sum A r x]

/-- Ghost covariance uses the native all-integer c Ward coefficient 2r-m. -/
theorem ghost_covariance_apply (r : ℤ) (x : State V) :
    (T A * ghostVirasoro A r - ghostVirasoro A r * T A) x =
      ∑ᶠ k : ℤ, ((2*r-k : ℤ) : ℂ) • paired A r k x := by
  have hx := summand_finite A x
  have hGx := summand_finite A (ghostVirasoro A r x)
  have hmap := hx.fun_comp (map_zero (ghostVirasoro A r))
  change (∑ᶠ m : ℤ, summand A m (ghostVirasoro A r x)) -
      ghostVirasoro A r (∑ᶠ m : ℤ, summand A m x) = _
  rw [map_finsum (ghostVirasoro A r) hx, ← finsum_sub_distrib hGx hmap]
  apply finsum_congr
  intro m
  exact LinearMap.congr_fun (ghost_commutator A m r) x

/-- The two finite weighted state sums cancel at every integer index. -/
theorem covariance (r : ℤ) :
    T A * (matterMode A r + ghostVirasoro A r) -
      (matterMode A r + ghostVirasoro A r) * T A =
      (-((A.centralCharge / 12) * ((r : ℂ)^3-r))) • ghostC A r := by
  apply LinearMap.ext
  intro x
  have hcancel : (∑ᶠ k : ℤ, ((k-2*r : ℤ) : ℂ) • paired A r k x) +
      (∑ᶠ k : ℤ, ((2*r-k : ℤ) : ℂ) • paired A r k x) = 0 := by
    rw [← finsum_add_distrib
      (weighted_finite A r x (fun k => ((k-2*r : ℤ) : ℂ)))
      (weighted_finite A r x (fun k => ((2*r-k : ℤ) : ℂ)))]
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    rw [← add_smul]
    have hz : ((k-2*r : ℤ) : ℂ) + ((2*r-k : ℤ) : ℂ) = 0 := by
      push_cast
      ring
    rw [hz, zero_smul]
  calc
    _ = (T A * matterMode A r - matterMode A r * T A) x +
        (T A * ghostVirasoro A r - ghostVirasoro A r * T A) x := by
      simp only [Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.sub_apply, map_add]
      abel
    _ = ((∑ᶠ k : ℤ, ((k-2*r : ℤ) : ℂ) • paired A r k x) +
        (∑ᶠ k : ℤ, ((2*r-k : ℤ) : ℂ) • paired A r k x)) +
        (-((A.centralCharge / 12) * ((r : ℂ)^3-r))) • ghostC A r x := by
      rw [matter_covariance_apply A r x, ghost_covariance_apply A r x]
      abel
    _ = _ := by simp only [hcancel, zero_add, LinearMap.smul_apply]

-- Linear packaging of the existing native tensor lift is required for map_add,
-- map_sub and map_smul; liftGhost itself is a function, not a linear map.
private def lift : Module.End ℂ Fock →ₗ[ℂ] Module.End ℂ (State V) :=
  LinearMap.lTensorHom V

private theorem lift_product (X Y : Module.End ℂ Fock) :
    lift (V := V) (X * Y) = lift X * lift Y := by
  exact lift_mul X Y

private theorem ghost_ward_b (r : ℤ) :
    ghostCharge A * ghostB A r + ghostB A r * ghostCharge A = ghostVirasoro A r := by
  change lift (V := V) BcGhostBRST.Qg * lift (BcGhostFock.b r) +
    lift (BcGhostFock.b r) * lift BcGhostBRST.Qg = lift (BcGhostVirasoro.L r)
  simpa only [map_add, lift_product] using
    congrArg (lift (V := V)) (BcGhostBRST.ward_b r)

private theorem ghost_ward_c (r : ℤ) :
    ghostCharge A * ghostC A r + ghostC A r * ghostCharge A = ghostR A r := by
  change lift (V := V) BcGhostBRST.Qg * lift (BcGhostFock.c r) +
    lift (BcGhostFock.c r) * lift BcGhostBRST.Qg = lift (BcGhostBRST.R r)
  simpa only [map_add, lift_product] using
    congrArg (lift (V := V)) (BcGhostBRST.ward_c r)

abbrev Ltotal (r : ℤ) : Module.End ℂ (State V) :=
  matterMode A r + ghostVirasoro A r
abbrev Q : Module.End ℂ (State V) := T A + ghostCharge A
abbrev N (_A : MatterDatum V) : Module.End ℂ (State V) := number (V := V)

/-- The literal all-integer Ward identities for Q=T+id⊗Qg. -/
theorem Q_ward_b (r : ℤ) :
    Q A * ghostB A r + ghostB A r * Q A = Ltotal A r := by
  unfold Q Ltotal
  calc
    _ = (T A * ghostB A r + ghostB A r * T A) +
        (ghostCharge A * ghostB A r + ghostB A r * ghostCharge A) := by
          noncomm_ring
    _ = _ := by rw [ward_b A r, ghost_ward_b A r]

theorem Q_ward_c (r : ℤ) :
    Q A * ghostC A r + ghostC A r * Q A = ghostR A r := by
  unfold Q
  calc
    _ = (T A * ghostC A r + ghostC A r * T A) +
        (ghostCharge A * ghostC A r + ghostC A r * ghostCharge A) := by
          noncomm_ring
    _ = _ := by rw [ward_c A r, ghost_ward_c A r, zero_add]

private theorem ghost_square_b (r : ℤ) :
    ghostSquareAnomaly A * ghostB A r - ghostB A r * ghostSquareAnomaly A =
      BcGhostBRST.anomalyCoefficient r • ghostC A r := by
  change lift (V := V) BcGhostBRST.squareAnomaly * lift (BcGhostFock.b r) -
    lift (BcGhostFock.b r) * lift BcGhostBRST.squareAnomaly =
      BcGhostBRST.anomalyCoefficient r • lift (BcGhostFock.c r)
  simpa only [map_sub, map_smul, lift_product] using
    congrArg (lift (V := V)) (squareAnomaly_b r)

private theorem ghost_square_c (r : ℤ) :
    ghostSquareAnomaly A * ghostC A r - ghostC A r * ghostSquareAnomaly A = 0 := by
  change lift (V := V) BcGhostBRST.squareAnomaly * lift (BcGhostFock.c r) -
    lift (BcGhostFock.c r) * lift BcGhostBRST.squareAnomaly = 0
  simpa only [map_sub, map_zero, lift_product] using
    congrArg (lift (V := V)) (squareAnomaly_c r)

private theorem ghostCharge_square :
    ghostCharge A * ghostCharge A = ghostSquareAnomaly A := by
  change lift (V := V) BcGhostBRST.Qg * lift BcGhostBRST.Qg =
    lift BcGhostBRST.squareAnomaly
  rw [← lift_product, BcGhostBRST.square_anomaly]

private theorem ghostCharge_R (r : ℤ) :
    ghostCharge A * ghostR A r - ghostR A r * ghostCharge A = 0 := by
  calc
    _ = (ghostCharge A * ghostCharge A) * ghostC A r -
        ghostC A r * (ghostCharge A * ghostCharge A) := by
      rw [← ghost_ward_c A r]
      noncomm_ring
    _ = 0 := by rw [ghostCharge_square A, ghost_square_c A r]

-- The native R is a statewise finite pure-c quadratic; cc_c supplies each term.
private theorem R_c (r s : ℤ) :
    BcGhostBRST.R r * BcGhostFock.c s - BcGhostFock.c s * BcGhostBRST.R r = 0 := by
  apply LinearMap.ext
  intro w
  have hw := BcGhostBRST.rTerm_finite r w
  have hc := BcGhostBRST.rTerm_finite r (BcGhostFock.c s w)
  have hmap := hw.fun_comp (map_zero (BcGhostFock.c s))
  change (∑ᶠ p : ℤ, BcGhostBRST.rTerm r p (BcGhostFock.c s w)) -
    BcGhostFock.c s (∑ᶠ p : ℤ, BcGhostBRST.rTerm r p w) = 0
  rw [map_finsum (BcGhostFock.c s) hw, ← finsum_sub_distrib hc hmap]
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  have h := LinearMap.congr_fun (cc_c p (r-p) s) w
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  simp only [BcGhostBRST.rTerm, LinearMap.smul_apply, map_smul, Module.End.mul_apply]
  rw [← smul_sub, h, smul_zero]

private theorem summand_R (m r : ℤ) :
    summand A m * ghostR A r - ghostR A r * summand A m = 0 := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun (sub_eq_zero.mp (R_c r (-m))) w
  simp only [Module.End.mul_apply] at h
  simp only [summand, ghostR, LinearMap.sub_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply]
  rw [h, sub_self]

private theorem T_R (r : ℤ) :
    T A * ghostR A r - ghostR A r * T A = 0 := by
  classical
  apply LinearMap.ext
  intro x
  obtain ⟨s, hs⟩ := common_capture A {x, ghostR A r x}
  have hx := hs x (by simp)
  have hR := hs (ghostR A r x) (by simp)
  change T A (ghostR A r x) - ghostR A r (T A x) = 0
  rw [finite_capture A _ s hR, finite_capture A _ s hx, map_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro m hm
  exact LinearMap.congr_fun (summand_R A m r) x

theorem Q_R (r : ℤ) : Q A * ghostR A r - ghostR A r * Q A = 0 := by
  unfold Q
  calc
    _ = (T A * ghostR A r - ghostR A r * T A) +
        (ghostCharge A * ghostR A r - ghostR A r * ghostCharge A) := by
      noncomm_ring
    _ = 0 := by rw [T_R A r, ghostCharge_R A r, add_zero]

private theorem ghostCharge_matterMode (r : ℤ) :
    ghostCharge A * matterMode A r - matterMode A r * ghostCharge A = 0 := by
  apply TensorProduct.ext'
  intro v w
  simp only [ghostCharge, BcGhostChargeTensor.liftGhost, matterMode, Module.End.mul_apply,
    LinearMap.sub_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.zero_apply, sub_self]

private theorem ghost_mixed_anomaly (r : ℤ) :
    ghostCharge A * ghostVirasoro A r - ghostVirasoro A r * ghostCharge A =
      ((26/12 : ℂ) * ((r : ℂ)^3-r)) • ghostC A r := by
  change lift (V := V) BcGhostBRST.Qg * lift (BcGhostVirasoro.L r) -
    lift (BcGhostVirasoro.L r) * lift BcGhostBRST.Qg =
      ((26/12 : ℂ) * ((r : ℂ)^3-r)) • lift (BcGhostFock.c r)
  simpa only [map_sub, map_smul, lift_product] using
    congrArg (lift (V := V)) (BcGhostBRST.mixed_anomaly r)

/-- The full covariance anomaly, including the positive ghost 26 term. -/
theorem Q_Ltotal (r : ℤ) :
    Q A * Ltotal A r - Ltotal A r * Q A =
      (((26-A.centralCharge) / 12) * ((r : ℂ)^3-r)) • ghostC A r := by
  change (T A + ghostCharge A) * (matterMode A r + ghostVirasoro A r) -
      (matterMode A r + ghostVirasoro A r) * (T A + ghostCharge A) = _
  calc
    _ = (T A * (matterMode A r + ghostVirasoro A r) -
        (matterMode A r + ghostVirasoro A r) * T A) +
        (ghostCharge A * matterMode A r - matterMode A r * ghostCharge A) +
        (ghostCharge A * ghostVirasoro A r - ghostVirasoro A r * ghostCharge A) := by
      noncomm_ring
    _ = _ := by
      rw [covariance A r, ghostCharge_matterMode A r,
        ghost_mixed_anomaly A r]
      simp only [add_zero, ← add_smul]
      congr 1
      ring

/-- The original cubic has ghost-number degree one. -/
theorem N_Q :
    N A * Q A - Q A * N A = Q A := by
  unfold N Q
  calc
    _ = (number (V := V) * T A - T A * number (V := V)) +
        (number (V := V) * ghostCharge A - ghostCharge A * number (V := V)) := by
      noncomm_ring
    _ = _ := by rw [number_T A, number_ghostCharge A]

/-- E is the genuine residual against the native ghost square. -/
def residual : Module.End ℂ (State V) :=
  Q A * Q A - ((26-A.centralCharge) / 26) • ghostSquareAnomaly A

private theorem residual_commutator (X Y C : Module.End ℂ (State V)) (a : ℂ) :
    (X-a • Y) * C - C * (X-a • Y) =
      (X*C-C*X) - a • (Y*C-C*Y) := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

private theorem square_ward_b (r : ℤ) :
    (Q A * Q A) * ghostB A r - ghostB A r * (Q A * Q A) =
      (((26-A.centralCharge) / 12) * ((r : ℂ)^3-r)) • ghostC A r := by
  calc
    _ = Q A * (Q A * ghostB A r + ghostB A r * Q A) -
        (Q A * ghostB A r + ghostB A r * Q A) * Q A := by noncomm_ring
    _ = _ := by rw [Q_ward_b A r, Q_Ltotal A r]

private theorem square_ward_c (r : ℤ) :
    (Q A * Q A) * ghostC A r - ghostC A r * (Q A * Q A) = 0 := by
  calc
    _ = Q A * (Q A * ghostC A r + ghostC A r * Q A) -
        (Q A * ghostC A r + ghostC A r * Q A) * Q A := by noncomm_ring
    _ = 0 := by rw [Q_ward_c A r, Q_R A r]

theorem residual_b (r : ℤ) :
    residual A * ghostB A r = ghostB A r * residual A := by
  apply sub_eq_zero.mp
  change (Q A * Q A - ((26-A.centralCharge) / 26) • ghostSquareAnomaly A) *
      ghostB A r - ghostB A r *
      (Q A * Q A - ((26-A.centralCharge) / 26) • ghostSquareAnomaly A) = 0
  rw [residual_commutator, square_ward_b A r, ghost_square_b A r, smul_smul]
  have hc : ((26-A.centralCharge) / 26) * BcGhostBRST.anomalyCoefficient r =
      ((26-A.centralCharge) / 12) * ((r : ℂ)^3-r) := by
    unfold BcGhostBRST.anomalyCoefficient
    ring
  rw [hc, sub_self]

theorem residual_c (r : ℤ) :
    residual A * ghostC A r = ghostC A r * residual A := by
  apply sub_eq_zero.mp
  change (Q A * Q A - ((26-A.centralCharge) / 26) • ghostSquareAnomaly A) *
      ghostC A r - ghostC A r *
      (Q A * Q A - ((26-A.centralCharge) / 26) • ghostSquareAnomaly A) = 0
  rw [residual_commutator, square_ward_c A r, ghost_square_c A r, smul_zero,
    sub_self]

private theorem square_degree (X : Module.End ℂ (State V))
    (hX : number (V := V) * X - X * number (V := V) = X) :
    number (V := V) * X ^ 2 - X ^ 2 * number (V := V) = (2 : ℂ) • X ^ 2 := by
  simp only [pow_two]
  calc
    _ = (number (V := V) * X - X * number (V := V)) * X +
        X * (number (V := V) * X - X * number (V := V)) := by
      simp only [sub_mul, mul_sub, mul_assoc]
      abel
    _ = _ := by simp only [hX, two_smul]

private theorem residual_degree :
    number (V := V) * residual A - residual A * number (V := V) = (2 : ℂ) • residual A := by
  rw [show residual A = Q A ^ 2 - ((26-A.centralCharge) / 26) •
      ghostCharge A ^ 2 by
        simp only [residual, pow_two, ghostCharge_square A]]
  calc
    _ = (number (V := V) * Q A ^ 2 - Q A ^ 2 * number (V := V)) -
        ((26-A.centralCharge) / 26) •
          (number (V := V) * ghostCharge A ^ 2 -
            ghostCharge A ^ 2 * number (V := V)) := by
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
      abel
    _ = (2 : ℂ) • Q A ^ 2 - ((26-A.centralCharge) / 26) •
        ((2 : ℂ) • ghostCharge A ^ 2) := by
      rw [square_degree (Q A) (N_Q A),
        square_degree (ghostCharge A) (number_ghostCharge A)]
    _ = (2 : ℂ) •
        (Q A ^ 2 - ((26-A.centralCharge) / 26) • ghostCharge A ^ 2) := by module

/-- Full central-charge square in the native ghost-square form. -/
theorem square_anomaly :
    Q A ^ 2 = ((26-A.centralCharge) / 26) • ghostSquareAnomaly A := by
  have hz : residual A = 0 :=
    BcGhostChargeTensor.charged_commutant_vanishes (M := V) (residual A)
      (fun r => residual_b A r) (fun r => residual_c A r)
      (2 : ℂ) (by norm_num) (residual_degree A)
  change Q A * Q A - ((26-A.centralCharge) / 26) • ghostSquareAnomaly A = 0 at hz
  simpa only [pow_two] using sub_eq_zero.mp hz

private def liftedSquareTerm (n : ℤ) : Module.End ℂ (State V) :=
  BcGhostChargeTensor.liftGhost (M := V) (BcGhostBRST.squareTerm n)

private theorem liftedSquareTerm_finite (x : State V) :
    Function.HasFiniteSupport (fun n : ℤ => liftedSquareTerm n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      simpa only [liftedSquareTerm, BcGhostChargeTensor.liftGhost,
        TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.mk_apply] using
        (BcGhostBRST.squareTerm_finite w).fun_comp
          (map_zero (TensorProduct.mk ℂ V Fock v))
  | add x y hx hy =>
      apply (hx.union hy).subset
      intro n hn
      by_contra hnot
      have hx0 : liftedSquareTerm n x = 0 := by
        by_contra hz; exact hnot (Or.inl hz)
      have hy0 : liftedSquareTerm n y = 0 := by
        by_contra hz; exact hnot (Or.inr hz)
      exact hn (by simp only [map_add, hx0, hy0, add_zero])

private theorem ghostSquare_apply (x : State V) :
    ghostSquareAnomaly A x = ∑ᶠ n : ℤ, liftedSquareTerm n x := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      simp only [ghostSquareAnomaly, BcGhostChargeTensor.liftGhost,
        TensorProduct.map_tmul, LinearMap.id_apply]
      change v ⊗ₜ[ℂ] (∑ᶠ n : ℤ, BcGhostBRST.squareTerm n w) =
        ∑ᶠ n : ℤ, liftedSquareTerm n (v ⊗ₜ[ℂ] w)
      simpa only [liftedSquareTerm, BcGhostChargeTensor.liftGhost,
        TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.mk_apply] using
        (map_finsum (TensorProduct.mk ℂ V Fock v)
          (BcGhostBRST.squareTerm_finite w))
  | add x y hx hy =>
      rw [map_add, hx, hy]
      simp only [map_add]
      exact (finsum_add_distrib (liftedSquareTerm_finite x)
        (liftedSquareTerm_finite y)).symm

private theorem liftedSquareTerm_eq (n : ℤ) :
    liftedSquareTerm (V := V) n =
      ((-26/24 : ℂ) * ((n : ℂ)^3-n)) • (ghostC A (-n) * ghostC A n) := by
  apply TensorProduct.ext'
  intro v w
  simp only [liftedSquareTerm, BcGhostChargeTensor.liftGhost,
    BcGhostBRST.squareTerm, ghostC, BcGhostChargeTensor.C,
    LinearMap.smul_apply, Module.End.mul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, TensorProduct.tmul_smul]

private theorem scaled_liftedSquareTerm (n : ℤ) (x : State V) :
    ((26-A.centralCharge) / 26) • (liftedSquareTerm n x) =
      (((A.centralCharge-26) / 24) * ((n : ℂ)^3-n)) •
        ((ghostC A (-n) * ghostC A n) x) := by
  rw [liftedSquareTerm_eq A, LinearMap.smul_apply, smul_smul]
  congr 1
  ring

/-- Genuine statewise finite support for the full signed anomaly. -/
theorem square_finite (x : State V) :
    Function.HasFiniteSupport (fun n : ℤ =>
      (((A.centralCharge-26) / 24) * ((n : ℂ)^3-n)) •
        ((ghostC A (-n) * ghostC A n) x)) := by
  have h := (liftedSquareTerm_finite x).fun_comp
    (smul_zero ((26-A.centralCharge) / 26) :
      ((26-A.centralCharge) / 26) • (0 : State V) = 0)
  simpa only [scaled_liftedSquareTerm A] using h

/-- Pointwise full signed integer-mode anomaly on every original tensor state. -/
theorem square_apply (x : State V) :
    (Q A ^ 2) x = ∑ᶠ n : ℤ,
      (((A.centralCharge-26) / 24) * ((n : ℂ)^3-n)) •
        ((ghostC A (-n) * ghostC A n) x) := by
  classical
  have hg := liftedSquareTerm_finite x
  have hf := square_finite (A := A) x
  let s : Finset ℤ := hg.toFinset ∪ hf.toFinset
  have hsg : Function.support (fun n : ℤ => liftedSquareTerm n x) ⊆ (s : Set ℤ) := by
    intro n hn; exact Finset.mem_union_left _ (hg.mem_toFinset.mpr hn)
  have hsf : Function.support (fun n : ℤ =>
      (((A.centralCharge-26) / 24) * ((n : ℂ)^3-n)) •
        ((ghostC A (-n) * ghostC A n) x)) ⊆ (s : Set ℤ) := by
    intro n hn; exact Finset.mem_union_right _ (hf.mem_toFinset.mpr hn)
  rw [square_anomaly A, LinearMap.smul_apply, ghostSquare_apply A x,
    finsum_eq_sum_of_support_subset _ hsg,
    finsum_eq_sum_of_support_subset _ hsf, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun n hn => scaled_liftedSquareTerm A n x)

end D5.S3.VertexAlgebra.VirasoroBRST
