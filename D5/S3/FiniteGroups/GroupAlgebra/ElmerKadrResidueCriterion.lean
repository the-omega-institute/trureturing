/- GID: D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrResidueCriterion
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/ElmerKadrResidueCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Lucas, mathlib/module/Mathlib.Data.Nat.Choose.Factorization]
   utility: none
   digest: The complete finite-field relative-stable tensor criterion in low residues and high-digit carries. -/


import D5.S3.FiniteGroups.GroupAlgebra.PrimeCyclicRelativeTrace
import D5.S3.FiniteGroups.GroupAlgebra.RectangularTensorObstruction
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Factorization

/-!
The finite-field all-residue relative tensor criterion.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrResidueCriterion

open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
open D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization
open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrPositiveCriterion
open scoped TensorProduct DirectSum

universe u

section ElementaryProducts

variable {K G A B C D : Type u} [Field K] [Group G]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]

def prodCongr {ρ : Representation K G A} {σ : Representation K G B}
    {τ : Representation K G C} {υ : Representation K G D}
    (e : ρ.Equiv σ) (f : τ.Equiv υ) : (ρ.prod τ).Equiv (σ.prod υ) :=
  Representation.Equiv.mk (e.toLinearEquiv.prodCongr f.toLinearEquiv) fun c => by
    apply LinearMap.ext
    intro x
    exact Prod.ext (LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' c) x.1)
      (LinearMap.congr_fun (f.toIntertwiningMap.isIntertwining' c) x.2)

def prodAssoc (ρ : Representation K G A) (σ : Representation K G B)
    (τ : Representation K G C) : ((ρ.prod σ).prod τ).Equiv (ρ.prod (σ.prod τ)) :=
  Representation.Equiv.mk (LinearEquiv.prodAssoc K A B C) fun _ => by
    apply LinearMap.ext
    intro x
    rfl

private def addZeroComplement (ρ : Representation K G A)
    (σ : Representation K G B) [Subsingleton B] : ρ.Equiv (ρ.prod σ) :=
  Representation.Equiv.mk
    { toFun := fun x => (x, 0)
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := fun x => Prod.ext rfl (Subsingleton.elim _ _)
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp } fun c => by
    apply LinearMap.ext
    intro x
    exact Prod.ext rfl (map_zero (σ c)).symm

/-- Five actual split identities, including the two off-diagonal zeros,
give an actual equivariant product decomposition. -/
private def equivOfSplitMaps
    (ρ : Representation K G A) (σ : Representation K G B)
    (τ : Representation K G C)
    (f : σ.IntertwiningMap ρ) (g : ρ.IntertwiningMap σ)
    (r : τ.IntertwiningMap ρ) (q : ρ.IntertwiningMap τ)
    (hgf : g.comp f = .id σ) (hqr : q.comp r = .id τ)
    (hgr : g.comp r = 0) (hqf : q.comp f = 0)
    (hsum : f.comp g + r.comp q = .id ρ) : ρ.Equiv (σ.prod τ) :=
  Representation.Equiv.mk
    { toFun := fun x => (g x, q x)
      invFun := fun x => f x.1 + r x.2
      left_inv := fun x => by
        exact congrArg (fun k : ρ.IntertwiningMap ρ => k x) hsum
      right_inv := fun x => by
        apply Prod.ext
        · change g (f x.1 + r x.2) = x.1
          rw [map_add]
          have hf := congrArg (fun k => k x.1) hgf
          have hr := congrArg (fun k => k x.2) hgr
          change g (f x.1) = x.1 at hf
          change g (r x.2) = 0 at hr
          rw [hf, hr, add_zero]
        · change q (f x.1 + r x.2) = x.2
          rw [map_add]
          have hf := congrArg (fun k => k x.1) hqf
          have hr := congrArg (fun k => k x.2) hqr
          change q (f x.1) = 0 at hf
          change q (r x.2) = x.2 at hr
          rw [hf, hr, zero_add]
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp } fun c => by
    apply LinearMap.ext
    intro x
    exact Prod.ext (LinearMap.congr_fun (g.isIntertwining' c) x)
      (LinearMap.congr_fun (q.isIntertwining' c) x)

end ElementaryProducts

section FullOneStepSplitting

variable {K : Type u} [Field K]

/-- The kernel retraction is inverse to the proved difference injection,
using the equation d h = id - sigma mu. -/
theorem kernelRetraction_difference (n m : ℕ)
    (σ : Trunc K ((n + 1) + (m + 1)) →ₗ[K]
      Trunc K (n + 1) ⊗[K] Trunc K (m + 1))
    (hσ : (multiplication (n + 1) (m + 1)).comp σ = LinearMap.id)
    (x : Trunc K n ⊗[K] Trunc K m) :
    kernelRetraction n m σ hσ (differenceTensor n m x) = x := by
  apply differenceTensor_injective (R := K) n m
  rw [difference_kernelRetraction]
  have hz := LinearMap.congr_fun
    (multiplication_differenceTensor (R := K) n m) x
  change multiplication (n + 1) (m + 1) (differenceTensor n m x) = 0 at hz
  rw [hz, map_zero, sub_zero]

theorem kernelRetraction_section (n m : ℕ)
    (σ : Trunc K ((n + 1) + (m + 1)) →ₗ[K]
      Trunc K (n + 1) ⊗[K] Trunc K (m + 1))
    (hσ : (multiplication (n + 1) (m + 1)).comp σ = LinearMap.id)
    (x : Trunc K ((n + 1) + (m + 1))) :
    kernelRetraction n m σ hσ (σ x) = 0 := by
  apply differenceTensor_injective (R := K) n m
  rw [difference_kernelRetraction, map_zero]
  have hs := LinearMap.congr_fun hσ x
  change multiplication (n + 1) (m + 1) (σ x) = x at hs
  rw [hs, sub_self]

/-- Genuine splitting on the original dual polynomial representations.
Both tensor-dual identifications are explicit, with positive kernel injection. -/
def dualTensor_split (n m : ℕ)
    (hbinom : (((n + 1) + (m + 1)).choose (n + 1) : K) ≠ 0) :
    ((dualAction K ((n + 1) + 1)).tprod
      (dualAction K ((m + 1) + 1))).Equiv
      ((dualAction K ((n + 1) + (m + 1) + 1)).prod
        ((dualAction K (n + 1)).tprod (dualAction K (m + 1)))) := by
  classical
  let sectionExists := equivariant_section (K := K) (n + 1) (m + 1) hbinom
  let σ₀ := Classical.choose sectionExists
  have hσ₀ := (Classical.choose_spec sectionExists).1
  have hσtrans := (Classical.choose_spec sectionExists).2
  let μ := multiplicationIntertwiner (K := K) (n + 1) (m + 1)
  let σ : (primalAction K ((n + 1) + (m + 1) + 1)).IntertwiningMap
      ((primalAction K ((n + 1) + 1)).tprod
        (primalAction K ((m + 1) + 1))) :=
    ⟨σ₀, fun c => (hσtrans (Multiplicative.toAdd c)).symm⟩
  let d := differenceIntertwiner (K := K) n m
  let h := kernelRetractionIntertwiner n m σ hσ₀
  letI : Module.Finite K (Primal K ((n + 1) + 1)) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K ((n + 1) + 1))
  letI : Module.Finite K (Primal K ((m + 1) + 1)) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K ((m + 1) + 1))
  letI : Module.Finite K (Primal K (n + 1)) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K (n + 1))
  letI : Module.Finite K (Primal K (m + 1)) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K (m + 1))
  let e := dualTensorEquiv (primalAction K ((n + 1) + 1))
    (primalAction K ((m + 1) + 1))
  let k := dualTensorEquiv (primalAction K (n + 1)) (primalAction K (m + 1))
  let f := e.symm.toIntertwiningMap.comp (dualIntertwiner μ)
  let g := (dualIntertwiner σ).comp e.toIntertwiningMap
  let q := k.symm.toIntertwiningMap.comp
    ((dualIntertwiner d).comp e.toIntertwiningMap)
  let r := e.symm.toIntertwiningMap.comp
    ((dualIntertwiner h).comp k.toIntertwiningMap)
  have hμσ (x) : μ (σ x) = x := LinearMap.congr_fun hσ₀ x
  have hμd (x) : μ (d x) = 0 :=
    LinearMap.congr_fun (multiplication_differenceTensor (R := K) n m) x
  have hhd (x) : h (d x) = x := kernelRetraction_difference n m σ₀ hσ₀ x
  have hhσ (x) : h (σ x) = 0 := kernelRetraction_section n m σ₀ hσ₀ x
  have hdh (x) : d (h x) = x - σ (μ x) :=
    difference_kernelRetraction n m σ₀ hσ₀ x
  apply equivOfSplitMaps _ _ _ f g r q
  · apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (dualIntertwiner σ) (e (e.symm (dualIntertwiner μ x))) y = x y
    rw [e.apply_symm_apply]
    change x (μ (σ y)) = x y
    rw [hμσ]
  · apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply k.injective
    change k (k.symm (dualIntertwiner d
      (e (e.symm (dualIntertwiner h (k x)))))) = k x
    rw [k.apply_symm_apply, e.apply_symm_apply]
    apply LinearMap.ext
    intro y
    change k x (h (d y)) = k x y
    rw [hhd]
  · apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (dualIntertwiner σ)
      (e (e.symm (dualIntertwiner h (k x)))) y = 0
    rw [e.apply_symm_apply]
    change k x (h (σ y)) = 0
    rw [hhσ, map_zero]
  · apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply k.injective
    change k (k.symm (dualIntertwiner d
      (e (e.symm (dualIntertwiner μ x))))) = k 0
    rw [k.apply_symm_apply, e.apply_symm_apply, map_zero]
    apply LinearMap.ext
    intro y
    change x (μ (d y)) = 0
    rw [hμd, map_zero]
  · apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply e.injective
    change e (e.symm (dualIntertwiner μ (dualIntertwiner σ (e x))) +
      e.symm (dualIntertwiner h (k (k.symm (dualIntertwiner d (e x)))))) = e x
    rw [map_add, e.apply_symm_apply, e.apply_symm_apply, k.apply_symm_apply]
    apply LinearMap.ext
    intro y
    change e x (σ (μ y)) + e x (d (h y)) = e x y
    rw [hdh, map_sub]
    abel

private instance dualZeroSubsingleton : Subsingleton (DualPower K 0) := by
  refine ⟨fun x y => ?_⟩
  exact (dualBasis K 0).equivFun.injective (funext fun i => Fin.elim0 i)

/-- Tensor actions always use the actual dualAction, also at dimension zero. -/
abbrev tensorAction (i j : ℕ) := (dualAction K i).tprod (dualAction K j)

/-- The tensor-unit branches have a literally zero complement. There is no
truncated predecessor used as a surrogate for the kernel at n=0 or m=0. -/
def tensor_split (i j : ℕ) (hi : 0 < i) (hj : 0 < j)
    (hbinom : ((i + j - 2).choose (i - 1) : K) ≠ 0) :
    (tensorAction (K := K) i j).Equiv
      ((dualAction K (i + j - 1)).prod (tensorAction (K := K) (i - 1) (j - 1))) := by
  by_cases hi1 : i = 1
  · subst i
    have htop : 1 + j - 1 = j := by omega
    have transfer (d r : ℕ) (hd : d = j) (hr : r = 0) :
        (tensorAction (K := K) 1 j).Equiv
          ((dualAction K d).prod (tensorAction (K := K) r (j - 1))) := by
      subst d r
      exact (tensorUnitLeft (dualAction K j)).trans
        (addZeroComplement (dualAction K j) (tensorAction (K := K) 0 (j - 1)))
    exact transfer _ _ htop (by omega)
  by_cases hj1 : j = 1
  · subst j
    have htop : i + 1 - 1 = i := by omega
    have transfer (d r : ℕ) (hd : d = i) (hr : r = 0) :
        (tensorAction (K := K) i 1).Equiv
          ((dualAction K d).prod (tensorAction (K := K) (i - 1) r)) := by
      subst d r
      exact (tensorUnitRight (dualAction K i)).trans
        (addZeroComplement (dualAction K i) (tensorAction (K := K) (i - 1) 0))
    exact transfer _ _ htop (by omega)
  let n := i - 2
  let m := j - 2
  have hnDim : (n + 1) + 1 = i := by dsimp only [n]; omega
  have hmDim : (m + 1) + 1 = j := by dsimp only [m]; omega
  have hN : (n + 1) + (m + 1) = i + j - 2 := by omega
  have htop : (n + 1) + (m + 1) + 1 = i + j - 1 := by omega
  have hn : n + 1 = i - 1 := by omega
  have hm : m + 1 = j - 1 := by omega
  have e := dualTensor_split (K := K) n m (by rw [hN, hn]; exact hbinom)
  have transfer (i' j' d r s : ℕ)
      (hi' : i' = (n + 1) + 1) (hj' : j' = (m + 1) + 1)
      (hd : d = (n + 1) + (m + 1) + 1)
      (hr : r = n + 1) (hs : s = m + 1) :
      (tensorAction (K := K) i' j').Equiv
        ((dualAction K d).prod (tensorAction (K := K) r s)) := by
    subst i' j' d r s
    exact e
  exact transfer i j (i + j - 1) (i - 1) (j - 1)
    hnDim.symm hmDim.symm htop.symm hn.symm hm.symm

end FullOneStepSplitting

section LowDigits

variable {K : Type u} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- A direct use of Mathlib's single-digit Lucas congruence, transported
to K by CharP. No new Lucas or factorial-division argument is introduced. -/
theorem choose_low_digits (A B x y : ℕ) (hxy : x + y < p) :
    (((p * A + x) + (p * B + y)).choose (p * A + x) : K) =
      ((x + y).choose x : K) * ((A + B).choose A : K) := by
  have hp0 : 0 < p := hp.out.pos
  have hx : x < p := by omega
  have hdiv (c z : ℕ) (hz : z < p) : (p * c + z) / p = c := by
    rw [Nat.add_comm, Nat.add_mul_div_left z c hp0,
      Nat.div_eq_of_lt hz, Nat.zero_add]
  have hmod (c z : ℕ) (hz : z < p) : (p * c + z) % p = z := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul,
      Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hz]
  have hsum : (p * A + x) + (p * B + y) = p * (A + B) + (x + y) := by ring
  have h := CharP.natCast_eq_natCast' K p
    (Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := p) (n := (p * A + x) + (p * B + y)) (k := p * A + x))
  rw [hsum, hmod (A + B) (x + y) hxy, hmod A x hx,
    hdiv (A + B) (x + y) hxy, hdiv A x hx, Nat.cast_mul] at h
  rw [hsum]
  exact h

theorem low_choose_ne_zero (x y : ℕ) (hxy : x + y < p) :
    ((x + y).choose x : K) ≠ 0 := by
  intro hz
  have hd : p ∣ (x + y).choose x := (CharP.cast_eq_zero_iff K p _).mp hz
  exact ((hp.out.coprime_iff_not_dvd).mp
    (hp.out.coprime_choose_of_lt hxy (by omega))) hd

/-- The scalar at every genuine splitting step is governed by the SAME
unrestricted high-digit binomial; no assumptions on further digits occur. -/
theorem step_choose_factorization (a b u v h : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u + v ≤ p)
    (hh : h < min u v) :
    (((p * a + u) + (p * b + v) - 2 - 2 * h).choose
      (p * a + u - 1 - h) : K) =
      ((u - 1 - h + (v - 1 - h)).choose (u - 1 - h) : K) *
        ((a + b).choose a : K) := by
  have hhu := lt_of_lt_of_le hh (min_le_left u v)
  have hhv := lt_of_lt_of_le hh (min_le_right u v)
  have hlow : u - 1 - h + (v - 1 - h) < p := by omega
  have hN : (p * a + u) + (p * b + v) - 2 - 2 * h =
      (p * a + (u - 1 - h)) + (p * b + (v - 1 - h)) := by omega
  have hn : p * a + u - 1 - h = p * a + (u - 1 - h) := by omega
  rw [hN, hn]
  exact choose_low_digits a b (u - 1 - h) (v - 1 - h) hlow

theorem step_choose_ne_zero (a b u v h : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u + v ≤ p)
    (hh : h < min u v) (hchoose : ((a + b).choose a : K) ≠ 0) :
    (((p * a + u) + (p * b + v) - 2 - 2 * h).choose
      (p * a + u - 1 - h) : K) ≠ 0 := by
  rw [step_choose_factorization a b u v h hu hv huv hh]
  have hhu := lt_of_lt_of_le hh (min_le_left u v)
  have hhv := lt_of_lt_of_le hh (min_le_right u v)
  exact mul_ne_zero (low_choose_ne_zero _ _ (by omega)) hchoose

end LowDigits

section ActualFiniteSum

variable {K : Type u} [Field K]

/-- The actual expected direct sum, with original polynomial dimensions. -/
abbrev LayerSpace (K : Type u) [Field K] (i j h k : ℕ) :=
  ⨁ ell : Fin k, DualPower K (i + j - (2 * (h + ell.val) + 1))

def layerAction (i j h k : ℕ) :
    Representation K (Multiplicative K) (LayerSpace K i j h k) :=
  Representation.directSum
    (fun ell : Fin k => dualAction K (i + j - (2 * (h + ell.val) + 1)))

abbrev ExpectedSpace (K : Type u) [Field K] (i j t : ℕ) :=
  ⨁ ell : Fin t, DualPower K (i + j - (2 * ell.val + 1))

def expectedAction (i j t : ℕ) :
    Representation K (Multiplicative K) (ExpectedSpace K i j t) :=
  Representation.directSum (fun ell : Fin t => dualAction K (i + j - (2 * ell.val + 1)))

/-- Finite direct sums split at index zero using Mathlib's actual
direct-sum/Pi and dependent Fin.cons linear equivalences. -/
private def directSumConsEquiv (k : ℕ) (d : Fin (k + 1) → ℕ) :
    (Representation.directSum (fun ell => dualAction K (d ell))).Equiv
      ((dualAction K (d 0)).prod
        (Representation.directSum (fun ell : Fin k => dualAction K (d ell.succ)))) :=
  Representation.Equiv.mk
    ((DirectSum.linearEquivFunOnFintype K (Fin (k + 1))
        (fun ell => DualPower K (d ell))).trans
      ((Fin.consLinearEquiv K (fun ell => DualPower K (d ell))).symm.trans
        ((LinearEquiv.refl K (DualPower K (d 0))).prodCongr
          (DirectSum.linearEquivFunOnFintype K (Fin k)
            (fun ell => DualPower K (d ell.succ))).symm))) fun c => by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · apply DFinsupp.ext
      intro ell
      rfl

def directSumCongr {α : Type*} [DecidableEq α]
    (d e : α → ℕ) (h : d = e) :
    (Representation.directSum (fun a => dualAction K (d a))).Equiv
      (Representation.directSum (fun a => dualAction K (e a))) := by
  subst e
  exact Representation.Equiv.refl _

private def layerConsEquiv (i j h k : ℕ) :
    (layerAction (K := K) i j h (k + 1)).Equiv
      ((dualAction K (i + j - (2 * h + 1))).prod
        (layerAction (K := K) i j (h + 1) k)) := by
  let e₀ := directSumConsEquiv (K := K) k
    (fun ell => i + j - (2 * (h + ell.val) + 1))
  let e₁ := directSumCongr (K := K)
    (fun ell : Fin k => i + j - (2 * (h + ell.succ.val) + 1))
    (fun ell : Fin k => i + j - (2 * ((h + 1) + ell.val) + 1))
    (by
      change (fun ell : Fin k => i + j - (2 * (h + ell.succ.val) + 1)) =
        (fun ell : Fin k => i + j - (2 * ((h + 1) + ell.val) + 1))
      funext ell
      change i + j - (2 * (h + (ell.val + 1)) + 1) =
        i + j - (2 * ((h + 1) + ell.val) + 1)
      omega)
  exact e₀.trans (prodCongr (Representation.Equiv.refl _) e₁)

private def emptyLayers (i j h : ℕ) {A : Type u} [AddCommGroup A] [Module K A]
    (ρ : Representation K (Multiplicative K) A) :
    ρ.Equiv ((layerAction (K := K) i j h 0).prod ρ) :=
  Representation.Equiv.mk
    { toFun := fun x => (0, x)
      invFun := Prod.snd
      left_inv := fun _ => rfl
      right_inv := fun x => by
        apply Prod.ext
        · apply DFinsupp.ext
          intro ell
          exact Fin.elim0 ell
        · rfl
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp } fun c => by
    apply LinearMap.ext
    intro x
    exact Prod.ext (map_zero ((layerAction (K := K) i j h 0) c)).symm rfl

/-- Iteration of the ACTUAL split equivalences, with explicit Fin-cons
reindexing. The hypotheses here describe individual steps; the classification
below supplies every one of them from its sole high-binomial condition. -/
theorem iterated_tensor_split (i j h k : ℕ)
    (hi : h + k ≤ i) (hj : h + k ≤ j)
    (hsteps : ∀ r, h ≤ r → r < h + k →
      ((i + j - 2 - 2 * r).choose (i - 1 - r) : K) ≠ 0) :
    Nonempty ((tensorAction (K := K) (i - h) (j - h)).Equiv
      ((layerAction (K := K) i j h k).prod
        (tensorAction (K := K) (i - (h + k)) (j - (h + k))))) := by
  induction k generalizing h with
  | zero =>
    exact ⟨by simpa only [Nat.add_zero] using
      emptyLayers i j h (tensorAction (K := K) (i - h) (j - h))⟩
  | succ k ih =>
    have hi0 : 0 < i - h := by omega
    have hj0 : 0 < j - h := by omega
    have hN : (i - h) + (j - h) - 2 = i + j - 2 - 2 * h := by omega
    have hn : i - h - 1 = i - 1 - h := by omega
    let e := tensor_split (K := K) (i - h) (j - h) hi0 hj0
      (by rw [hN, hn]; exact hsteps h le_rfl (by omega))
    obtain ⟨e'⟩ := ih (h + 1) (by omega) (by omega)
      (fun r hr hr' => hsteps r (by omega) (by omega))
    have htop : (i - h) + (j - h) - 1 = i + j - (2 * h + 1) := by omega
    have hi' : i - h - 1 = i - (h + 1) := by omega
    have hj' : j - h - 1 = j - (h + 1) := by omega
    have hsum : (h + 1) + k = h + (k + 1) := by omega
    have e₀ : (tensorAction (K := K) (i - h) (j - h)).Equiv
        ((dualAction K (i + j - (2 * h + 1))).prod
          (tensorAction (K := K) (i - (h + 1)) (j - (h + 1)))) := by
      have transfer (d r s : ℕ) (hd : d = (i - h) + (j - h) - 1)
          (hr : r = i - h - 1) (hs : s = j - h - 1) :
          (tensorAction (K := K) (i - h) (j - h)).Equiv
            ((dualAction K d).prod (tensorAction (K := K) r s)) := by
        subst d r s
        exact e
      exact transfer _ _ _ htop.symm hi'.symm hj'.symm
    let e₁ := e₀.trans (prodCongr (Representation.Equiv.refl _) e')
    let e₂ := e₁.trans ((prodAssoc (dualAction K (i + j - (2 * h + 1)))
      (layerAction (K := K) i j (h + 1) k)
      (tensorAction (K := K) (i - ((h + 1) + k)) (j - ((h + 1) + k)))).symm)
    have transfer (z : ℕ) (hz : z = (h + 1) + k) :
        Nonempty ((tensorAction (K := K) (i - h) (j - h)).Equiv
          ((layerAction (K := K) i j h (k + 1)).prod
            (tensorAction (K := K) (i - z) (j - z)))) := by
      subst z
      exact ⟨e₂.trans
        (prodCongr (layerConsEquiv i j h k).symm (Representation.Equiv.refl _))⟩
    exact transfer _ hsum.symm

end ActualFiniteSum

section RelativeComplement

variable {K : Type u} [Field K] {G M A B : Type u} [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

theorem relativeProjective_transport (τ : Representation K G M)
    {ρ : Representation K G A} {σ : Representation K G B} (e : ρ.Equiv σ)
    (hρ : RelativeProjective τ (Rep.of ρ)) : RelativeProjective τ (Rep.of σ) := by
  obtain ⟨X, i, r, hri⟩ := hρ
  refine ⟨X, i.comp e.symm.toIntertwiningMap, e.toIntertwiningMap.comp r, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change e (r (i (e.symm x))) = x
  have hx := congrArg (fun k => k (e.symm x)) hri
  change r (i (e.symm x)) = e.symm x at hx
  rw [hx, e.apply_symm_apply]

private theorem relativeProjective_of_subsingleton (τ : Representation K G M)
    (ρ : Representation K G A) [Subsingleton A] :
    RelativeProjective τ (Rep.of ρ) := by
  refine ⟨Rep.of (Representation.trivial K G K), 0, 0, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

end RelativeComplement

section ResidueComplement

variable {K : Type u} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- Transport the actual dual-tensor retract proof to the literal
tensor V_(pa) tensor V_m. Its witnesses use relativeInclusion/projection of
the named summand a-1 and the actual tensor flip, including all X/P quantifiers. -/
theorem multiple_tensor_relativeProjective (s a m : ℕ) (ha : a ≤ s) :
    RelativeProjective (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
      (Rep.of (tensorAction (K := K) (p * a) m)) := by
  by_cases ha0 : a = 0
  · subst a
    simpa only [Nat.mul_zero] using
      relativeProjective_of_subsingleton
        (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
        (tensorAction (K := K) 0 m)
  have ha0' : 0 < a := Nat.pos_of_ne_zero ha0
  let c : Fin s := ⟨a - 1, by omega⟩
  have hdim : p * (c.val + 1) = p * a := by
    congr 1
    dsimp only [c]
    omega
  letI : Module.Finite K (Primal K (p * (c.val + 1))) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K (p * (c.val + 1)))
  letI : Module.Finite K (Primal K m) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K m)
  have hP := relativeProjective_transport
    (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
    (dualTensorEquiv (primalAction K (p * (c.val + 1))) (primalAction K m)).symm
    (dualTensor_relativeProjective (K := K) (p := p) s c m)
  have transfer (d : ℕ) (hd : d = p * (c.val + 1)) :
      RelativeProjective (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
        (Rep.of (tensorAction (K := K) d m)) := by
    subst d
    exact hP
  exact transfer _ hdim.symm

/-- One of the two actual remaining factors has dimension pa or pb.
The zero cases and either choice of the smaller residue are retained. -/
theorem residue_remainder_relativeProjective (s a b u v : ℕ)
    (ha : a ≤ s) (hb : b ≤ s) :
    RelativeProjective (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
      (Rep.of (tensorAction (K := K)
        (p * a + u - min u v) (p * b + v - min u v))) := by
  rcases le_total u v with huv | hvu
  · have ht : min u v = u := min_eq_left huv
    have hi : p * a + u - min u v = p * a := by rw [ht]; omega
    rw [hi]
    exact multiple_tensor_relativeProjective s a _ ha
  · have ht : min u v = v := min_eq_right hvu
    have hj : p * b + v - min u v = p * b := by rw [ht]; omega
    rw [hj]
    exact relativeProjective_transport _
      (Representation.TensorProduct.comm (dualAction K (p * b))
        (dualAction K (p * a + u - min u v)))
      (multiple_tensor_relativeProjective s b _ hb)

/-- The finite sum produced by the iteration is the required Fin(min u v)
sum, and the remainder is the literal tensor with each dimension decreased
by min u v. This is stronger than a relative stable isomorphism. -/
theorem residue_decomposition (a b u v : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u + v ≤ p)
    (hchoose : ((a + b).choose a : K) ≠ 0) :
    Nonempty ((tensorAction (K := K) (p * a + u) (p * b + v)).Equiv
      ((expectedAction (K := K) (p * a + u) (p * b + v) (min u v)).prod
        (tensorAction (K := K)
          (p * a + u - min u v) (p * b + v - min u v)))) := by
  have htu : min u v ≤ u := min_le_left u v
  have htv : min u v ≤ v := min_le_right u v
  obtain ⟨e⟩ := iterated_tensor_split (K := K)
    (p * a + u) (p * b + v) 0 (min u v) (by omega) (by omega)
    (fun r _ hr => step_choose_ne_zero a b u v r hu hv huv
      (by simpa only [Nat.zero_add] using hr) hchoose)
  have transfer (z : ℕ) (hz : z = 0 + min u v) :
      Nonempty ((tensorAction (K := K) (p * a + u) (p * b + v)).Equiv
        ((layerAction (K := K) (p * a + u) (p * b + v) 0 (min u v)).prod
          (tensorAction (K := K) (p * a + u - z) (p * b + v - z)))) := by
    subst z
    exact ⟨e⟩
  obtain ⟨e'⟩ := transfer (min u v) (Nat.zero_add _).symm
  let eS := directSumCongr (K := K)
    (fun ell : Fin (min u v) =>
      (p * a + u) + (p * b + v) - (2 * (0 + ell.val) + 1))
    (fun ell : Fin (min u v) =>
      (p * a + u) + (p * b + v) - (2 * ell.val + 1))
    (by
      change (fun ell : Fin (min u v) =>
          (p * a + u) + (p * b + v) - (2 * (0 + ell.val) + 1)) =
        (fun ell : Fin (min u v) =>
          (p * a + u) + (p * b + v) - (2 * ell.val + 1))
      funext ell
      rw [Nat.zero_add])
  exact ⟨e'.trans (prodCongr eS (Representation.Equiv.refl _))⟩

end ResidueComplement

section FinalRelativeMaps

variable {K G M A B C : Type u} [Field K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]

/-- Given the constructed actual decomposition, the inverse errors factor
through exactly its actual remainder. The second error has a negative sign. -/
theorem relativeStableIso_of_decomposition (τ : Representation K G M)
    (ρ : Representation K G A) (σ : Representation K G B)
    (κ : Representation K G C) (e : σ.Equiv (ρ.prod κ))
    (hκ : RelativeProjective τ (Rep.of κ)) : RelativeStableIso τ ρ σ := by
  let inS := Representation.IntertwiningMap.inl K ρ κ
  let prS := Representation.IntertwiningMap.fst K ρ κ
  let inR := Representation.IntertwiningMap.inr K ρ κ
  let prR := Representation.IntertwiningMap.snd K ρ κ
  let f := e.symm.toIntertwiningMap.comp inS
  let g := prS.comp e.toIntertwiningMap
  have hgf : g.comp f = .id ρ := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (e (e.symm (x, 0))).1 = x
    rw [e.apply_symm_apply]
  refine ⟨f, g, ?_, ?_⟩
  · rw [hgf, sub_self]
    exact relativeFactors_zero τ ρ ρ
  · refine ⟨Rep.of κ, hκ, prR.comp e.toIntertwiningMap,
      -(e.symm.toIntertwiningMap.comp inR), ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change -e.symm (0, (e x).2) = e.symm ((e x).1, 0) - x
    apply e.injective
    rw [map_neg, map_sub]
    change -e.toLinearEquiv (e.toLinearEquiv.symm (0, (e x).2)) =
      e.toLinearEquiv (e.toLinearEquiv.symm ((e x).1, 0)) - e.toLinearEquiv x
    rw [e.toLinearEquiv.apply_symm_apply, e.toLinearEquiv.apply_symm_apply]
    apply Prod.ext <;> simp

end FinalRelativeMaps

section FirstSummandObstruction

variable {K : Type u} [Field K] [Fintype K]
  {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- Literal inclusion and projection of ell=0 in the required full sum. -/
def firstInclusion (i j t : ℕ) (ht : 0 < t) :
    (dualAction K (i + j - 1)).IntertwiningMap
      (expectedAction (K := K) i j t) where
  toLinearMap := DirectSum.lof K (Fin t)
    (fun ell => DualPower K (i + j - (2 * ell.val + 1))) ⟨0, ht⟩
  isIntertwining' c := by
    apply LinearMap.ext
    intro x
    exact (DirectSum.lmap_lof
      (fun ell : Fin t => dualAction K (i + j - (2 * ell.val + 1)) c)
      ⟨0, ht⟩ x).symm

def firstProjection (i j t : ℕ) (ht : 0 < t) :
    (expectedAction (K := K) i j t).IntertwiningMap
      (dualAction K (i + j - 1)) where
  toLinearMap := DirectSum.component K (Fin t)
    (fun ell => DualPower K (i + j - (2 * ell.val + 1))) ⟨0, ht⟩
  isIntertwining' c := by
    apply LinearMap.ext
    intro x
    rfl

theorem firstProjection_inclusion (i j t : ℕ) (ht : 0 < t) :
    (firstProjection (K := K) i j t ht).comp (firstInclusion i j t ht) =
      .id (dualAction K (i + j - 1)) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact DirectSum.component.lof_self (R := K) (ι := Fin t)
    (M := fun ell : Fin t => DualPower K (i + j - (2 * ell.val + 1))) ⟨0, ht⟩ x

/-- The arbitrary-morphism rectangle obstruction is applied AFTER sandwiching
the stable error. No assertion U ~ T is made, and the SAME P is retained. -/
theorem no_stableIso_with_retract {A : Type u} [AddCommGroup A] [Module K A]
    (s n m d : ℕ) (hU : d = n + m + 1)
    (hsize : n + m + 2 ≤ Fintype.card K)
    (hchoose : ((n + m).choose n : K) = 0)
    (hdim : (d : K) ≠ 0)
    (σ : Representation K (Multiplicative K) A)
    (jU : (dualAction K d).IntertwiningMap σ)
    (pU : σ.IntertwiningMap (dualAction K d))
    (hpj : pU.comp jU = .id (dualAction K d)) :
    ¬ RelativeStableIso (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
      σ (RectangularTensorObstruction.tensorAction K n m) := by
  subst d
  intro hs
  obtain ⟨f, g, hS, _⟩ := hs
  let fU := f.comp jU
  let gU := pU.comp g
  have herror : RelativeFactors
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
      (gU.comp fU - .id (dualAction K (n + m + 1))) := by
    obtain ⟨P, hP, α, β, hβα⟩ := hS
    refine ⟨P, hP, α.comp jU, pU.comp β, ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change pU (β (α (jU x))) = pU (g (f (jU x))) - x
    have hx := congrArg (fun k => k (jU x)) hβα
    change β (α (jU x)) = g (f (jU x)) - jU x at hx
    have hpx := congrArg (fun k => k x) hpj
    change pU (jU x) = x at hpx
    rw [hx, map_sub, hpx]
  letI : Module.Finite K (DualPower K (n + m + 1)) :=
    Module.Finite.of_basis (dualBasis K (n + m + 1))
  have hid : LinearMap.trace K (DualPower K (n + m + 1)) LinearMap.id =
      ((n + m + 1 : ℕ) : K) := by
    rw [LinearMap.trace_id, Module.finrank_eq_card_basis (dualBasis K (n + m + 1))]
    simp
  have htrace := PrimeCyclicRelativeTrace.trace_relativeFactors s _ _ herror
  have hrect := RectangularTensorObstruction.composition_trace_zero n m hsize hchoose fU gU
  change LinearMap.trace K (DualPower K (n + m + 1))
    (gU.toLinearMap.comp fU.toLinearMap - LinearMap.id) = 0 at htrace
  rw [map_sub, hrect, hid] at htrace
  exact hdim (neg_eq_zero.mp (by simpa only [zero_sub] using htrace))

theorem not_stableIso_of_zero_choose (s i j t : ℕ)
    (hi : 0 < i) (hj : 0 < j) (ht : 0 < t)
    (hsize : i + j ≤ Fintype.card K)
    (hchoose : ((i + j - 2).choose (i - 1) : K) = 0)
    (hdim : ((i + j - 1 : ℕ) : K) ≠ 0) :
    ¬ RelativeStableIso (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
      (expectedAction (K := K) i j t) (tensorAction (K := K) i j) := by
  have hn : i - 1 + 1 = i := by omega
  have hm : j - 1 + 1 = j := by omega
  have hN : (i - 1) + (j - 1) = i + j - 2 := by omega
  have htop : (i - 1) + (j - 1) + 1 = i + j - 1 := by omega
  have hnot := no_stableIso_with_retract (K := K) (p := p)
    s (i - 1) (j - 1) (i + j - 1) htop.symm (by omega)
    (by simpa only [hN] using hchoose) hdim
    (expectedAction (K := K) i j t)
    (firstInclusion (K := K) i j t ht) (firstProjection (K := K) i j t ht)
    (firstProjection_inclusion (K := K) i j t ht)
  have transfer (r s' : ℕ) (hr : r = i - 1 + 1) (hs' : s' = j - 1 + 1) :
      ¬ RelativeStableIso (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
        (expectedAction (K := K) i j t) (tensorAction (K := K) r s') := by
    subst r s'
    exact hnot
  exact transfer i j hn.symm hm.symm

end FirstSummandObstruction

section Classification

variable {K : Type u} [Field K] [Fintype K]
  {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- The dimension of the FIRST actual summand has nonzero characteristic
residue u+v-1, including u+v=p and p=2. -/
theorem first_dimension_ne_zero (a b u v : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : u + v ≤ p) :
    (((p * a + u) + (p * b + v) - 1 : ℕ) : K) ≠ 0 := by
  have hsum : (p * a + u) + (p * b + v) = p * (a + b) + (u + v) := by ring
  have hdim : (p * a + u) + (p * b + v) - 1 =
      p * (a + b) + (u + v - 1) := by rw [hsum]; omega
  rw [hdim, Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero K p, zero_mul, zero_add]
  intro hz
  have hd : p ∣ u + v - 1 := (CharP.cast_eq_zero_iff K p _).mp hz
  have hp_le := Nat.le_of_dvd (by omega : 0 < u + v - 1) hd
  omega

/-- Full nonzero-low-residue correction to Elmer--Kadr 3.7(a) for the
finite-field additive-group realization. S is the ACTUAL Fin(min u v) direct
sum of V_(i+j-(2*ell+1)); T and M have their original literal actions.

The only high-digit condition is the displayed nonvanishing binomial. All
boundary cases a=0 or b=0 remain included. No result about 3.7(b) is claimed.
-/
theorem residue_criterion_binomial (a b u v : ℕ)
    (hu : 1 ≤ u) (hup : u < p) (hv : 1 ≤ v) (hvp : v < p)
    (huv : u + v ≤ p)
    (hsize : (p * a + u) + (p * b + v) ≤ Fintype.card K) :
    RelativeStableIso
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) (Fintype.card K / p))
      (expectedAction (K := K) (p * a + u) (p * b + v) (min u v))
      (tensorAction (K := K) (p * a + u) (p * b + v)) ↔
        ((a + b).choose a : K) ≠ 0 := by
  classical
  have ht : 0 < min u v := by omega
  constructor
  · intro hstable
    by_cases hz : ((a + b).choose a : K) = 0
    · have hfactor := step_choose_factorization (K := K) a b u v 0 hu hv huv ht
      have hzero : (((p * a + u) + (p * b + v) - 2).choose
          (p * a + u - 1) : K) = 0 := by
        simpa only [Nat.mul_zero, Nat.sub_zero, hz, mul_zero] using hfactor
      exact False.elim ((not_stableIso_of_zero_choose
        (Fintype.card K / p) (p * a + u) (p * b + v) (min u v)
        (by omega) (by omega) ht hsize hzero
        (first_dimension_ne_zero a b u v hu hv huv)) hstable)
    · exact hz
  · intro hchoose
    have ha : a ≤ Fintype.card K / p := by
      apply (Nat.le_div_iff_mul_le hp.out.pos).mpr
      rw [Nat.mul_comm]
      omega
    have hb : b ≤ Fintype.card K / p := by
      apply (Nat.le_div_iff_mul_le hp.out.pos).mpr
      rw [Nat.mul_comm]
      omega
    obtain ⟨e⟩ := residue_decomposition a b u v hu hv huv hchoose
    exact relativeStableIso_of_decomposition _ _ _ _ e
      (residue_remainder_relativeProjective (Fintype.card K / p) a b u v ha hb)


end Classification

section AllResidues

variable {K : Type u} [Field K] [Fintype K]
  {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- All low residues, including either zero residue, for the original M,
the actual expected direct sum S, and the original tensor action T.
The high-binomial condition is necessary only when both low residues are
nonzero. This includes a=0, b=0, zero spaces, p=2, u+v=p and i+j=card K.
-/
theorem residue_criterion_all (a b u v : ℕ)
    (hup : u < p) (hvp : v < p) (huv : u + v ≤ p)
    (hsize : (p * a + u) + (p * b + v) ≤ Fintype.card K) :
    RelativeStableIso
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) (Fintype.card K / p))
      (expectedAction (K := K) (p * a + u) (p * b + v) (min u v))
      (tensorAction (K := K) (p * a + u) (p * b + v)) ↔
        u = 0 ∨ v = 0 ∨ ((a + b).choose a : K) ≠ 0 := by
  have ha : a ≤ Fintype.card K / p := by
    apply (Nat.le_div_iff_mul_le hp.out.pos).2
    rw [Nat.mul_comm a p]
    omega
  have hb : b ≤ Fintype.card K / p := by
    apply (Nat.le_div_iff_mul_le hp.out.pos).2
    rw [Nat.mul_comm b p]
    omega
  have hzero (hz : u = 0 ∨ v = 0) :
      RelativeStableIso
        (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
          (Fintype.card K / p))
        (expectedAction (K := K) (p * a + u) (p * b + v) (min u v))
        (tensorAction (K := K) (p * a + u) (p * b + v)) := by
    have hmin : min u v = 0 := by
      rcases hz with hu0 | hv0
      · simp only [hu0, Nat.zero_min]
      · simp only [hv0, Nat.min_zero]
    have hP : RelativeProjective
        (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
          (Fintype.card K / p))
        (Rep.of (tensorAction (K := K) (p * a + u) (p * b + v))) := by
      rcases hz with hu0 | hv0
      · have transfer (d : ℕ) (hd : d = p * a) :
            RelativeProjective
              (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
                (Fintype.card K / p))
              (Rep.of (tensorAction (K := K) d (p * b + v))) := by
          subst d
          exact multiple_tensor_relativeProjective (K := K) (p := p)
            (Fintype.card K / p) a (p * b + v) ha
        exact transfer _ (by omega)
      · have hPb := multiple_tensor_relativeProjective (K := K) (p := p)
          (Fintype.card K / p) b (p * a + u) hb
        have hflip := relativeProjective_transport
          (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
            (Fintype.card K / p))
          (Representation.TensorProduct.comm (dualAction K (p * b))
            (dualAction K (p * a + u))) hPb
        have transfer (d : ℕ) (hd : d = p * b) :
            RelativeProjective
              (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
                (Fintype.card K / p))
              (Rep.of (tensorAction (K := K) (p * a + u) d)) := by
          subst d
          exact hflip
        exact transfer _ (by omega)
    have e : (tensorAction (K := K) (p * a + u) (p * b + v)).Equiv
        ((expectedAction (K := K) (p * a + u) (p * b + v) 0).prod
          (tensorAction (K := K) (p * a + u) (p * b + v))) := by
      let eS := directSumCongr (K := K)
        (fun ell : Fin 0 =>
          (p * a + u) + (p * b + v) - (2 * (0 + ell.val) + 1))
        (fun ell : Fin 0 =>
          (p * a + u) + (p * b + v) - (2 * ell.val + 1))
        (by funext ell; exact Fin.elim0 ell)
      exact (emptyLayers (p * a + u) (p * b + v) 0
        (tensorAction (K := K) (p * a + u) (p * b + v))).trans
          (prodCongr eS (Representation.Equiv.refl _))
    rw [hmin]
    exact relativeStableIso_of_decomposition _ _ _ _ e hP
  by_cases hu0 : u = 0
  · exact ⟨fun _ => Or.inl hu0, fun _ => hzero (Or.inl hu0)⟩
  by_cases hv0 : v = 0
  · exact ⟨fun _ => Or.inr (Or.inl hv0), fun _ => hzero (Or.inr hv0)⟩
  have hnonzero := residue_criterion_binomial (K := K) (p := p) a b u v
    (by omega) hup (by omega) hvp huv hsize
  constructor
  · intro hs
    exact Or.inr (Or.inr (hnonzero.mp hs))
  · intro hcases
    rcases hcases with hu | hv | hchoose
    · exact False.elim (hu0 hu)
    · exact False.elim (hv0 hv)
    · exact hnonzero.mpr hchoose

/-- The complete original-M classification, expressed by Kummer's exact
no-carry condition, with both zero low residues unconditional. The empty
interval at a=b=0 is retained. -/
theorem residue_criterion (a b u v : ℕ)
    (hup : u < p) (hvp : v < p)
    (huv : u + v ≤ p)
    (hsize : (p * a + u) + (p * b + v) ≤ Fintype.card K) :
    RelativeStableIso
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) (Fintype.card K / p))
      (expectedAction (K := K) (p * a + u) (p * b + v) (min u v))
      (tensorAction (K := K) (p * a + u) (p * b + v)) ↔
        u = 0 ∨ v = 0 ∨ ∀ k ∈ Finset.Ico 1 (Nat.log p (a + b) + 1),
          a % p ^ k + b % p ^ k < p ^ k := by
  rw [residue_criterion_all a b u v hup hvp huv hsize]
  refine or_congr Iff.rfl (or_congr Iff.rfl ?_)
  rw [ne_eq, CharP.cast_eq_zero_iff K p]
  have hchoose : (a + b).choose a ≠ 0 := Nat.choose_ne_zero (by omega)
  have hval : ((a + b).choose a).factorization p = 0 ↔ ¬p ∣ (a + b).choose a := by
    simp only [Nat.factorization_eq_zero_iff, hp.out, not_true,
      hchoose, or_false, false_or]
  rw [← hval]
  have hk := Nat.factorization_choose' (p := p) (n := b) (k := a)
    (b := Nat.log p (a + b) + 1) hp.out
    (by rw [Nat.add_comm b a]; omega)
  rw [Nat.add_comm b a] at hk
  rw [hk, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [not_le]


end AllResidues

end D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrResidueCriterion
