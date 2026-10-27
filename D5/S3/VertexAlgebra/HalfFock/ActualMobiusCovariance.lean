/- GID: D5/S3/VertexAlgebra/HalfFock/ActualMobiusCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/ActualMobiusCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original all-source physical L1 coefficient covariance by evaluated insertion. -/

import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentWard
import D5.S3.VertexAlgebra.SourceMobius.PositiveMode
import D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity

/-! Classical twisted lattice construction; original conventions and notices
are inherited from the imported owners. The endpoint retains all original
sources, signed exponents and the actual tensor action. Charged, singleton,
scalar cancellation and insertion lemmas are consumed by the full-source proof.
The physical coordinate is z = t². -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open scoped BigOperators TensorProduct
noncomputable section

/-- The scalar Pascal step for the original normalized jets. -/
private theorem jet_shift (r : ℕ) (j : ℤ) :
    jetScalar (r + 1) (j - 1) = jetScalar (r + 1) j + jetScalar r j := by
  induction r with
  | zero => simp [jetScalar, Finset.prod_range_succ]; ring
  | succ r ih =>
    have hleft := LatticeHalfFockOriginalTranslation.jet_successor (r + 1) (j - 1)
    have hright := LatticeHalfFockOriginalTranslation.jet_successor (r + 1) j
    have hlower := LatticeHalfFockOriginalTranslation.jet_successor r j
    rw [ih] at hleft
    have hn : (r + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : r + 2 ≠ 0)
    apply (mul_left_cancel₀ hn)
    push_cast at hleft hright hlower ⊢
    linear_combination hleft - hright - hlower

/-- The only scalar product rule needed for the L1 singleton commutator. -/
private theorem jet_l1_scalar (r : ℕ) (j : ℤ) :
    ((j : ℂ) - (r : ℂ) - 1/2) * jetScalar r j -
        ((j : ℂ) - 1/2) * jetScalar r (j - 1) =
      if r = 0 then 0 else (r + 1 : ℂ) * jetScalar (r - 1) j := by
  cases r with
  | zero => simp [jetScalar]
  | succ r =>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    rw [jet_shift]
    have h := LatticeHalfFockOriginalTranslation.jet_successor r j
    linear_combination -h

private theorem jet_boundary (r : ℕ) : jetScalar r (-1) = halfBinomial r := by
  unfold jetScalar halfBinomial
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  push_cast
  ring

private theorem actual_current_l1 (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (j : ℤ) :
    tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 *
        tensorCurrent D (ActualGround D hu) i j -
      tensorCurrent D (ActualGround D hu) i j *
        tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 =
      (-((j : ℂ) + 1/2)) • tensorCurrent D (ActualGround D hu) i (j + 1) := by
  apply TensorProduct.ext'
  intro p t
  have h := congrArg (fun U : Module.End ℂ (Oscillator D) => U p ⊗ₜ[ℂ] t)
    (L_current_commutator D (HalfFockSpectralFiberSource.actualInverse D)
      (HalfFockSpectralFiberSource.actualInverse_left D hu)
      (HalfFockSpectralFiberSource.actualInverse_right D hu) i 1 j)
  simpa only [tensorL, tensorCurrent, tensorEnd, Module.End.mul_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, TensorProduct.sub_tmul, TensorProduct.smul_tmul',
    frequency, add_comm 1 j] using h


private theorem flat_singleton_jet (D : LatticeData) (hu : IsUnit D.G.det)
    (F : NativeField D hu) (i : Fin D.rank) (r : ℕ) (j e : ℤ) :
    flatCoefficient D hu F [(i,r)] (j,()) e =
      jetScalar r j • flatCoefficient D hu F [(i,0)] (j,()) (e+2*(r:ℤ)) := by
  have scalar0 (k : ℤ) : jetScalar 0 k = 1 := by simp [jetScalar]
  have shift : e+2*(r:ℤ)+2*j+3 = e+2*j+2*(r:ℤ)+3 := by omega
  simp only [flatCoefficient, jetCurrent, scalar0, Nat.cast_zero, mul_zero, add_zero, one_smul, shift]
  split_ifs <;> simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

/-- A single original normal-order term. The hypothesis is local induction
information on the shorter source, not an assumption of the final theorem.
The only exceptional reindexing is j=-1 to the nonnegative mode 0. -/
private theorem singleton_term_l1 (D : LatticeData) (hu : IsUnit D.G.det)
    (F G H : NativeField D hu)
    (hF : ∀ d : ℤ,
      tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 * F.coeff d -
        F.coeff d * tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 =
      G.coeff d + ((d : ℂ)/2-1) • F.coeff (d-2) + (2 : ℂ) • H.coeff (d-2))
    (i : Fin D.rank) (r : ℕ) (j e : ℤ) :
    tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 *
        flatCoefficient D hu F [(i,r)] (j,()) e -
      flatCoefficient D hu F [(i,r)] (j,()) e *
        tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 =
      flatCoefficient D hu G [(i,r)] (j,()) e +
        (((e+2*j+2*(r:ℤ)+3 : ℤ):ℂ)/2-1) •
          flatCoefficient D hu F [(i,r)] (j,()) (e-2) +
        (2 : ℂ) • flatCoefficient D hu H [(i,r)] (j,()) (e-2) +
        (-frequency j * jetScalar r j) •
          flatCoefficient D hu F [(i,0)] (j+1,()) (e+2*(r:ℤ)-2) +
        if j = -1 then (1/2 * halfBinomial r : ℂ) •
          (tensorCurrent D (ActualGround D hu) i 0 * F.coeff (e+2*(r:ℤ)+1) -
            F.coeff (e+2*(r:ℤ)+1) * tensorCurrent D (ActualGround D hu) i 0)
        else 0 := by
  let T := tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1
  let J := tensorCurrent D (ActualGround D hu) i
  have hc (k : ℤ) : T * J k - J k * T = (-frequency k) • J (k+1) := by
    exact actual_current_l1 D hu i k
  have left (k d : ℤ) : T * (J k * F.coeff d) - (J k * F.coeff d) * T =
      (-frequency k) • (J (k+1) * F.coeff d) + J k * G.coeff d +
        ((d:ℂ)/2-1) • (J k * F.coeff (d-2)) + (2 : ℂ) • (J k * H.coeff (d-2)) := by
    calc
      _ = (T*J k-J k*T)*F.coeff d + J k*(T*F.coeff d-F.coeff d*T) := by noncomm_ring
      _ = _ := by
        rw [hc, hF]
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, mul_add]
        abel
  have right (k d : ℤ) : T * (F.coeff d * J k) - (F.coeff d * J k) * T =
      G.coeff d * J k + ((d:ℂ)/2-1) • (F.coeff (d-2)*J k) +
        (2 : ℂ) • (H.coeff (d-2)*J k) + (-frequency k) • (F.coeff d * J (k+1)) := by
    calc
      _ = (T*F.coeff d-F.coeff d*T)*J k + F.coeff d*(T*J k-J k*T) := by noncomm_ring
      _ = _ := by
        rw [hc, hF]
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, add_mul]
  have scalar0 (k : ℤ) : jetScalar 0 k = 1 := by simp [jetScalar]
  have down : e-2+2*j+2*(r:ℤ)+3 = (e+2*j+2*(r:ℤ)+3)-2 := by omega
  have next : e+2*(r:ℤ)-2+2*(j+1)+3 = e+2*j+2*(r:ℤ)+3 := by omega
  simp only [flatCoefficient, jetCurrent, scalar0, Nat.cast_zero, mul_zero, add_zero, one_smul]
  simp only [down, next]
  change T * _ - _ * T = _
  by_cases cross : j = -1
  · subst j
    simp only [show (-1 : ℤ) < 0 by omega, ite_true,
      show ¬ (-1+1 : ℤ) < 0 by omega, ite_false, neg_add_cancel,
      show e+2*(-1)+2*(r:ℤ)+3 = e+2*(r:ℤ)+1 by omega]
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]
    rw [left]
    simp only [jet_boundary]
    simp only [frequency, Int.cast_neg, Int.cast_one, neg_add_cancel,
      lt_self_iff_false, ite_false]
    module
  · have signs : (j+1 < 0) ↔ j < 0 := by omega
    simp only [if_neg cross, signs, add_zero]
    by_cases negative : j < 0
    · simp only [negative, ite_true, if_neg cross, add_zero]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]
      rw [left]
      module
    · simp only [negative, ite_false, if_neg cross, add_zero]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]
      rw [right]
      module


/-- Pointwise summation of the original singleton commutator. Only the shorter
source law hF is used. No endomorphism-valued global support is assumed. -/
private theorem singleton_l1 (D : LatticeData) (hu : IsUnit D.G.det)
    (F G H : NativeField D hu)
    (hF : ∀ d : ℤ,
      tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 * F.coeff d -
        F.coeff d * tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 =
      G.coeff d + ((d : ℂ)/2-1) • F.coeff (d-2) + (2 : ℂ) • H.coeff (d-2))
    (i : Fin D.rank) (r : ℕ) (e : ℤ) (x : ActualTensor D hu) :
    tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1
        ((singletonLinear D hu (i,r) F).coeff e x) -
      (singletonLinear D hu (i,r) F).coeff e
        (tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 x) =
      (singletonLinear D hu (i,r) G).coeff e x +
        ((e : ℂ)/2-1+2*(r+1 : ℂ)) • (singletonLinear D hu (i,r) F).coeff (e-2) x +
        (2 : ℂ) • (singletonLinear D hu (i,r) H).coeff (e-2) x +
        (if r = 0 then 0 else (r+1 : ℂ) • (singletonLinear D hu (i,r-1) F).coeff e x) +
        (1/2 * halfBinomial r : ℂ) •
          (tensorCurrent D (ActualGround D hu) i 0 (F.coeff (e+2*(r:ℤ)+1) x) -
            F.coeff (e+2*(r:ℤ)+1) (tensorCurrent D (ActualGround D hu) i 0 x)) := by
  classical
  let T := tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1
  have finite (A : NativeField D hu) (s : ℕ) (d : ℤ) (v : ActualTensor D hu) :
      Function.HasFiniteSupport (fun j : ℤ => flatCoefficient D hu A [(i,s)] (j,()) d v) := by
    have inj : Function.Injective (fun j : ℤ => (j, ())) :=
      fun a b h => congrArg Prod.fst h
    exact (flatTerm_finite D hu A [(i,s)] d v).fun_comp_of_injective inj
  let u := fun j : ℤ => flatCoefficient D hu F [(i,r)] (j,()) (e-2) x
  let v := fun j : ℤ => flatCoefficient D hu F [(i,0)] (j,()) (e+2*(r:ℤ)-2) x
  let g := fun j : ℤ => flatCoefficient D hu G [(i,r)] (j,()) e x
  let h := fun j : ℤ => flatCoefficient D hu H [(i,r)] (j,()) (e-2) x
  let b := fun j : ℤ => (((e+2*j+2*(r:ℤ)+3 : ℤ):ℂ)/2-1) • u j
  let k := fun j : ℤ => (-frequency (j-1) * jetScalar r (j-1)) • v j
  let l := fun j : ℤ => if r = 0 then 0 else
    (r+1 : ℂ) • flatCoefficient D hu F [(i,r-1)] (j,()) e x
  let c : ℂ := (e:ℂ)/2-1+2*(r+1 : ℂ)
  let B : ActualTensor D hu := (1/2 * halfBinomial r : ℂ) •
    (tensorCurrent D (ActualGround D hu) i 0 (F.coeff (e+2*(r:ℤ)+1) x) -
      F.coeff (e+2*(r:ℤ)+1) (tensorCurrent D (ActualGround D hu) i 0 x))
  let w := fun j : ℤ => if j = -1 then B else 0
  have fu : Function.HasFiniteSupport u := finite F r (e-2) x
  have fv : Function.HasFiniteSupport v := finite F 0 (e+2*(r:ℤ)-2) x
  have fg : Function.HasFiniteSupport g := finite G r e x
  have fh : Function.HasFiniteSupport h := finite H r (e-2) x
  have fb : Function.HasFiniteSupport b := by
    apply fu.subset
    intro j hj hz
    exact hj (by simp [b, hz])
  have fk : Function.HasFiniteSupport k := by
    apply fv.subset
    intro j hj hz
    exact hj (by simp [k, hz])
  have fkshift : Function.HasFiniteSupport (fun j : ℤ => k (j+1)) :=
    fk.fun_comp_of_injective (fun a b h => by omega)
  have fl : Function.HasFiniteSupport l := by
    by_cases hr : r = 0
    · apply (Set.finite_empty : (∅ : Set ℤ).Finite).subset
      intro j hj
      exact False.elim (hj (by simp [l, hr]))
    · simpa only [l, if_neg hr] using
        (finite F (r-1) e x).fun_comp (smul_zero (r+1 : ℂ))
  have fw : Function.HasFiniteSupport w := by
    apply (Set.finite_singleton (-1 : ℤ)).subset
    intro j hj
    by_contra hn
    apply hj
    simp only [Set.mem_singleton_iff] at hn
    simp [w, hn]
  have f2h := fh.fun_comp (smul_zero (2:ℂ))
  have term (j : ℤ) :
      T (flatCoefficient D hu F [(i,r)] (j,()) e x) -
        flatCoefficient D hu F [(i,r)] (j,()) e (T x) =
      g j + b j + (2 : ℂ) • h j + k (j+1) + w j := by
    have ht := congrArg (fun U : Module.End ℂ (ActualTensor D hu) => U x)
      (singleton_term_l1 D hu F G H hF i r j e)
    by_cases hj : j = -1
    · simpa only [T, g, b, u, h, k, v, w, B, show j+1-1=j by omega,
        if_pos hj, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.zero_apply] using ht
    · simpa only [T, g, b, u, h, k, v, w, B, show j+1-1=j by omega,
        if_neg hj, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.zero_apply] using ht
  have summed : T ((singletonLinear D hu (i,r) F).coeff e x) -
      (singletonLinear D hu (i,r) F).coeff e (T x) =
      ∑ᶠ j : ℤ, (g j + b j + (2 : ℂ) • h j + k (j+1) + w j) := by
    rw [singletonLinear_coefficient, singletonLinear_coefficient]
    change T (∑ᶠ j : ℤ, flatCoefficient D hu F [(i,r)] (j,()) e x) -
      (∑ᶠ j : ℤ, flatCoefficient D hu F [(i,r)] (j,()) e (T x)) = _
    rw [map_finsum T (finite F r e x),
      ← finsum_sub_distrib ((finite F r e x).fun_comp (map_zero T)) (finite F r e (T x))]
    exact finsum_congr term
  have split : (∑ᶠ j : ℤ, (g j+b j+(2 : ℂ) • h j+k (j+1)+w j)) =
      (∑ᶠ j : ℤ, g j)+(∑ᶠ j : ℤ, b j)+(∑ᶠ j : ℤ, (2 : ℂ) • h j)+
        (∑ᶠ j : ℤ, k (j+1))+(∑ᶠ j : ℤ, w j) := by
    calc
      _ = (∑ᶠ j : ℤ, (g j+b j+(2 : ℂ) • h j+k (j+1))) + ∑ᶠ j : ℤ, w j :=
        finsum_add_distrib (((fg.add fb).add f2h).add fkshift) fw
      _ = ((∑ᶠ j : ℤ, (g j+b j+(2 : ℂ) • h j)) + ∑ᶠ j : ℤ, k (j+1)) + ∑ᶠ j : ℤ, w j := by
        congr 1
        exact finsum_add_distrib ((fg.add fb).add f2h) fkshift
      _ = (((∑ᶠ j : ℤ, (g j+b j)) + ∑ᶠ j : ℤ, (2 : ℂ) • h j) + ∑ᶠ j : ℤ, k (j+1)) +
          ∑ᶠ j : ℤ, w j := by
        congr 1; congr 1
        exact finsum_add_distrib (fg.add fb) f2h
      _ = _ := by
        congr 1; congr 1; congr 1
        exact finsum_add_distrib fg fb
  have reindex : (∑ᶠ j : ℤ, k (j+1)) = ∑ᶠ j : ℤ, k j :=
    finsum_eq_of_bijective (fun j : ℤ => j+1)
      ⟨fun a b h => by dsimp only at h; omega,
        fun b => ⟨b-1, by dsimp only; omega⟩⟩ (fun _ => rfl)
  have boundary : (∑ᶠ j : ℤ, w j) = B := by
    rw [finsum_eq_single _ (-1) (fun j hj => by simp [w, hj])]
    simp [w]
  have uj (j : ℤ) : u j = jetScalar r j • v j := by
    have ht := congrArg (fun U : Module.End ℂ (ActualTensor D hu) => U x)
      (flat_singleton_jet D hu F i r j (e-2))
    simpa only [u, v, LinearMap.smul_apply,
      show e-2+2*(r:ℤ) = e+2*(r:ℤ)-2 by omega] using ht
  have lj (j : ℤ) : l j =
      (if r = 0 then 0 else (r+1 : ℂ)*jetScalar (r-1) j) • v j := by
    by_cases hr : r = 0
    · simp [l, hr]
    · have sh : e+2*((r-1:ℕ):ℤ) = e+2*(r:ℤ)-2 := by omega
      dsimp only [l, v]
      rw [if_neg hr, if_neg hr, flat_singleton_jet]
      simp only [LinearMap.smul_apply, smul_smul, sh]
  have coefficient (j : ℤ) :
      (((e+2*j+2*(r:ℤ)+3 : ℤ):ℂ)/2-1)*jetScalar r j +
        (-frequency (j-1)*jetScalar r (j-1)) =
      c*jetScalar r j + (if r = 0 then 0 else (r+1 : ℂ)*jetScalar (r-1) j) := by
    have hs := jet_l1_scalar r j
    dsimp only [c, frequency]
    push_cast
    linear_combination hs
  have pair (j : ℤ) : b j + k j = c • u j + l j := by
    dsimp only [b, k]
    rw [uj, lj]
    simp only [smul_smul]
    rw [← add_smul, coefficient, add_smul]
  have contract : (∑ᶠ j : ℤ, b j)+(∑ᶠ j : ℤ, k j) =
      c • (∑ᶠ j : ℤ, u j)+(∑ᶠ j : ℤ, l j) := by
    calc
      _ = ∑ᶠ j : ℤ, (b j+k j) := (finsum_add_distrib fb fk).symm
      _ = ∑ᶠ j : ℤ, (c • u j+l j) := finsum_congr pair
      _ = (∑ᶠ j : ℤ, c • u j)+(∑ᶠ j : ℤ, l j) :=
        finsum_add_distrib (fu.fun_comp (smul_zero c)) fl
      _ = _ := by rw [← smul_finsum' c fu]
  have lower : (∑ᶠ j : ℤ, l j) =
      if r = 0 then 0 else (r+1 : ℂ) • (singletonLinear D hu (i,r-1) F).coeff e x := by
    by_cases hr : r = 0
    · simp [l, hr]
    · rw [if_neg hr, singletonLinear_coefficient]
      change (∑ᶠ j : ℤ, (if r=0 then 0 else (r+1 : ℂ) •
        flatCoefficient D hu F [(i,r-1)] (j,()) e x)) = _
      simp only [if_neg hr]
      exact (smul_finsum' (r+1 : ℂ) (finite F (r-1) e x)).symm
  change T ((singletonLinear D hu (i,r) F).coeff e x) -
    (singletonLinear D hu (i,r) F).coeff e (T x) = _
  rw [summed, split, reindex, boundary, ← smul_finsum' (2:ℂ) fh]
  calc
    _ = (∑ᶠ j : ℤ, g j) + ((∑ᶠ j : ℤ, b j)+(∑ᶠ j : ℤ, k j)) +
        (2 : ℂ) • (∑ᶠ j : ℤ, h j) + B := by abel
    _ = _ := by
      rw [contract, lower]
      simp only [singletonLinear_coefficient]
      change (∑ᶠ j : ℤ, g j) + (c • (∑ᶠ j : ℤ, u j) + _) +
        (2 : ℂ) • (∑ᶠ j : ℤ, h j) + B =
        (∑ᶠ j : ℤ, g j) + c • (∑ᶠ j : ℤ, u j) +
          (2 : ℂ) • (∑ᶠ j : ℤ, h j) + _ + B
      abel


/-- The insertion scalar cancellation after the ORIGINAL corrected-field
readout. The finite top boundary vanishes by the original source cutoff. -/
private theorem evaluated_insertion_l1_cancel (D : LatticeData) (hu : IsUnit D.G.det)
    (b : Carrier D) (i : Fin D.rank) (r N : ℕ)
    (hN : LatticeSugawaraCurrents.vectorFrequencyBound D b < N)
    (e : ℤ) (x : ActualTensor D hu) :
    let f := fun n : ℕ =>
      (LatticeHalfFockCorrectedField.correctedField D hu
        (LatticeFiniteNegativeGeneration.neutralMode D i (n:ℤ) b)).coeff
          (e+2*((r+n:ℕ):ℤ)) x
    let k := fun n : ℕ => (r+1:ℂ)*halfBinomial (r+1)*halfBinomial n / ((r+1:ℂ)+(n:ℂ))
    (1/2*halfBinomial r : ℂ) •
        (∑ n ∈ Finset.range N, Ring.choose (1/2:ℂ) n • f n) =
      (∑ n ∈ Finset.range N, (((r+1:ℂ)+(n:ℂ))*k n) • f n) +
        (∑ n ∈ Finset.range N, ((n:ℂ)*k n) • f (n+1)) +
        (if r = 0 then f 0 else (r+1:ℂ) •
          ∑ n ∈ Finset.range N,
            ((r:ℂ)*halfBinomial r*halfBinomial n / ((r:ℂ)+(n:ℂ))) • f n) := by
  classical
  dsimp only
  let f := fun n : ℕ =>
      (LatticeHalfFockCorrectedField.correctedField D hu
        (LatticeFiniteNegativeGeneration.neutralMode D i (n:ℤ) b)).coeff
          (e+2*((r+n:ℕ):ℤ)) x
  let k := fun n : ℕ => (r+1:ℂ)*halfBinomial (r+1)*halfBinomial n / ((r+1:ℂ)+(n:ℂ))
  let p := fun n : ℕ => if n=0 then 0 else ((n:ℂ)-1)*k (n-1)
  let a := fun n : ℕ => if r=0 then (if n=0 then 1 else 0) else
    (r+1:ℂ)*((r:ℂ)*halfBinomial r*halfBinomial n / ((r:ℂ)+(n:ℂ)))
  have npos : 0 < N := by omega
  have top : f N = 0 := by
    have hz := LatticeSugawaraCurrents.neutralMode_vanish D i b (N:ℤ) (by exact_mod_cast hN)
    simp [f, hz]
  have scalar (n : ℕ) : (1/2*halfBinomial r : ℂ)*Ring.choose (1/2:ℂ) n =
      ((r+1:ℂ)+(n:ℂ))*k n+p n+a n := by
    exact insertion_l1_scalar r n
  have distribute : (1/2*halfBinomial r : ℂ) •
      (∑ n ∈ Finset.range N, Ring.choose (1/2:ℂ) n • f n) =
      (∑ n ∈ Finset.range N, (((r+1:ℂ)+(n:ℂ))*k n) • f n) +
        (∑ n ∈ Finset.range N, p n • f n) +
        (∑ n ∈ Finset.range N, a n • f n) := by
    rw [Finset.smul_sum]
    simp only [smul_smul]
    calc
      _ = ∑ n ∈ Finset.range N, (((r+1:ℂ)+(n:ℂ))*k n+p n+a n) • f n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [scalar]
      _ = _ := by simp only [add_smul, Finset.sum_add_distrib]
  let q := fun n : ℕ => p n • f n
  have qzero : q 0 = 0 := by simp [q,p]
  have qtop : q N = 0 := by simp [q,top]
  have shift : (∑ n ∈ Finset.range N, q n) = ∑ n ∈ Finset.range N, q (n+1) := by
    have hh := (Finset.sum_range_succ q N).symm.trans (Finset.sum_range_succ' q N)
    simpa only [qtop,qzero,add_zero,zero_add] using hh
  have qsucc (n : ℕ) : q (n+1) = ((n:ℂ)*k n) • f (n+1) := by
    simp only [q,p,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,
      Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
  have previous : (∑ n ∈ Finset.range N, p n • f n) =
      ∑ n ∈ Finset.range N, ((n:ℂ)*k n) • f (n+1) := by
    change (∑ n ∈ Finset.range N, q n) = _
    rw [shift]
    exact Finset.sum_congr rfl (fun n hn => qsucc n)
  have lower : (∑ n ∈ Finset.range N, a n • f n) =
      if r=0 then f 0 else (r+1:ℂ) •
        ∑ n ∈ Finset.range N,
          ((r:ℂ)*halfBinomial r*halfBinomial n / ((r:ℂ)+(n:ℂ))) • f n := by
    by_cases hr : r=0
    · rw [if_pos hr, Finset.sum_eq_single 0
        (fun n hn hn0 => by simp [a,hr,hn0])
        (fun hn0 => False.elim (hn0 (Finset.mem_range.mpr npos)))]
      simp [a,hr]
    · simp only [a,if_neg hr,Finset.smul_sum,smul_smul]
  change (1/2*halfBinomial r : ℂ) •
      (∑ n ∈ Finset.range N, Ring.choose (1/2:ℂ) n • f n) =
      (∑ n ∈ Finset.range N, (((r+1:ℂ)+(n:ℂ))*k n) • f n) +
        (∑ n ∈ Finset.range N, ((n:ℂ)*k n) • f (n+1)) + _
  rw [distribute,previous,lower]


/-- Charged source base for the original full-source induction. -/
private theorem ground_l1 (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (e : ℤ) :
    let a : Carrier D := Finsupp.single q (1 : Oscillator D)
    let T := tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1
    let S := LatticeSugawaraCurrents.sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹
    T * (LatticeHalfFockCorrectedField.correctedField D hu a).coeff e -
      (LatticeHalfFockCorrectedField.correctedField D hu a).coeff e * T =
      (LatticeHalfFockCorrectedField.correctedField D hu (S 1 a)).coeff e +
        ((e:ℂ)/2-1) • (LatticeHalfFockCorrectedField.correctedField D hu a).coeff (e-2) +
        (2:ℂ) • (LatticeHalfFockCorrectedField.correctedField D hu (S 0 a)).coeff (e-2) := by
  let a : Carrier D := Finsupp.single q (1 : Oscillator D)
  let H := HalfFockSpectralFiberSource.actualInverse D
  have inv : (LatticeSugawaraCurrents.gramComplex D)⁻¹ = H :=
    Matrix.inv_eq_left_inv (HalfFockSpectralFiberSource.actualInverse_left D hu)
  have s1 : LatticeSugawaraCurrents.sugawaraMode D H 1 a = 0 :=
    LatticeSugawaraVirasoro.sugawaraMode_ground_positive D H q 1 (by omega)
  have s0 : LatticeSugawaraCurrents.sugawaraMode D H 0 a = ((bilinear D q q : ℂ)/2) • a := by
    rw [LatticeSugawaraVirasoro.sugawaraMode_ground_zero,
      LatticeSugawaraConformal.chargeQuadratic_eq D H
        (HalfFockSpectralFiberSource.actualInverse_left D hu)
        (HalfFockSpectralFiberSource.actualInverse_right D hu)]
  have coeff (d : ℤ) : (LatticeHalfFockCorrectedField.correctedField D hu a).coeff d =
      chargedCoefficient D hu q d := by
    apply LinearMap.ext
    intro x
    rw [LatticeHalfFockCorrectedField.corrected_singleton_coeff_charged]
    simp only [chargedField,HVertexOperator.coeff_of_coeff]
  change tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 *
      (LatticeHalfFockCorrectedField.correctedField D hu a).coeff e -
    (LatticeHalfFockCorrectedField.correctedField D hu a).coeff e *
      tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 =
    (LatticeHalfFockCorrectedField.correctedField D hu
      (LatticeSugawaraCurrents.sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 1 a)).coeff e +
    ((e:ℂ)/2-1) • (LatticeHalfFockCorrectedField.correctedField D hu a).coeff (e-2) +
    (2:ℂ) • (LatticeHalfFockCorrectedField.correctedField D hu
      (LatticeSugawaraCurrents.sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 0 a)).coeff (e-2)
  rw [inv,s1,s0]
  simp only [map_zero,map_smul,Pi.zero_apply,Pi.smul_apply,zero_add]
  simp only [coeff]
  rw [LatticeHalfFockChargedSeedPhysical.charged_l1_coefficient]
  module


private theorem insertion_coeff_cutoff (D : LatticeData) (hu : IsUnit D.G.det)
    (b : Carrier D) (i : Fin D.rank) (r N : ℕ)
    (hN : LatticeSugawaraCurrents.vectorFrequencyBound D b < N) (e : ℤ) :
    (LatticeHalfFockCorrectedField.correctedField D hu
      (LatticeFiniteNegativeGeneration.neutralMode D i (-((r+1:ℕ):ℤ)) b)).coeff e =
      (singletonLinear D hu (i,r) (LatticeHalfFockCorrectedField.correctedField D hu b)).coeff e +
      ∑ n ∈ Finset.range N,
        ((r+1:ℂ)*halfBinomial (r+1)*halfBinomial n / ((r+1:ℂ)+(n:ℂ))) •
          (LatticeHalfFockCorrectedField.correctedField D hu
            (LatticeFiniteNegativeGeneration.neutralMode D i (n:ℤ) b)).coeff
              (e+2*((r+1+n:ℕ):ℤ)) := by
  have original := congrArg (fun A : NativeField D hu => A.coeff e)
    (LatticeHalfFockCorrectedField.correctedField_negative_current_insertion D hu (i,r) b)
  simp only [sourceWeight,map_add,map_sum,map_smul,Pi.add_apply,Pi.smul_apply,
    Finset.sum_apply,LatticeHalfFockCorrectedField.shiftField_coefficient_public] at original
  simp only [Nat.cast_add,Nat.cast_one] at original ⊢
  rw [original]
  congr 1
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n hn hnold
  have above : (LatticeSugawaraCurrents.vectorFrequencyBound D b:ℤ) < (n:ℤ) := by
    exact_mod_cast (show LatticeSugawaraCurrents.vectorFrequencyBound D b < n by
      simp only [Finset.mem_range,not_lt] at hnold
      omega)
  simp [LatticeSugawaraCurrents.neutralMode_vanish D i b (n:ℤ) above]

private theorem zero_ward_cutoff (D : LatticeData) (hu : IsUnit D.G.det)
    (b : Carrier D) (i : Fin D.rank) (N : ℕ)
    (hN : LatticeSugawaraCurrents.vectorFrequencyBound D b < N)
    (e : ℤ) (x : ActualTensor D hu) :
    tensorCurrent D (ActualGround D hu) i 0
        ((LatticeHalfFockCorrectedField.correctedField D hu b).coeff e x) -
      (LatticeHalfFockCorrectedField.correctedField D hu b).coeff e
        (tensorCurrent D (ActualGround D hu) i 0 x) =
      ∑ n ∈ Finset.range N, Ring.choose (1/2:ℂ) n •
        (LatticeHalfFockCorrectedField.correctedField D hu
          (LatticeFiniteNegativeGeneration.neutralMode D i (n:ℤ) b)).coeff
            (e-1+2*(n:ℤ)) x := by
  have original := LatticeHalfFockCorrectedField.correctedField_current_ward D hu i b 0 e x
  simp only [frequency,Int.cast_zero,zero_add,mul_zero] at original
  rw [original]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n hn hnold
  have above : (LatticeSugawaraCurrents.vectorFrequencyBound D b:ℤ) < (n:ℤ) := by
    exact_mod_cast (show LatticeSugawaraCurrents.vectorFrequencyBound D b < n by
      simp only [Finset.mem_range,not_lt] at hnold
      omega)
  simp [LatticeSugawaraCurrents.neutralMode_vanish D i b (n:ℤ) above]

private def L1Law (D : LatticeData) (hu : IsUnit D.G.det) (a : Carrier D) : Prop :=
  ∀ e : ℤ,
    tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 *
        (LatticeHalfFockCorrectedField.correctedField D hu a).coeff e -
      (LatticeHalfFockCorrectedField.correctedField D hu a).coeff e *
        tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 =
      (LatticeHalfFockCorrectedField.correctedField D hu
        (LatticeSugawaraCurrents.sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 1 a)).coeff e +
      ((e:ℂ)/2-1) • (LatticeHalfFockCorrectedField.correctedField D hu a).coeff (e-2) +
      (2:ℂ) • (LatticeHalfFockCorrectedField.correctedField D hu
        (LatticeSugawaraCurrents.sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 0 a)).coeff (e-2)

private theorem l1_law_zero (D : LatticeData) (hu : IsUnit D.G.det) : L1Law D hu 0 := by
  intro e
  simp only [map_zero, Pi.zero_apply, mul_zero, zero_mul, sub_self, smul_zero, add_zero]

private theorem l1_law_add (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (ha : L1Law D hu a) (hb : L1Law D hu b) : L1Law D hu (a+b) := by
  intro e
  have h1 := ha e
  have h2 := hb e
  simp only [map_add, Pi.add_apply, mul_add, add_mul, smul_add]
  linear_combination (norm := module) h1+h2

private theorem l1_law_smul (D : LatticeData) (hu : IsUnit D.G.det)
    (c : ℂ) (a : Carrier D) (ha : L1Law D hu a) : L1Law D hu (c • a) := by
  intro e
  have hh := ha e
  simp only [map_smul, Pi.smul_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  linear_combination (norm := module) c • hh

private theorem l1_law_sum (D : LatticeData) (hu : IsUnit D.G.det)
    {ι : Type*} (s : Finset ι) (f : ι → Carrier D) (hf : ∀ i ∈ s, L1Law D hu (f i)) :
    L1Law D hu (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using l1_law_zero D hu
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact l1_law_add D hu _ _ (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj])))

/-- Assembly of the original evaluated insertion, including the zero-mode
crossover. The hypotheses are consumed only as the smaller-source induction
steps in the full source theorem. -/
private theorem insertion_l1 (D : LatticeData) (hu : IsUnit D.G.det)
    (b : Carrier D) (i : Fin D.rank) (r : ℕ)
    (hb : L1Law D hu b)
    (hJ : ∀ n : ℕ, L1Law D hu (LatticeFiniteNegativeGeneration.neutralMode D i (n:ℤ) b)) :
    L1Law D hu (LatticeFiniteNegativeGeneration.neutralMode D i (-((r+1:ℕ):ℤ)) b) := by
  classical
  let F := LatticeHalfFockCorrectedField.correctedField D hu
  let A (d : ℤ) : Carrier D →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) :=
    (LinearMap.proj d).comp (HVertexOperator.coeff.comp F)
  let T := tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1
  let S := LatticeSugawaraCurrents.sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹
  let J := LatticeFiniteNegativeGeneration.neutralMode D i
  let comm : Module.End ℂ (ActualTensor D hu) →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) :=
    LinearMap.mulLeft ℂ T - LinearMap.mulRight ℂ T
  have inverse : (LatticeSugawaraCurrents.gramComplex D)⁻¹ = HalfFockSpectralFiberSource.actualInverse D :=
    Matrix.inv_eq_left_inv (HalfFockSpectralFiberSource.actualInverse_left D hu)
  have source (j k : ℤ) (v : Carrier D) : S j (J k v) =
      J k (S j v) - (k:ℂ) • J (j+k) v := by
    have hh := congrArg (fun U : Module.End ℂ (Carrier D) => U v)
      (LatticeSugawaraCurrents.sugawaraMode_current_commutator D
        (HalfFockSpectralFiberSource.actualInverse D)
        (HalfFockSpectralFiberSource.actualInverse_left D hu)
        (HalfFockSpectralFiberSource.actualInverse_right D hu) i j k)
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] at hh
    dsimp only [S,J]
    rw [inverse]
    linear_combination (norm := module) hh
  let N := max (LatticeSugawaraCurrents.vectorFrequencyBound D b)
    (max (LatticeSugawaraCurrents.vectorFrequencyBound D (S 1 b))
      (LatticeSugawaraCurrents.vectorFrequencyBound D (S 0 b))) + 1
  have hNb : LatticeSugawaraCurrents.vectorFrequencyBound D b < N := by dsimp [N]; omega
  have hN1 : LatticeSugawaraCurrents.vectorFrequencyBound D (S 1 b) < N := by dsimp [N]; omega
  have hN0 : LatticeSugawaraCurrents.vectorFrequencyBound D (S 0 b) < N := by dsimp [N]; omega
  let k (n : ℕ) := (r+1:ℂ)*halfBinomial (r+1)*halfBinomial n / ((r+1:ℂ)+(n:ℂ))
  let R (v : Carrier D) (d : ℤ) := ∑ n ∈ Finset.range N,
    k n • A (d+2*((r+1+n:ℕ):ℤ)) (J (n:ℤ) v)
  let Q (v : Carrier D) (d : ℤ) := (singletonLinear D hu (i,r) (F v)).coeff d
  have ins (v : Carrier D) (hv : LatticeSugawaraCurrents.vectorFrequencyBound D v < N) (d : ℤ) :
      A d (J (-((r+1:ℕ):ℤ)) v) = Q v d + R v d :=
    insertion_coeff_cutoff D hu v i r N hv d
  intro e
  let f (n : ℕ) := A (e+2*((r+n:ℕ):ℤ)) (J (n:ℤ) b)
  let E := (∑ n ∈ Finset.range N, (((r+1:ℂ)+(n:ℂ))*k n) • f n) +
    ∑ n ∈ Finset.range N, ((n:ℂ)*k n) • f (n+1)
  let c : ℂ := (e:ℂ)/2-1+2*(r+1:ℂ)
  let lower := if r=0 then 0 else (r+1:ℂ) •
    (singletonLinear D hu (i,r-1) (F b)).coeff e
  let boundary := (1/2*halfBinomial r : ℂ) •
    (tensorCurrent D (ActualGround D hu) i 0 * A (e+2*(r:ℤ)+1) b -
      A (e+2*(r:ℤ)+1) b * tensorCurrent D (ActualGround D hu) i 0)
  have single : comm (Q b e) = Q (S 1 b) e + c • Q b (e-2) +
      (2:ℂ) • Q (S 0 b) (e-2) + lower + boundary := by
    apply LinearMap.ext
    intro x
    simpa only [comm,Q,c,lower,boundary,A,LinearMap.comp_apply,LinearMap.proj_apply,
      LinearMap.mulLeft_apply,LinearMap.mulRight_apply,LinearMap.sub_apply,
      Module.End.mul_apply,LinearMap.add_apply,LinearMap.smul_apply,DFunLike.ite_apply,
      LinearMap.zero_apply] using
      singleton_l1 D hu (F b) (F (S 1 b)) (F (S 0 b)) hb i r e x
  have lower_cancel : lower + boundary = (r+1:ℂ) • A e (J (1-((r+1:ℕ):ℤ)) b) + E := by
    have cancel : boundary = E +
        (if r=0 then f 0 else (r+1:ℂ) • ∑ n ∈ Finset.range N,
          ((r:ℂ)*halfBinomial r*halfBinomial n / ((r:ℂ)+(n:ℂ))) • f n) := by
      apply LinearMap.ext
      intro x
      have hc := evaluated_insertion_l1_cancel D hu b i r N hNb e x
      have hw := zero_ward_cutoff D hu b i N hNb (e+2*(r:ℤ)+1) x
      dsimp only [boundary,A,F]
      simp only [LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.smul_apply,
        LinearMap.sub_apply,Module.End.mul_apply]
      rw [hw]
      have shift (n : ℕ) : e+2*(r:ℤ)+1-1+2*(n:ℤ) = e+2*((r+n:ℕ):ℤ) := by push_cast; ring
      simp only [shift]
      simpa only [E,k,f,A,J,F,LinearMap.comp_apply,LinearMap.proj_apply,
        LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,Finset.sum_apply,DFunLike.ite_apply,
        LinearMap.zero_apply] using hc
    rw [cancel]
    by_cases hr : r=0
    · subst r
      simp only [lower,if_pos rfl,Nat.cast_zero,zero_add,Nat.cast_one,one_smul,
        Nat.zero_add,Int.cast_zero,mul_zero,add_zero] at *
      dsimp only [f]
      abel
    · have il := insertion_coeff_cutoff D hu b i (r-1) N hNb e
      have nr : r-1+1=r := by omega
      have shift (n : ℕ) : e+2*((r-1+1+n:ℕ):ℤ) = e+2*((r+n:ℕ):ℤ) := by omega
      have cr : ((r-1:ℕ):ℂ)+1=(r:ℂ) := by exact_mod_cast nr
      simp only [nr,shift,cr] at il
      have mode : (1:ℤ)-((r+1:ℕ):ℤ) = -((r-1+1:ℕ):ℤ) := by omega
      rw [mode]
      change lower + (E+_) = (r+1:ℂ) •
        (LatticeHalfFockCorrectedField.correctedField D hu (J (-((r-1+1:ℕ):ℤ)) b)).coeff e + E
      rw [show r-1+1=r by omega,il]
      dsimp only [lower,f,k,A,J,F]
      simp only [if_neg hr,LinearMap.comp_apply,LinearMap.proj_apply]
      module
  have residual : comm (R b e) = R (S 1 b) e + c • R b (e-2) +
      (2:ℂ) • R (S 0 b) (e-2) - E := by
    have term (n : ℕ) : k n • comm (A (e+2*((r+1+n:ℕ):ℤ)) (J (n:ℤ) b)) =
        k n • A (e+2*((r+1+n:ℕ):ℤ)) (J (n:ℤ) (S 1 b)) +
        c • (k n • A (e-2+2*((r+1+n:ℕ):ℤ)) (J (n:ℤ) b)) +
        (2:ℂ) • (k n • A (e-2+2*((r+1+n:ℕ):ℤ)) (J (n:ℤ) (S 0 b))) -
        (((r+1:ℂ)+(n:ℂ))*k n) • f n - ((n:ℂ)*k n) • f (n+1) := by
      have hc := hJ n (e+2*((r+1+n:ℕ):ℤ))
      change T * A _ (J _ b) - A _ (J _ b) * T = _ at hc
      change k n • (T * A _ (J _ b) - A _ (J _ b) * T) = _
      rw [hc]
      change k n • (A (e+2*((r+1+n:ℕ):ℤ)) (S 1 (J (n:ℤ) b)) +
        (((e+2*((r+1+n:ℕ):ℤ):ℤ):ℂ)/2-1) •
          A (e+2*((r+1+n:ℕ):ℤ)-2) (J (n:ℤ) b) +
        (2:ℂ) • A (e+2*((r+1+n:ℕ):ℤ)-2) (S 0 (J (n:ℤ) b))) = _
      rw [source,source]
      simp only [map_sub,map_smul]
      have shift : e+2*((r+1+n:ℕ):ℤ)-2 = e-2+2*((r+1+n:ℕ):ℤ) := by omega
      have fs : e-2+2*((r+1+n:ℕ):ℤ) = e+2*((r+n:ℕ):ℤ) := by omega
      have ns : (1:ℤ)+(n:ℤ) = ((n+1:ℕ):ℤ) := by omega
      have fn : e+2*((r+1+n:ℕ):ℤ) = e+2*((r+(n+1):ℕ):ℤ) := by omega
      simp only [shift,zero_add,ns]
      dsimp only [f,c]
      rw [← fs,← fn]
      push_cast
      module
    dsimp only [R]
    rw [map_sum]
    simp only [map_smul]
    rw [Finset.sum_congr rfl (fun n hn => term n)]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.smul_sum]
    dsimp only [E]
    abel
  change comm (A e (J (-((r+1:ℕ):ℤ)) b)) =
    A e (S 1 (J (-((r+1:ℕ):ℤ)) b)) + ((e:ℂ)/2-1) • A (e-2) (J (-((r+1:ℕ):ℤ)) b) +
    (2:ℂ) • A (e-2) (S 0 (J (-((r+1:ℕ):ℤ)) b))
  rw [source,source]
  rw [show (1:ℤ)+(-((r+1:ℕ):ℤ))=1-((r+1:ℕ):ℤ) by omega]
  simp only [map_sub,map_smul,zero_add]
  rw [ins b hNb e, map_add,single,residual,ins (S 1 b) hN1 e,
    ins (S 0 b) hN0 (e-2),ins b hNb (e-2)]
  have lc := lower_cancel
  dsimp only [c] at lc ⊢
  push_cast at lc ⊢
  linear_combination (norm := module) lc


set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1200000 in
-- Keep the source-only induction within a dedicated elaboration budget.
/-- Oscillator-length induction on the original charge sector. Positive
currents differentiate and strictly lower length; mode zero remains the
original charge scalar. -/
private theorem polynomial_l1 (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (p : Oscillator D) : L1Law D hu (Finsupp.single q p) := by
  classical
  have ground : L1Law D hu (Finsupp.single q (1 : Oscillator D)) := ground_l1 D hu q
  have bounded : ∀ n : ℕ, ∀ p : Oscillator D, p.totalDegree ≤ n →
      L1Law D hu (Finsupp.single q p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp
      have mon (m : Index D →₀ ℕ) (c : ℂ) (hm : m.sum (fun _ e => e) ≤ n) :
          L1Law D hu (Finsupp.single q (MvPolynomial.monomial m c)) := by
        by_cases hz : m=0
        · subst m
          have hc : (MvPolynomial.monomial (0 : Index D →₀ ℕ) c : Oscillator D) =
              c • (1 : Oscillator D) := MvPolynomial.C_eq_smul_one
          have state : Finsupp.single q (MvPolynomial.monomial (0 : Index D →₀ ℕ) c) =
              c • Finsupp.single q (1 : Oscillator D) :=
            (congrArg (Finsupp.single q) hc).trans (Finsupp.smul_single c q (1 : Oscillator D)).symm
          exact Eq.mpr (congrArg (L1Law D hu) state) (l1_law_smul D hu c _ ground)
        · obtain ⟨v,hv⟩ := Finsupp.support_nonempty_iff.mpr hz
          have vle : Finsupp.single v 1 ≤ m :=
            Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv))
          let t := m-Finsupp.single v 1
          have teq : t+Finsupp.single v 1=m := tsub_add_cancel_of_le vle
          have length : t.sum (fun _ e => e)+1=m.sum (fun _ e => e) := by
            simpa [Finsupp.sum_add_index'] using
              congrArg (fun z : Index D →₀ ℕ => z.sum (fun _ e => e)) teq
          have ht : t.sum (fun _ e => e)<n := by omega
          let b : Carrier D := Finsupp.single q (MvPolynomial.monomial t c)
          have deg : (MvPolynomial.monomial t c : Oscillator D).totalDegree ≤ t.sum (fun _ e => e) :=
            MvPolynomial.totalDegree_monomial_le t c
          have hb : L1Law D hu b := ih _ ht _ deg
          have positive (k : ℕ) : L1Law D hu
              (LatticeFiniteNegativeGeneration.neutralMode D v.1 (k:ℤ) b) := by
            cases k with
            | zero =>
              have he : LatticeFiniteNegativeGeneration.neutralMode D v.1 0 b =
                  (bilinear D (unitCharge D v.1) q : ℂ) • b := by
                dsimp only [b]
                rw [LatticeSugawaraCurrents.neutralMode_single]
                simp only [LatticeFiniteNegativeGeneration.neutralPolynomialMode,lt_self_iff_false,
                  if_false,if_true,LinearMap.smul_apply,LinearMap.id_apply,Finsupp.smul_single]
              rw [Nat.cast_zero,he]
              exact l1_law_smul D hu _ _ hb
            | succ k =>
              have derivatives (j : Fin D.rank) : L1Law D hu
                  (Finsupp.single q (MvPolynomial.pderiv (j,k) (MvPolynomial.monomial t c))) := by
                by_cases hz : MvPolynomial.pderiv (j,k) (MvPolynomial.monomial t c : Oscillator D)=0
                · rw [hz,Finsupp.single_zero]
                  exact l1_law_zero D hu
                · have hd := D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity.API.totalDegree_pderiv_lt
                    (MvPolynomial.monomial t c : Oscillator D) (j,k) hz
                  exact ih _ (lt_trans hd (lt_of_le_of_lt deg ht)) _ le_rfl
              have hs := l1_law_smul D hu (k+1:ℂ) _
                (l1_law_sum D hu Finset.univ
                  (fun j : Fin D.rank => (D.G v.1 j : ℂ) •
                    Finsupp.single q (MvPolynomial.pderiv (j,k) (MvPolynomial.monomial t c)))
                  (fun j hj => l1_law_smul D hu _ _ (derivatives j)))
              have action : LatticeFiniteNegativeGeneration.neutralMode D v.1 ((k+1:ℕ):ℤ) b =
                  (k+1:ℂ) • ∑ j : Fin D.rank, (D.G v.1 j : ℂ) •
                    Finsupp.single q (MvPolynomial.pderiv (j,k) (MvPolynomial.monomial t c)) := by
                dsimp only [b]
                rw [Nat.cast_add,Nat.cast_one,LatticeSugawaraCurrents.neutralMode_single,
                  LatticeSugawaraCurrents.neutralPolynomialMode_positive]
                simp only [LinearMap.smul_apply,LatticeSugawaraCurrents.weightedPartial,
                  LinearMap.sum_apply,LinearMap.smul_apply,Derivation.coeFn_coe,
                  Finsupp.single_finsetSum,← Finsupp.smul_single]
              exact Eq.mpr (congrArg (L1Law D hu) action) hs
          have step := insertion_l1 D hu b v.1 v.2 hb positive
          have creation : LatticeFiniteNegativeGeneration.neutralMode D v.1 (-((v.2+1:ℕ):ℤ)) b =
              Finsupp.single q (MvPolynomial.monomial m c) := by
            dsimp only [b]
            have index : -((v.2+1:ℕ):ℤ)=-(v.2:ℤ)-1 := by omega
            rw [index,LatticeSugawaraCurrents.neutralMode_single,
              LatticeSugawaraCurrents.neutralPolynomialMode_negative,LinearMap.mulLeft_apply]
            congr 1
            rw [MvPolynomial.X,MvPolynomial.monomial_mul_monomial]
            rw [add_comm,teq,one_mul]
          rwa [creation] at step
      have expansion : Finsupp.single q p = ∑ m ∈ p.support,
          Finsupp.single q (MvPolynomial.monomial m (p.coeff m)) := by
        rw [← Finsupp.single_finsetSum]
        exact congrArg (Finsupp.single q) p.as_sum
      rw [expansion]
      exact l1_law_sum D hu p.support _ (fun m hm => mon m (p.coeff m)
        (le_trans (MvPolynomial.le_totalDegree hm) hp))
  exact bounded p.totalDegree p le_rfl

/-- Physical z=t² special-conformal coefficient covariance for EVERY original
source and actual target input. All corrections, inverse Gram contractions,
signed exponents, and original independent source L0/L1 actions are retained. -/
theorem corrected_field_l1_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (e : ℤ) :
    tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 *
        (LatticeHalfFockCorrectedField.correctedField D hu a).coeff e -
      (LatticeHalfFockCorrectedField.correctedField D hu a).coeff e *
        tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 =
      (LatticeHalfFockCorrectedField.correctedField D hu
        (LatticeSugawaraCurrents.sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 1 a)).coeff e +
      ((e:ℂ)/2-1) • (LatticeHalfFockCorrectedField.correctedField D hu a).coeff (e-2) +
      (2:ℂ) • (LatticeHalfFockCorrectedField.correctedField D hu
        (LatticeSugawaraCurrents.sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 0 a)).coeff (e-2) := by
  have ha : L1Law D hu a := by
    classical
    have expansion : a = ∑ q ∈ a.support, Finsupp.single q (a q) := a.sum_single.symm
    rw [expansion]
    exact l1_law_sum D hu a.support _ (fun q hq => polynomial_l1 D hu q (a q))
  exact ha e


end
end D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
