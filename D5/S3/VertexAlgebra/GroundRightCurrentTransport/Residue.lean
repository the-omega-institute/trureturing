/- GID: D5/S3/VertexAlgebra/GroundRightCurrentTransport/Residue
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GroundRightCurrentTransport/Residue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise finite fields and scalar convolution on actual intermediate inputs. -/

import D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds

/-! Complete supported residue calculus for the native ground-current consumer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct VertexOperator
open D5.S3.VertexAlgebra

namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport

universe u

namespace Calculus

open scoped VertexOperator

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

private def upper (A : VertexOperator ℂ M) (x : M) : ℕ :=
  (-((HahnModule.of ℂ).symm (A x)).order - 1).toNat + 1

private theorem high (A : VertexOperator ℂ M) (x : M) (n : ℤ)
    (hn : (upper A x : ℤ) ≤ n) : (A [[n]]) x = 0 := by
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  dsimp [upper] at hn
  omega

private theorem forward_finite (A B : VertexOperator ℂ M) (r n : ℤ) (x : M) :
    Function.HasFiniteSupport (fun j : ℕ => (A [[r - j]]) ((B [[n + j]]) x)) := by
  refine (Finset.range ((upper B x : ℤ) - n).toNat).finite_toSet.subset ?_
  intro j hj
  by_contra outside
  have hz := high B x (n + j) (by
    simp only [Finset.mem_coe, Finset.mem_range] at outside
    omega)
  exact hj (by simpa only [hz, map_zero])

private theorem reverse_finite (A B : VertexOperator ℂ M) (r n : ℤ) (x : M) :
    Function.HasFiniteSupport (fun j : ℕ => (B [[n + r - j]]) ((A [[j]]) x)) := by
  refine (Finset.range (upper A x)).finite_toSet.subset ?_
  intro j hj
  by_contra outside
  have hz := high A x j (by
    simp only [Finset.mem_coe, Finset.mem_range] at outside
    omega)
  exact hj (by simpa only [hz, map_zero])

def R (A B : VertexOperator ℂ M) (r : ℤ) : VertexOperator ℂ M := by
  classical
  have leftFinite (n : ℤ) (x : M) : Function.HasFiniteSupport (fun j : ℕ =>
      residueWeight r j • (A [[r - j]]) ((B [[n + j]]) x)) := by
    simpa only [Pi.smul_def'] using (forward_finite A B r n x).smul_right (residueWeight r)
  have rightFinite (n : ℤ) (x : M) : Function.HasFiniteSupport (fun j : ℕ =>
      residueWeight r j • (B [[n + r - j]]) ((A [[j]]) x)) := by
    simpa only [Pi.smul_def'] using (reverse_finite A B r n x).smul_right (residueWeight r)
  let coefficient (n : ℤ) : Module.End ℂ M := {
    toFun x := (∑ᶠ j : ℕ, residueWeight r j • (A [[r - j]]) ((B [[n + j]]) x)) -
      (-1 : ℂ) ^ r • ∑ᶠ j : ℕ,
        residueWeight r j • (B [[n + r - j]]) ((A [[j]]) x)
    map_add' x y := by
      simp only [map_add, smul_add]
      rw [finsum_add_distrib (leftFinite n x) (leftFinite n y),
        finsum_add_distrib (rightFinite n x) (rightFinite n y)]
      module
    map_smul' c x := by
      simp only [map_smul]
      simp_rw [smul_comm _ c]
      rw [← smul_finsum' c (leftFinite n x), ← smul_finsum' c (rightFinite n x)]
      simp only [RingHom.id_apply]
      module }
  have bounded (x : M) : BddBelow (Function.support
      (fun e : ℤ => coefficient (-e - 1) x)) := by
    let orders := (Finset.range (upper A x + 1)).image (fun j : ℕ =>
      ((HahnModule.of ℂ).symm (B ((A [[j]]) x))).order + r - j)
    have nonempty : orders.Nonempty := Finset.image_nonempty.mpr
      ⟨0, Finset.mem_range.mpr (by omega)⟩
    let lower := min ((HahnModule.of ℂ).symm (B x)).order (orders.min' nonempty)
    refine ⟨lower, ?_⟩
    intro e he
    by_contra outside
    have small : e < lower := by omega
    have firstZero (j : ℕ) : (A [[r - j]]) ((B [[-e - 1 + j]]) x) = 0 := by
      have hz : (B [[-e - 1 + j]]) x = 0 := by
        apply VertexOperator.ncoeff_eq_zero_of_lt_order
        dsimp [lower] at small
        omega
      rw [hz, map_zero]
    have secondZero (j : ℕ) : (B [[-e - 1 + r - j]]) ((A [[j]]) x) = 0 := by
      by_cases inside : j ≤ upper A x
      · have hm : ((HahnModule.of ℂ).symm (B ((A [[j]]) x))).order + r - j ∈ orders :=
          Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
        have hb := Finset.min'_le orders _ hm
        apply VertexOperator.ncoeff_eq_zero_of_lt_order
        dsimp [lower] at small
        omega
      · rw [high A x j (by omega), map_zero]
    exact he (by simp [coefficient, firstZero, secondZero])
  exact VertexOperator.of_coeff (fun e => coefficient (-e - 1)) bounded

private theorem R_mode (A B : VertexOperator ℂ M) (r n : ℤ) (x : M) :
    ((R A B r) [[n]]) x =
      (∑ᶠ j : ℕ, residueWeight r j • (A [[r - j]]) ((B [[n + j]]) x)) -
      (-1 : ℂ) ^ r • ∑ᶠ j : ℕ,
        residueWeight r j • (B [[n + r - j]]) ((A [[j]]) x) := by
  simp only [R, VertexOperator.ncoeff_of_coeff,
    show -(-n - 1) - 1 = n by omega]
  rfl

def Z (c : ℤ) (A : VertexOperator ℂ M) : VertexOperator ℂ M :=
  VertexOperator.of_coeff (fun e => A.coeff (e + c)) (by
    intro x
    refine ⟨((HahnModule.of ℂ).symm (A x)).order - c, ?_⟩
    intro e he
    by_contra outside
    exact he (HahnSeries.coeff_eq_zero_of_lt_order (by omega)))

private theorem Z_mode (c : ℤ) (A : VertexOperator ℂ M) (n : ℤ) :
    (Z c A)[[n]] = A[[n - c]] := by
  simp only [Z, VertexOperator.ncoeff_of_coeff]
  change A.coeff (-n - 1 + c) = A.coeff (-(n - c) - 1)
  rw [show -n - 1 + c = -(n - c) - 1 by omega]

def Q (A B : VertexOperator ℂ M) (s r : ℤ) (K : ℕ) :
    VertexOperator ℂ M :=
  ∑ ell ∈ Finset.range ((K : ℤ) - r).toNat,
    Ring.choose (-(s : ℂ) / 2) ell • Z ell (R A B (r + ell))

private theorem Q_mode (A B : VertexOperator ℂ M) (s r n : ℤ) (K : ℕ) (x : M) :
    ((Q A B s r K) [[n]]) x =
      ∑ ell ∈ Finset.range ((K : ℤ) - r).toNat,
        Ring.choose (-(s : ℂ) / 2) ell • ((R A B (r + ell)) [[n - ell]]) x := by
  simp only [Q, map_sum, Finset.sum_apply, LinearMap.sum_apply, map_smul,
    Pi.smul_apply, LinearMap.smul_apply, Z_mode]

def Valid (A B : VertexOperator ℂ M) (K : ℕ) : Prop :=
  ∀ r : ℤ, (K : ℤ) ≤ r → R A B r = 0

private theorem Q_cutoff (A B : VertexOperator ℂ M) (s r : ℤ)
    (K L : ℕ) (hK : Valid A B K) (hL : Valid A B L) :
    Q A B s r K = Q A B s r L := by
  classical
  suffices extend : ∀ K L : ℕ, K ≤ L → Valid A B K → Q A B s r K = Q A B s r L by
    exact (extend K (max K L) (le_max_left _ _) hK).trans
      (extend L (max K L) (le_max_right _ _) hL).symm
  intro K L hle valid
  unfold Q
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj outside
  have hjK : ((K : ℤ) - r).toNat ≤ j := by
    simpa only [Finset.mem_range, not_lt] using outside
  rw [valid (r + j) (by omega)]
  have hz : Z (j : ℤ) (0 : VertexOperator ℂ M) = 0 := by
    apply HVertexOperator.coeff_inj
    funext e
    apply LinearMap.ext
    intro x
    simp [Z]
  rw [hz, smul_zero]

private theorem ext_modes {A B : VertexOperator ℂ M}
    (h : ∀ n : ℤ, A[[n]] = B[[n]]) : A = B := by
  apply HVertexOperator.coeff_inj
  funext e
  simpa only [VertexOperator.ncoeff_apply, show -(-e - 1) - 1 = e by omega]
    using h (-e - 1)

private theorem R_add (A B C : VertexOperator ℂ M) (r : ℤ) :
    R A (B + C) r = R A B r + R A C r := by
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  simp only [R_mode, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  have leftB := (forward_finite A B r n x).smul_right (residueWeight r)
  have leftC := (forward_finite A C r n x).smul_right (residueWeight r)
  have rightB := (reverse_finite A B r n x).smul_right (residueWeight r)
  have rightC := (reverse_finite A C r n x).smul_right (residueWeight r)
  simp only [Pi.smul_def'] at leftB leftC rightB rightC
  rw [finsum_add_distrib leftB leftC, finsum_add_distrib rightB rightC]
  module

private theorem R_smul (A B : VertexOperator ℂ M) (r : ℤ) (c : ℂ) :
    R A (c • B) r = c • R A B r := by
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  simp only [R_mode, map_smul, Pi.smul_apply, LinearMap.smul_apply]
  simp_rw [smul_comm _ c]
  have left := (forward_finite A B r n x).smul_right (residueWeight r)
  have right := (reverse_finite A B r n x).smul_right (residueWeight r)
  simp only [Pi.smul_def'] at left right
  rw [← smul_finsum' c left, ← smul_finsum' c right]
  module

private theorem R_zero (A : VertexOperator ℂ M) (r : ℤ) :
    R A 0 r = 0 := by
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  simp [R_mode]

private theorem R_sum (A : VertexOperator ℂ M) (r : ℤ)
    {I : Type*} (s : Finset I) (f : I → VertexOperator ℂ M) :
    R A (∑ i ∈ s, f i) r = ∑ i ∈ s, R A (f i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [R_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, R_add, ih, Finset.sum_insert ha]

private theorem R_Z (A B : VertexOperator ℂ M) (r c : ℤ) :
    R A (Z c B) r = Z c (R A B r) := by
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  simp only [R_mode, Z_mode]
  congr 1
  · apply finsum_congr
    intro j
    rw [show n + (j : ℤ) - c = n - c + j by omega]
  · congr 1
    apply finsum_congr
    intro j
    rw [show n + r - (j : ℤ) - c = n - c + r - j by omega]

private theorem pair_finite (f : ℕ → ℕ → M) (N : ℕ)
    (tail : ∀ j, N ≤ j → ∀ k, f j k = 0)
    (rows : ∀ j, Function.HasFiniteSupport (f j)) :
    Function.HasFiniteSupport (Function.uncurry f) := by
  classical
  have finite : (⋃ j ∈ (↑(Finset.range N) : Set ℕ),
      (Prod.mk j) '' Function.support (f j)).Finite :=
    (Finset.range N).finite_toSet.biUnion (fun j _ => (rows j).image (Prod.mk j))
  apply finite.subset
  rintro ⟨j,k⟩ h
  have hj : j < N := by
    by_contra outside
    exact h (tail j (by omega) k)
  exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hj,
    ⟨k, h, rfl⟩⟩⟩

private theorem swap_finite {f : ℕ × ℕ → M} (h : Function.HasFiniteSupport f) :
    Function.HasFiniteSupport (fun p : ℕ × ℕ => f (p.2,p.1)) :=
  h.comp_of_injective (Equiv.prodComm ℕ ℕ).injective

private theorem fiber_finite {f : ℕ × ℕ → M} (h : Function.HasFiniteSupport f) :
    Function.HasFiniteSupport (fun j : ℕ => ∑ᶠ k : ℕ, f (j,k)) := by
  refine (h.image Prod.fst).subset ?_
  intro j hj
  by_contra outside
  have zero : ∀ k : ℕ, f (j,k) = 0 := by
    intro k
    by_contra hk
    exact outside ⟨(j,k), hk, rfl⟩
  exact hj (by simp [zero])

local macro "finiteConvolution" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds.finite_convolution))

private theorem finsum_convolution (a c : ℂ) (v : ℕ → M)
    (finite : Function.HasFiniteSupport v) :
    (∑ᶠ j : ℕ, ∑ᶠ k : ℕ, (Ring.choose a j * Ring.choose c k) • v (j + k)) =
      ∑ᶠ n : ℕ, Ring.choose (a + c) n • v n := by
  classical
  let K := finite.toFinset.sup id + 1
  have tail (n : ℕ) (hn : K ≤ n) : v n = 0 := by
    by_contra nonzero
    have mem := finite.mem_toFinset.mpr nonzero
    have le := Finset.le_sup (f := id) mem
    simp only [id_eq] at le
    dsimp [K] at hn
    omega
  have inner (j : ℕ) :
      (∑ᶠ k : ℕ, (Ring.choose a j * Ring.choose c k) • v (j + k)) =
        ∑ k ∈ Finset.range K, (Ring.choose a j * Ring.choose c k) • v (j + k) := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra outside
    exact hk (by simp [tail (j+k) (by have := Finset.mem_range.not.mp outside; omega)])
  have outer :
      (∑ᶠ j : ℕ, ∑ᶠ k : ℕ, (Ring.choose a j * Ring.choose c k) • v (j + k)) =
        ∑ j ∈ Finset.range K, ∑ᶠ k : ℕ,
          (Ring.choose a j * Ring.choose c k) • v (j + k) := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have zero (k : ℕ) : (Ring.choose a j * Ring.choose c k) • v (j + k) = 0 := by
      rw [tail (j+k) (by have := Finset.mem_range.not.mp outside; omega), smul_zero]
    exact hj (by simp [zero])
  rw [outer]
  simp_rw [inner, ← smul_smul, ← Finset.smul_sum]
  rw [finiteConvolution a c K v tail]
  symm
  apply finsum_eq_sum_of_support_subset
  intro n hn
  by_contra outside
  exact hn (by simp [tail n (by have := Finset.mem_range.not.mp outside; omega)])

theorem R_nat (A B : VertexOperator ℂ M) (r : ℕ) (n : ℤ) (x : M) :
    ((R A B r)[[n]]) x =
      ((FieldNormalProductLocality.deltaEnd ^ r)
        (FieldNormalProductLocality.commutator A B)) 0 n x := by
  classical
  have left : (∑ᶠ j : ℕ, residueWeight r j •
      (A [[(r : ℤ) - j]]) ((B [[n + j]]) x)) =
      ∑ j ∈ Finset.range (r+1), ((-1 : ℂ)^j * (r.choose j : ℂ)) •
        (A [[(r : ℤ) - j]]) ((B [[n + j]]) x) := by
    simp only [residueWeight, Int.cast_natCast, Ring.choose_natCast]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have zero := Nat.choose_eq_zero_of_lt (show r < j by simpa using outside)
    exact hj (by simp [zero])
  have right : (∑ᶠ j : ℕ, residueWeight r j •
      (B [[n + (r : ℤ) - j]]) ((A [[j]]) x)) =
      ∑ j ∈ Finset.range (r+1), ((-1 : ℂ)^j * (r.choose j : ℂ)) •
        (B [[n + (r : ℤ) - j]]) ((A [[j]]) x) := by
    simp only [residueWeight, Int.cast_natCast, Ring.choose_natCast]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have zero := Nat.choose_eq_zero_of_lt (show r < j by simpa using outside)
    exact hj (by simp [zero])
  rw [R_mode, left, right, FieldDeltaBinomial.delta_binomial]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    FieldNormalProductLocality.commutator, LinearMap.sub_apply,
    Module.End.mul_apply, zero_add, smul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.smul_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have within : j ≤ r := by simpa using Finset.mem_range.mp hj
  simp only [Nat.add_sub_cancel, Nat.choose_symm within, smul_smul, zpow_natCast]
  have sign : (-1 : ℂ)^r * (-1 : ℂ)^(r-j) = (-1 : ℂ)^j := by
    have split : (-1 : ℂ)^r = (-1 : ℂ)^j * (-1 : ℂ)^(r-j) := by
      rw [← pow_add, Nat.add_sub_of_le within]
    have square : ((-1 : ℂ)^(r-j))^2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [split]
    calc
      _ = (-1 : ℂ)^j * ((-1 : ℂ)^(r-j))^2 := by ring
      _ = _ := by rw [square, mul_one]
  rw [← mul_assoc, sign, Int.natCast_sub within]
  rw [show n + (r : ℤ) - ((r : ℤ) - j) = n + j by omega]

private theorem valid_of_locality (A B : VertexOperator ℂ M) (K : ℕ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ K)
      (FieldNormalProductLocality.commutator A B) = 0) : Valid A B K := by
  intro r hr
  obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r by omega)
  have le : K ≤ degree := by omega
  have killed : (FieldNormalProductLocality.deltaEnd ^ degree)
      (FieldNormalProductLocality.commutator A B) = 0 := by
    obtain ⟨extra, equality⟩ := Nat.exists_eq_add_of_le le
    rw [equality, Nat.add_comm K extra, pow_add, Module.End.mul_apply, locality, map_zero]
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  rw [R_nat, killed]
  rfl

private theorem map_R (L : Module.End ℂ M) (J B : VertexOperator ℂ M)
    (d t : ℤ) (x : M) :
    L (((R J B d)[[t]]) x) =
      (∑ᶠ k : ℕ, residueWeight d k • L ((J [[d-k]]) ((B [[t+k]]) x))) -
      (-1 : ℂ)^d • ∑ᶠ k : ℕ,
        residueWeight d k • L ((B [[t+d-k]]) ((J [[k]]) x)) := by
  have hf := (forward_finite J B d t x).smul_right (residueWeight d)
  have hg := (reverse_finite J B d t x).smul_right (residueWeight d)
  simp only [Pi.smul_def'] at hf hg
  rw [R_mode, map_sub, map_smul, map_finsum L hf, map_finsum L hg]
  simp only [map_smul]

private theorem nested_sum (f g : ℕ × ℕ → M)
    (hf : Function.HasFiniteSupport f) (hg : Function.HasFiniteSupport g) (c : ℂ) :
    (∑ᶠ j : ℕ, ((∑ᶠ k : ℕ, f (j,k)) - c • (∑ᶠ k : ℕ, g (j,k)))) =
      (∑ᶠ p : ℕ × ℕ, f p) - c • ∑ᶠ p : ℕ × ℕ, g p := by
  have hc := (fiber_finite hg).smul_right (fun _ => c)
  simp only [Pi.smul_def'] at hc
  rw [finsum_sub_distrib (fiber_finite hf) hc,
    ← smul_finsum' c (fiber_finite hg), ← finsum_curry f hf, ← finsum_curry g hg]

private theorem triple_first_finite (A J B : VertexOperator ℂ M)
    (r d n : ℤ) (x : M) : Function.HasFiniteSupport (fun p : ℕ × ℕ =>
      (A [[r-p.1]]) ((J [[d-p.2]]) ((B [[n+p.1+p.2]]) x))) := by
  refine pair_finite (fun j k =>
    (A [[r-j]]) ((J [[d-k]]) ((B [[n+j+k]]) x)))
    ((upper B x : ℤ) - n).toNat ?_ ?_
  · intro j hj k
    rw [high B x (n+j+k) (by omega), map_zero, map_zero]
  · intro j
    simpa only [add_assoc] using
      (forward_finite J B d (n+j) x).fun_comp (map_zero (A [[r-j]]))

private theorem triple_second_finite (A J B : VertexOperator ℂ M)
    (r d n : ℤ) (x : M) : Function.HasFiniteSupport (fun p : ℕ × ℕ =>
      (A [[r-p.1]]) ((B [[n+p.1+d-p.2]]) ((J [[p.2]]) x))) := by
  refine swap_finite (f := fun p : ℕ × ℕ =>
    (A [[r-p.2]]) ((B [[n+p.2+d-p.1]]) ((J [[p.1]]) x))) ?_
  refine pair_finite (fun k j =>
    (A [[r-j]]) ((B [[n+j+d-k]]) ((J [[k]]) x))) (upper J x) ?_ ?_
  · intro k hk j
    rw [high J x k (by omega), map_zero, map_zero]
  · intro k
    simpa only [show ∀ j : ℕ, n+(j:ℤ)+d-k = n+d-k+j by intro j; omega]
      using forward_finite A B r (n+d-k) ((J [[k]]) x)

private theorem triple_third_finite (A J B : VertexOperator ℂ M)
    (r d n : ℤ) (x : M) : Function.HasFiniteSupport (fun p : ℕ × ℕ =>
      (J [[d-p.2]]) ((B [[n+r-p.1+p.2]]) ((A [[p.1]]) x))) := by
  refine pair_finite (fun j k =>
    (J [[d-k]]) ((B [[n+r-j+k]]) ((A [[j]]) x))) (upper A x) ?_ ?_
  · intro j hj k
    rw [high A x j (by omega), map_zero, map_zero]
  · intro j
    exact forward_finite J B d (n+r-j) ((A [[j]]) x)

private theorem triple_fourth_finite (A J B : VertexOperator ℂ M)
    (r d n : ℤ) (x : M) : Function.HasFiniteSupport (fun p : ℕ × ℕ =>
      (B [[n+r+d-p.1-p.2]]) ((J [[p.2]]) ((A [[p.1]]) x))) := by
  refine pair_finite (fun j k =>
    (B [[n+r+d-j-k]]) ((J [[k]]) ((A [[j]]) x))) (upper A x) ?_ ?_
  · intro j hj k
    rw [high A x j (by omega), map_zero, map_zero]
  · intro j
    simpa only [show ∀ k : ℕ, n+((r+d-(j:ℤ)):ℤ)-k = n+r+d-j-k by intro k; omega]
      using reverse_finite J B (r+d-j) n ((A [[j]]) x)

def nestedCell (A J B : VertexOperator ℂ M) (r d n : ℤ)
    (j k : ℕ) : Module.End ℂ M :=
  (residueWeight r j * residueWeight d k) •
    ((A [[r-j]]) * (J [[d-k]]) * (B [[n+j+k]]) -
      (-1 : ℂ)^d • ((A [[r-j]]) * (B [[n+j+d-k]]) * (J [[k]])) -
      (-1 : ℂ)^r • ((J [[d-k]]) * (B [[n+r-j+k]]) * (A [[j]]) -
        (-1 : ℂ)^d • ((B [[n+r+d-j-k]]) * (J [[k]]) * (A [[j]]))))

private theorem nested_expansion (A J B : VertexOperator ℂ M)
    (r d n : ℤ) (x : M) :
    ((R A (R J B d) r)[[n]]) x =
      ∑ᶠ p : ℕ × ℕ, nestedCell A J B r d n p.1 p.2 x := by
  let w (p : ℕ × ℕ) := residueWeight r p.1 * residueWeight d p.2
  let f1 (p : ℕ × ℕ) := w p •
    (A [[r-p.1]]) ((J [[d-p.2]]) ((B [[n+p.1+p.2]]) x))
  let f2 (p : ℕ × ℕ) := w p •
    (A [[r-p.1]]) ((B [[n+p.1+d-p.2]]) ((J [[p.2]]) x))
  let f3 (p : ℕ × ℕ) := w p •
    (J [[d-p.2]]) ((B [[n+r-p.1+p.2]]) ((A [[p.1]]) x))
  let f4 (p : ℕ × ℕ) := w p •
    (B [[n+r+d-p.1-p.2]]) ((J [[p.2]]) ((A [[p.1]]) x))
  have hf1 : Function.HasFiniteSupport f1 := by
    simpa only [f1, Pi.smul_def'] using (triple_first_finite A J B r d n x).smul_right w
  have hf2 : Function.HasFiniteSupport f2 := by
    simpa only [f2, Pi.smul_def'] using (triple_second_finite A J B r d n x).smul_right w
  have hf3 : Function.HasFiniteSupport f3 := by
    simpa only [f3, Pi.smul_def'] using (triple_third_finite A J B r d n x).smul_right w
  have hf4 : Function.HasFiniteSupport f4 := by
    simpa only [f4, Pi.smul_def'] using (triple_fourth_finite A J B r d n x).smul_right w
  have row1 (j : ℕ) : residueWeight r j • (A [[r-j]])
      (((R J B d)[[n+j]]) x) =
      (∑ᶠ k : ℕ, f1 (j,k)) - (-1 : ℂ)^d • ∑ᶠ k : ℕ, f2 (j,k) := by
    have h := map_R (residueWeight r j • (A [[r-j]])) J B d (n+j) x
    simpa only [LinearMap.smul_apply, smul_smul, mul_comm,
      f1, f2, w, add_assoc] using h
  have row2 (j : ℕ) : residueWeight r j •
      (((R J B d)[[n+r-j]]) ((A [[j]]) x)) =
      (∑ᶠ k : ℕ, f3 (j,k)) - (-1 : ℂ)^d • ∑ᶠ k : ℕ, f4 (j,k) := by
    have h := map_R (residueWeight r j • (LinearMap.id : Module.End ℂ M))
      J B d (n+r-j) ((A [[j]]) x)
    simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
      mul_comm, f3, f4, w,
      show ∀ k : ℕ, n+r-(j:ℤ)+d-k = n+r+d-j-k by intro k; omega] using h
  have g2 : Function.HasFiniteSupport (fun p => (-1 : ℂ)^d • f2 p) := by
    simpa only [Pi.smul_def'] using hf2.smul_right (fun _ => (-1 : ℂ)^d)
  have g4 : Function.HasFiniteSupport (fun p => (-1 : ℂ)^d • f4 p) := by
    simpa only [Pi.smul_def'] using hf4.smul_right (fun _ => (-1 : ℂ)^d)
  have g34 : Function.HasFiniteSupport
      (fun p => (-1 : ℂ)^r • (f3 p - (-1 : ℂ)^d • f4 p)) := by
    simpa only [Pi.smul_def', Pi.sub_def] using
      (hf3.sub g4).smul_right (fun _ => (-1 : ℂ)^r)
  have cell (p : ℕ × ℕ) : nestedCell A J B r d n p.1 p.2 x =
      f1 p - (-1 : ℂ)^d • f2 p -
        (-1 : ℂ)^r • (f3 p - (-1 : ℂ)^d • f4 p) := by
    simp only [nestedCell, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.mul_apply, f1, f2, f3, f4, w]
    module
  simp_rw [cell]
  have g12 : Function.HasFiniteSupport (fun p => f1 p - (-1 : ℂ)^d • f2 p) := by
    simpa only [Pi.sub_def] using hf1.sub g2
  have g3m4 : Function.HasFiniteSupport (fun p => f3 p - (-1 : ℂ)^d • f4 p) := by
    simpa only [Pi.sub_def] using hf3.sub g4
  rw [finsum_sub_distrib g12 g34,
    finsum_sub_distrib hf1 g2,
    ← smul_finsum' ((-1 : ℂ)^d) hf2,
    ← smul_finsum' ((-1 : ℂ)^r) g3m4,
    finsum_sub_distrib hf3 g4, ← smul_finsum' ((-1 : ℂ)^d) hf4]
  rw [R_mode]
  simp only [row1, row2]
  rw [nested_sum f1 f2 hf1 hf2, nested_sum f3 f4 hf3 hf4]

private theorem nested_finite (A J B : VertexOperator ℂ M)
    (r d n : ℤ) (x : M) :
    Function.HasFiniteSupport (fun p : ℕ × ℕ => nestedCell A J B r d n p.1 p.2 x) := by
  have h2 := (triple_second_finite A J B r d n x).smul_right (fun _ => (-1 : ℂ)^d)
  have h4 := (triple_fourth_finite A J B r d n x).smul_right (fun _ => (-1 : ℂ)^d)
  have h34 := ((triple_third_finite A J B r d n x).sub h4).smul_right
    (fun _ => (-1 : ℂ)^r)
  have h := ((triple_first_finite A J B r d n x).sub h2).sub h34
  have weighted := h.smul_right (fun p : ℕ × ℕ =>
    residueWeight r p.1 * residueWeight d p.2)
  simpa only [nestedCell, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Pi.smul_def', Pi.sub_def] using weighted

private theorem diagonal_finite (v : ℕ → M) (finite : Function.HasFiniteSupport v) :
    Function.HasFiniteSupport (fun p : ℕ × ℕ => v (p.1+p.2)) := by
  classical
  let N := finite.toFinset.sup id + 1
  refine pair_finite (fun j k => v (j+k)) N ?_ ?_
  · intro j hj k
    by_contra nonzero
    have le := Finset.le_sup (f := id) (finite.mem_toFinset.mpr nonzero)
    simp only [id_eq] at le
    dsimp [N] at hj
    omega
  · intro j
    exact finite.comp_of_injective (by intro a b h; exact Nat.add_left_cancel h)

private theorem residue_convolution (r d : ℤ) (v : ℕ → M)
    (finite : Function.HasFiniteSupport v) :
    (∑ᶠ p : ℕ × ℕ,
      (residueWeight r p.1 * residueWeight d p.2) • v (p.1+p.2)) =
      ∑ᶠ h : ℕ, residueWeight (r+d) h • v h := by
  have joint := (diagonal_finite v finite).smul_right
    (fun p : ℕ × ℕ => residueWeight r p.1 * residueWeight d p.2)
  simp only [Pi.smul_def'] at joint
  rw [finsum_curry _ joint]
  have signed := finite.smul_right (fun h : ℕ => (-1 : ℂ)^h)
  simp only [Pi.smul_def'] at signed
  calc
    _ = ∑ᶠ j : ℕ, ∑ᶠ k : ℕ,
        (Ring.choose (r : ℂ) j * Ring.choose (d : ℂ) k) •
          ((-1 : ℂ)^(j+k) • v (j+k)) := by
      apply finsum_congr
      intro j
      apply finsum_congr
      intro k
      simp only [residueWeight, pow_add, smul_smul]
      module
    _ = ∑ᶠ h : ℕ, Ring.choose ((r : ℂ)+(d : ℂ)) h •
        ((-1 : ℂ)^h • v h) := finsum_convolution (r : ℂ) (d : ℂ) _ signed
    _ = _ := by
      apply finsum_congr
      intro h
      simp only [residueWeight, Int.cast_add, smul_smul]
      module


end Calculus
end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
