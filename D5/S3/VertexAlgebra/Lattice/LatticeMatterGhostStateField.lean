/- GID: D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateField
   mirror-E: none(waiver:algebraic-original-matter-ghost-field)
   anchors: []
   utility: none
   digest: Locally finite original all-state tensor fields have signed locality and the actual total current. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.LatticeActualStateDerivative
import D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
Original all-state matter/ghost tensor field and polynomial-cleared locality.
The original carrier is algebraic, not completed; both field maps and all
operators are unchanged. Infinite sums act on fixed vectors, without any
finite-support hypothesis on endomorphism families.
Classical tensor-field construction: Bakalov--Kac, math/0402315v1, section 4.1.
Ghost normal products and coefficient calculus retain Scott Carnahan's
Apache-2.0 attribution in their suppliers. No literature novelty is asserted.
proof_shape: Y, stateField_locality, conformal_modes, current_zero_mode: content
admission_basis: escape-witness
escape_witness: bounded pointwise tensor convolution descends through both
tensor relations; finite same-order pairs permit integer polynomial shifts;
both cleared factors have rectangular support. The actual current is computed.
Private helpers are consumed below. This module asserts no Jacobi, total-charge
derivation, ghost square-zero, no-ghost, or full string/AdS completion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeMatterGhostStateField

open LatticeGeneratingFieldLocality LatticeMatterGhostCoupling
open D5.S3.Quantum.Fermionic
open CountableOccupationFock

noncomputable section

private def cut {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A : VertexOperator ℂ E) (v : E) : ℤ :=
  -((HahnModule.of ℂ).symm (A v)).order

private theorem cut_kills {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A : VertexOperator ℂ E) (v : E) (n : ℤ) (hn : cut A v ≤ n) :
    (A[[n]]) v = 0 := by
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  dsimp [cut] at hn
  omega

/-- A fixed tensor mode, bilinear in the ORIGINAL field states and inputs. -/
private def term (D : LatticeData) (n k : ℤ) :
    State D →ₗ[ℂ] Module.End ℂ (State D) :=
  TensorProduct.map₂
    ((LinearMap.proj k).comp ((VertexOperator.ncoeff).comp (LatticeAllStateField.Y D)))
    ((LinearMap.proj (n - 1 - k)).comp
      ((VertexOperator.ncoeff).comp BcGhostStateField.Y))

private theorem term_tmul (D : LatticeData) (u v : Carrier D) (a b : Fock)
    (n k : ℤ) :
    term D n k (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) =
      ((LatticeAllStateField.Y D u)[[k]]) v ⊗ₜ[ℂ]
        ((BcGhostStateField.Y a)[[n - 1 - k]]) b := rfl

private theorem term_support (D : LatticeData) (u v : Carrier D) (a b : Fock)
    (n M G : ℤ)
    (hm : ∀ k : ℤ, M ≤ k → ((LatticeAllStateField.Y D u)[[k]]) v = 0)
    (hg : ∀ j : ℤ, G ≤ j → ((BcGhostStateField.Y a)[[j]]) b = 0) :
    Function.support (fun k => term D n k (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b)) ⊆
      Set.Icc (n - G) (M - 1) := by
  intro k hk
  by_contra h
  have hd : k < n - G ∨ M - 1 < k := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using h
  apply hk
  dsimp only
  rw [term_tmul]
  rcases hd with hd | hd
  · rw [hg _ (by omega), TensorProduct.tmul_zero]
  · rw [hm _ (by omega), TensorProduct.zero_tmul]

private theorem term_finite (D : LatticeData) (s x : State D) (n : ℤ) :
    Function.HasFiniteSupport (fun k : ℤ => term D n k s x) := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    induction x using TensorProduct.inductionOn with
    | tmul v b =>
      exact (Set.finite_Icc _ _).subset
        (term_support D u v a b n
          (cut (LatticeAllStateField.Y D u) v) (cut (BcGhostStateField.Y a) b)
          (cut_kills _ _) (cut_kills _ _))
    | add x y hx hy =>
      simpa only [map_add, Pi.add_def] using hx.add hy
  | add s t hs ht =>
    simpa only [map_add, LinearMap.add_apply, Pi.add_def] using hs.add ht

private theorem term_truncation (D : LatticeData) (s x : State D) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∀ k : ℤ, term D n k s x = 0 := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    induction x using TensorProduct.inductionOn with
    | tmul v b =>
      let M := cut (LatticeAllStateField.Y D u) v
      let G := cut (BcGhostStateField.Y a) b
      refine ⟨M + G, ?_⟩
      intro n hn k
      rw [term_tmul]
      by_cases hk : M ≤ k
      · rw [cut_kills _ _ _ hk, TensorProduct.zero_tmul]
      · rw [cut_kills _ _ (n - 1 - k) (by omega), TensorProduct.tmul_zero]
    | add x y hx hy =>
      obtain ⟨N, hN⟩ := hx
      obtain ⟨P, hP⟩ := hy
      exact ⟨max N P, fun n hn k => by
        rw [map_add, hN n (by omega) k, hP n (by omega) k, add_zero]⟩
  | add s t hs ht =>
    obtain ⟨N, hN⟩ := hs
    obtain ⟨P, hP⟩ := ht
    exact ⟨max N P, fun n hn k => by
      rw [map_add, LinearMap.add_apply, hN n (by omega) k, hP n (by omega) k,
        add_zero]⟩

private def coefficient (D : LatticeData) (n : ℤ) :
    State D →ₗ[ℂ] Module.End ℂ (State D) where
  toFun s := {
    toFun x := ∑ᶠ k : ℤ, term D n k s x
    map_add' x y := by
      simp only [map_add]
      exact finsum_add_distrib (term_finite D s x n) (term_finite D s y n)
    map_smul' z x := by
      simp only [map_smul, RingHom.id_apply]
      exact (smul_finsum' z (term_finite D s x n)).symm }
  map_add' s t := by
    apply LinearMap.ext
    intro x
    change (∑ᶠ k : ℤ, term D n k (s + t) x) =
      (∑ᶠ k : ℤ, term D n k s x) + (∑ᶠ k : ℤ, term D n k t x)
    simp only [map_add, LinearMap.add_apply]
    exact finsum_add_distrib (term_finite D s x n) (term_finite D t x n)
  map_smul' z s := by
    apply LinearMap.ext
    intro x
    change (∑ᶠ k : ℤ, term D n k (z • s) x) = z • ∑ᶠ k : ℤ, term D n k s x
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]
    exact (smul_finsum' z (term_finite D s x n)).symm

private def field (D : LatticeData) (s : State D) : VertexOperator ℂ (State D) :=
  VertexOperator.of_coeff (fun power => coefficient D (-power - 1) s) (by
    intro x
    obtain ⟨N, hN⟩ := term_truncation D s x
    refine ⟨-N, ?_⟩
    intro power hp
    by_contra hn
    exact hp (finsum_eq_zero_of_forall_eq_zero (hN (-power - 1) (by omega))))

private theorem field_modes (D : LatticeData) (s : State D) (n : ℤ) :
    (field D s)[[n]] = coefficient D n s := by
  rw [field, VertexOperator.ncoeff_of_coeff, show -(-n - 1) - 1 = n by omega]

/-- The all-state linear tensor field on the original algebraic carrier. -/
def Y (D : LatticeData) : State D →ₗ[ℂ] VertexOperator ℂ (State D) where
  toFun := field D
  map_add' s t := by
    apply HVertexOperator.coeff_inj
    funext power
    simp only [VertexOperator.coeff_eq_ncoeff, field_modes, map_add, Pi.add_apply]
  map_smul' z s := by
    apply HVertexOperator.coeff_inj
    funext power
    simp only [VertexOperator.coeff_eq_ncoeff, field_modes, map_smul, Pi.smul_apply, RingHom.id_apply]

private theorem Y_modes (D : LatticeData) (s x : State D) (n : ℤ) :
    ((Y D s)[[n]]) x = ∑ᶠ k : ℤ, term D n k s x := by
  change ((field D s)[[n]]) x = _
  rw [field_modes]
  rfl

/-- Literal coefficient formula, its actual finite support, and the sharp
pointwise interval for ANY supplied matter and ghost tail bounds. -/
theorem tensor_coefficients (D : LatticeData) (u v : Carrier D) (a b : Fock)
    (n M G : ℤ)
    (hm : ∀ k : ℤ, M ≤ k → ((LatticeAllStateField.Y D u)[[k]]) v = 0)
    (hg : ∀ j : ℤ, G ≤ j → ((BcGhostStateField.Y a)[[j]]) b = 0) :
    let f : ℤ → State D := fun k =>
      ((LatticeAllStateField.Y D u)[[k]]) v ⊗ₜ[ℂ]
        ((BcGhostStateField.Y a)[[n - 1 - k]]) b
    Function.support f ⊆ Set.Icc (n - G) (M - 1) ∧
      Function.HasFiniteSupport f ∧
      ((Y D (u ⊗ₜ[ℂ] a))[[n]]) (v ⊗ₜ[ℂ] b) = ∑ᶠ k : ℤ, f k ∧
      (M + G ≤ n → ((Y D (u ⊗ₜ[ℂ] a))[[n]]) (v ⊗ₜ[ℂ] b) = 0) := by
  dsimp only
  have hs := term_support D u v a b n M G hm hg
  simp only [term_tmul] at hs
  refine ⟨hs, (Set.finite_Icc _ _).subset hs, ?_, ?_⟩
  · rw [Y_modes]
    exact finsum_congr (fun k => term_tmul D u v a b n k)
  · intro hn
    rw [Y_modes]
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    rw [term_tmul]
    by_cases hk : M ≤ k
    · rw [hm k hk, TensorProduct.zero_tmul]
    · rw [hg _ (by omega), TensorProduct.tmul_zero]

private theorem Y_tmul (D : LatticeData) (u v : Carrier D) (a b : Fock) (n : ℤ) :
    ((Y D (u ⊗ₜ[ℂ] a))[[n]]) (v ⊗ₜ[ℂ] b) =
      ∑ᶠ k : ℤ, ((LatticeAllStateField.Y D u)[[k]]) v ⊗ₜ[ℂ]
        ((BcGhostStateField.Y a)[[n - 1 - k]]) b := by
  rw [Y_modes]
  exact finsum_congr (fun k => term_tmul D u v a b n k)

/-- All field states and all input states, including inhomogeneous finite sums. -/
theorem stateField_truncation (D : LatticeData) (s x : State D) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ((Y D s)[[n]]) x = 0 := by
  obtain ⟨N, hN⟩ := term_truncation D s x
  exact ⟨N, fun n hn => by
    rw [Y_modes]
    exact finsum_eq_zero_of_forall_eq_zero (hN n hn)⟩

def vacuum (D : LatticeData) : State D :=
  LatticeAllStateField.vacuum D ⊗ₜ[ℂ] CountableOccupationFock.vacuum

/-- The fixed original matter translation and original ghost L(-1). -/
def translation (D : LatticeData) : Module.End ℂ (State D) :=
  TensorProduct.map (LatticeSugawaraConformal.translation D) LinearMap.id +
    TensorProduct.map LinearMap.id (BcGhostVirasoro.L (-1))

def parity (D : LatticeData) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id CountableOccupationFock.parity

private theorem translation_tmul (D : LatticeData) (v : Carrier D) (b : Fock) :
    translation D (v ⊗ₜ[ℂ] b) =
      LatticeSugawaraConformal.translation D v ⊗ₜ[ℂ] b +
        v ⊗ₜ[ℂ] BcGhostVirasoro.L (-1) b := by
  simp only [translation, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply]

private theorem identity_modes {E : Type*} [AddCommGroup E] [Module ℂ E] (n : ℤ) :
    ((FieldNormalProduct.identityField : VertexOperator ℂ E)[[n]]) =
      if n = -1 then LinearMap.id else 0 := by
  rw [FieldNormalProduct.identityField, VertexOperator.ncoeff_of_coeff]
  simp only [show -n - 1 = 0 ↔ n = -1 by omega]

private theorem right_vacuum_modes (D : LatticeData) (u : Carrier D) (n : ℤ) :
    ((Y D (u ⊗ₜ[ℂ] CountableOccupationFock.vacuum))[[n]]) =
      TensorProduct.map ((LatticeAllStateField.Y D u)[[n]]) LinearMap.id := by
  apply TensorProduct.ext'
  intro v b
  rw [Y_tmul, BcGhostStateField.stateField_creation.1]
  rw [finsum_eq_single _ n]
  · rw [identity_modes, ite_eq_left (show n - 1 - n = -1 by omega)]
    rfl
  · intro k hk
    simp [identity_modes, show n - 1 - k ≠ -1 by omega]

private theorem left_vacuum_modes (D : LatticeData) (a : Fock) (n : ℤ) :
    ((Y D (LatticeAllStateField.vacuum D ⊗ₜ[ℂ] a))[[n]]) =
      TensorProduct.map LinearMap.id ((BcGhostStateField.Y a)[[n]]) := by
  apply TensorProduct.ext'
  intro v b
  rw [Y_tmul, LatticeAllStateField.stateField_vacuum]
  rw [finsum_eq_single _ (-1)]
  · rw [identity_modes, ite_eq_left rfl, show n - 1 - -1 = n by omega]
    rfl
  · intro k hk
    simp [identity_modes, hk]

/-- Vacuum field, all-state creation and all nonnegative vacuum coefficients,
and vanishing of the ORIGINAL translation on the tensor vacuum. -/
theorem stateField_vacuum_creation (D : LatticeData) :
    Y D (vacuum D) = FieldNormalProduct.identityField ∧
      (∀ s : State D, ((Y D s)[[-1]]) (vacuum D) = s) ∧
      (∀ (s : State D) (n : ℤ), 0 ≤ n → ((Y D s)[[n]]) (vacuum D) = 0) ∧
      translation D (vacuum D) = 0 := by
  have creative (s : State D) (n : ℤ) (hn : 0 ≤ n) :
      ((Y D s)[[n]]) (vacuum D) = 0 := by
    induction s using TensorProduct.inductionOn with
    | tmul u a =>
      rw [vacuum, Y_tmul]
      apply finsum_eq_zero_of_forall_eq_zero
      intro k
      by_cases hk : 0 ≤ k
      · rw [LatticeAllStateField.stateField_creativity D u k hk, TensorProduct.zero_tmul]
      · rw [BcGhostStateField.stateField_creation.2.2.1 a (n - 1 - k) (by omega),
          TensorProduct.tmul_zero]
    | add s t hs ht => simp [map_add, hs, ht]
  refine ⟨?_, ?_, creative, ?_⟩
  · apply HVertexOperator.coeff_inj
    funext power
    rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
    rw [vacuum, right_vacuum_modes, LatticeAllStateField.stateField_vacuum,
      identity_modes, identity_modes]
    split_ifs <;> simp [TensorProduct.map_id]
  · intro s
    induction s using TensorProduct.inductionOn with
    | tmul u a =>
      rw [vacuum, Y_tmul, finsum_eq_single _ (-1)]
      · simp only [show (-1 : ℤ) - 1 - -1 = -1 by omega,
          LatticeAllStateField.stateField_creation,
          BcGhostStateField.stateField_creation.2.1]
      · intro k hk
        by_cases hp : 0 ≤ k
        · rw [LatticeAllStateField.stateField_creativity D u k hp, TensorProduct.zero_tmul]
        · rw [BcGhostStateField.stateField_creation.2.2.1 a (-1 - 1 - k) (by omega),
            TensorProduct.tmul_zero]
    | add s t hs ht => simp [map_add, hs, ht]
  · rw [vacuum, translation_tmul, LatticeAllStateField.translation_kills_vacuum,
      BcGhostStateField.stateField_translation.1]
    simp

private theorem term_covariance (D : LatticeData) (s : State D) (n k : ℤ) :
    translation D * term D n k s - term D n k s * translation D =
      -(k : ℂ) • term D (n - 1) (k - 1) s +
        -((n - 1 - k : ℤ) : ℂ) • term D (n - 1) k s := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    apply TensorProduct.ext'
    intro v b
    have hm := LinearMap.congr_fun (LatticeAllStateField.stateField_covariance D u k) v
    have hg := LinearMap.congr_fun
      (BcGhostStateField.stateField_translation.2 a (n - 1 - k)) b
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] at hm hg
    have hm' := sub_eq_iff_eq_add.mp hm
    have hg' := sub_eq_iff_eq_add.mp hg
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, term_tmul, translation_tmul, map_add]
    rw [hm', hg']
    rw [show n - 1 - 1 - (k - 1) = n - 1 - k by omega,
      show n - 1 - k - 1 = n - 1 - 1 - k by omega]
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    module
  | add s t hs ht =>
    simp only [map_add, mul_add, add_mul] at *
    rw [show ∀ A B C E : Module.End ℂ (State D),
      (A + B) - (C + E) = (A - C) + (B - E) by intros; abel, hs, ht]
    module

/-- Covariance of every coefficient under the original tensor translation.
The shift is made only in a finite action family. -/
theorem stateField_covariance (D : LatticeData) (s : State D) (n : ℤ) :
    translation D * ((Y D s)[[n]]) - ((Y D s)[[n]]) * translation D =
      -(n : ℂ) • ((Y D s)[[n - 1]]) := by
  apply LinearMap.ext
  intro x
  let f : ℤ → State D := fun k => term D (n - 1) k s x
  have hf : Function.HasFiniteSupport f := term_finite D s x (n - 1)
  let e : ℤ ≃ ℤ := Equiv.subRight 1
  have hleft : Function.HasFiniteSupport (fun k : ℤ => -(k : ℂ) • f (k - 1)) :=
    (hf.comp_of_injective e.injective).smul_right (fun k : ℤ => -(k : ℂ))
  have hright : Function.HasFiniteSupport
      (fun k : ℤ => -((n - 1 - k : ℤ) : ℂ) • f k) :=
    hf.smul_right (fun k : ℤ => -((n - 1 - k : ℤ) : ℂ))
  have shifted : (∑ᶠ k : ℤ, -(k : ℂ) • f (k - 1)) =
      ∑ᶠ k : ℤ, -((k + 1 : ℤ) : ℂ) • f k := by
    let g : ℤ → State D := fun k => -((k + 1 : ℤ) : ℂ) • f k
    calc
      _ = ∑ᶠ k : ℤ, g (e k) := by
        apply finsum_congr
        intro k
        change -(k : ℂ) • f (k - 1) = -((k - 1 + 1 : ℤ) : ℂ) • f (k - 1)
        rw [show k - 1 + 1 = k by omega]
      _ = _ := finsum_comp_equiv e
  change translation D (((Y D s)[[n]]) x) -
    ((Y D s)[[n]]) (translation D x) = -(n : ℂ) • ((Y D s)[[n - 1]]) x
  rw [Y_modes, Y_modes, map_finsum (translation D) (term_finite D s x n),
    ← finsum_sub_distrib ((term_finite D s x n).fun_comp (map_zero (translation D)))
      (term_finite D s (translation D x) n)]
  calc
    _ = ∑ᶠ k : ℤ, (-(k : ℂ) • f (k - 1) +
        -((n - 1 - k : ℤ) : ℂ) • f k) := by
      apply finsum_congr
      intro k
      exact LinearMap.congr_fun (term_covariance D s n k) x
    _ = _ := by
      rw [finsum_add_distrib hleft hright, shifted,
        ← finsum_add_distrib
          (f := fun k : ℤ => -((k + 1 : ℤ) : ℂ) • f k)
          (g := fun k : ℤ => -((n - 1 - k : ℤ) : ℂ) • f k)
          (hf.smul_right (fun k : ℤ => -((k + 1 : ℤ) : ℂ))) hright]
      simp_rw [← add_smul, show ∀ k : ℤ,
        -((k + 1 : ℤ) : ℂ) + -((n - 1 - k : ℤ) : ℂ) = -(n : ℂ) by
          intro k; push_cast; ring]
      rw [← smul_finsum' _ hf, Y_modes]

private theorem term_parity (D : LatticeData) (s : State D) (n k : ℤ) :
    parity D * term D n k s = term D n k (parity D s) * parity D := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    apply TensorProduct.ext'
    intro v b
    have h := LinearMap.congr_fun (BcGhostStateField.stateField_parity a (n - 1 - k)) b
    simpa only [parity, term, TensorProduct.map₂_apply_tmul,
      LinearMap.comp_apply, LinearMap.proj_apply, Module.End.mul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply] using
      congrArg (fun w => ((LatticeAllStateField.Y D u)[[k]]) v ⊗ₜ[ℂ] w) h
  | add s t hs ht =>
    simp only [map_add, mul_add, add_mul, hs, ht]

/-- Actual parity acts on every field state, without a homogeneity premise. -/
theorem stateField_parity (D : LatticeData) (s : State D) (n : ℤ) :
    parity D * ((Y D s)[[n]]) = ((Y D (parity D s))[[n]]) * parity D := by
  apply LinearMap.ext
  intro x
  change parity D (((Y D s)[[n]]) x) = ((Y D (parity D s))[[n]]) (parity D x)
  rw [Y_modes, Y_modes, map_finsum (parity D) (term_finite D s x n)]
  exact finsum_congr (fun k => LinearMap.congr_fun (term_parity D s n k) x)

/-- Literal conformal state; H is arbitrary and rank zero is included. -/
def omega (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : State D :=
  LatticeActualConformalState.omega D H ⊗ₜ[ℂ] CountableOccupationFock.vacuum +
    LatticeAllStateField.vacuum D ⊗ₜ[ℂ] BcGhostConformalBRSTState.Omega

/-- The exact original total modes in `LatticeBRST.total_ward_b`. -/
theorem conformal_modes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    ((Y D (omega D H))[[m + 1]]) = matterMode D H m + ghostVirasoro D m := by
  simp only [omega, map_add, Pi.add_apply, right_vacuum_modes, left_vacuum_modes,
    LatticeActualConformalState.omega_modes, BcGhostConformalBRSTState.conformal_modes,
    matterMode, ghostVirasoro]

/-- The actual coupled current, not a replacement charge or a reconstruction
certificate: omega_m tensor c-state plus vacuum_m tensor raw original cubic. -/
def Jtot (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : State D :=
  LatticeActualConformalState.omega D H ⊗ₜ[ℂ] ket {1} +
    LatticeAllStateField.vacuum D ⊗ₜ[ℂ] BcGhostConformalBRSTState.Jg

/-- Exact integer reindexing k=m+1 gives the existing locally finite matter
coupling T. Neither inverse Gram nor rank 26 is used. -/
theorem current_zero_mode (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    ((Y D (Jtot D H))[[0]]) = LatticeBRST.totalCharge D H := by
  have matterCurrent : ((Y D
      (LatticeActualConformalState.omega D H ⊗ₜ[ℂ] ket {1}))[[0]]) = T D H := by
    apply TensorProduct.ext'
    intro v b
    rw [Y_tmul]
    let e : ℤ ≃ ℤ := Equiv.addRight 1
    calc
      _ = ∑ᶠ m : ℤ,
          ((LatticeAllStateField.Y D (LatticeActualConformalState.omega D H))[[e m]]) v ⊗ₜ[ℂ]
            ((BcGhostStateField.Y (ket {1}))[[0 - 1 - e m]]) b :=
        (finsum_comp_equiv e).symm
      _ = ∑ᶠ m : ℤ, summand D H m (v ⊗ₜ[ℂ] b) := by
        apply finsum_congr
        intro m
        dsimp [e]
        rw [LatticeActualConformalState.omega_modes,
          BcGhostStateField.stateField_creation.2.2.2.2,
          show (-1 : ℤ) - (m + 1) + 2 = -m by omega]
        rfl
      _ = _ := rfl
  simp only [Jtot, map_add, Pi.add_apply, matterCurrent, left_vacuum_modes,
    BcGhostConformalBRSTState.current_zero_mode,
    LatticeBRST.totalCharge, LatticeBRST.ghostCharge]

/- Finite convolution uses only same-order factor families. Iterated finite
shifts implement polynomial multiplication without binomial/Fubini interchange. -/

open FieldNormalProductLocality (delta)

private def deltaLinear {E : Type*} [AddCommGroup E] [Module ℂ E] :
    Module.End ℂ (ℤ → ℤ → E) where
  toFun := delta
  map_add' f g := by funext p q; simp only [delta, Pi.add_apply]; abel
  map_smul' z f := by funext p q; simp only [delta, Pi.smul_apply, smul_sub, RingHom.id_apply]

private theorem deltaLinear_pow_apply {E : Type*} [AddCommGroup E] [Module ℂ E]
    (N : ℕ) (f : ℤ → ℤ → E) :
    (deltaLinear ^ N) f = delta^[N] f := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
    change delta ((deltaLinear ^ N) f) = delta (delta^[N] f)
    rw [ih]

private theorem delta_evaluate {E : Type*} [AddCommGroup E] [Module ℂ E]
    (f : ℤ → ℤ → Module.End ℂ E) (x : E) (N : ℕ) :
    delta^[N] (fun p q => f p q x) = fun p q => (delta^[N] f) p q x := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext p q
    simp only [delta, LinearMap.sub_apply]

private def pairShift (a b : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun z := (z.1 + a, z.2 + b)
  invFun z := (z.1 - a, z.2 - b)
  left_inv z := by ext <;> dsimp <;> omega
  right_inv z := by ext <;> dsimp <;> omega

private def conv {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : ℤ → ℤ → E) (g : ℤ → ℤ → F) :
    ℤ → ℤ → E ⊗[ℂ] F := fun r s =>
  ∑ᶠ z : ℤ × ℤ, f z.1 z.2 ⊗ₜ[ℂ] g (r - 1 - z.1) (s - 1 - z.2)

private def PairFinite {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : ℤ → ℤ → E) (g : ℤ → ℤ → F) : Prop :=
  ∀ r s : ℤ, Function.HasFiniteSupport
    (fun z : ℤ × ℤ => f z.1 z.2 ⊗ₜ[ℂ] g (r - 1 - z.1) (s - 1 - z.2))

private theorem pair_shift_finite {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] {f : ℤ → ℤ → E} {g : ℤ → ℤ → F}
    (h : PairFinite f g) (r s a b c d : ℤ) :
    Function.HasFiniteSupport (fun z : ℤ × ℤ =>
      f (z.1 + a) (z.2 + b) ⊗ₜ[ℂ] g (r - 1 - z.1 + c) (s - 1 - z.2 + d)) := by
  let H : ℤ × ℤ → E ⊗[ℂ] F := fun z =>
    f z.1 z.2 ⊗ₜ[ℂ] g (r + a + c - 1 - z.1) (s + b + d - 1 - z.2)
  have he : Function.HasFiniteSupport (H ∘ pairShift a b) :=
    (h (r + a + c) (s + b + d)).comp_of_injective (pairShift a b).injective
  have eq : (fun z : ℤ × ℤ =>
      f (z.1 + a) (z.2 + b) ⊗ₜ[ℂ] g (r - 1 - z.1 + c) (s - 1 - z.2 + d)) =
      H ∘ pairShift a b := by
    funext z
    dsimp [H, pairShift]
    congr 2 <;> omega
  rw [eq]
  exact he

private theorem pair_delta_left {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] {f : ℤ → ℤ → E} {g : ℤ → ℤ → F}
    (h : PairFinite f g) : PairFinite (delta f) g := by
  intro r s
  have h1 := pair_shift_finite h r s 1 0 0 0
  have h2 := pair_shift_finite h r s 0 1 0 0
  simpa only [delta, TensorProduct.sub_tmul, add_zero, Pi.sub_def] using h1.sub h2

private theorem pair_delta_right {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] {f : ℤ → ℤ → E} {g : ℤ → ℤ → F}
    (h : PairFinite f g) : PairFinite f (delta g) := by
  intro r s
  have h1 := pair_shift_finite h r s 0 0 1 0
  have h2 := pair_shift_finite h r s 0 0 0 1
  simpa only [delta, TensorProduct.tmul_sub, add_zero, Pi.sub_def] using h1.sub h2

private theorem pair_iterated {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] {f : ℤ → ℤ → E} {g : ℤ → ℤ → F}
    (h : PairFinite f g) (p q : ℕ) : PairFinite (delta^[p] f) (delta^[q] g) := by
  have hp : PairFinite (delta^[p] f) g := by
    induction p with
    | zero => exact h
    | succ p ih =>
      rw [Function.iterate_succ_apply']
      exact pair_delta_left ih
  induction q with
  | zero => exact hp
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact pair_delta_right ih

private theorem conv_shift {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : ℤ → ℤ → E) (g : ℤ → ℤ → F)
    (r s a b : ℤ) :
    (∑ᶠ z : ℤ × ℤ, f (z.1 + a) (z.2 + b) ⊗ₜ[ℂ]
      g (r - 1 - z.1) (s - 1 - z.2)) = conv f g (r + a) (s + b) := by
  let H : ℤ × ℤ → E ⊗[ℂ] F := fun z =>
    f z.1 z.2 ⊗ₜ[ℂ] g (r + a - 1 - z.1) (s + b - 1 - z.2)
  calc
    _ = ∑ᶠ z : ℤ × ℤ, H (pairShift a b z) := by
      apply finsum_congr
      intro z
      dsimp [H, pairShift]
      congr 2 <;> omega
    _ = _ := finsum_comp_equiv (pairShift a b)

private theorem conv_delta_left {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] {f : ℤ → ℤ → E} {g : ℤ → ℤ → F}
    (h : PairFinite f g) : conv (delta f) g = delta (conv f g) := by
  funext r s
  simp only [conv, delta, TensorProduct.sub_tmul]
  rw [finsum_sub_distrib
    (by simpa only [add_zero] using pair_shift_finite h r s 1 0 0 0)
    (by simpa only [add_zero] using pair_shift_finite h r s 0 1 0 0)]
  have h1 := conv_shift f g r s 1 0
  have h2 := conv_shift f g r s 0 1
  simpa only [add_zero, conv] using congrArg₂ (· - ·) h1 h2

private theorem conv_delta_right {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] {f : ℤ → ℤ → E} {g : ℤ → ℤ → F}
    (h : PairFinite f g) : conv f (delta g) = delta (conv f g) := by
  funext r s
  simp only [conv, delta, TensorProduct.tmul_sub]
  rw [finsum_sub_distrib
    (by simpa only [add_zero] using pair_shift_finite h r s 0 0 1 0)
    (by simpa only [add_zero] using pair_shift_finite h r s 0 0 0 1)]
  congr 1 <;> apply finsum_congr <;> intro z <;> congr 2 <;> omega

private theorem conv_clear {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] {f : ℤ → ℤ → E} {g : ℤ → ℤ → F}
    (h : PairFinite f g) (p q : ℕ) :
    delta^[p + q] (conv f g) = conv (delta^[p] f) (delta^[q] g) := by
  have leftClear : delta^[p] (conv f g) = conv (delta^[p] f) g := by
    induction p with
    | zero => rfl
    | succ p ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact (conv_delta_left (pair_iterated h p 0)).symm
  have rightClear : delta^[q] (conv (delta^[p] f) g) =
      conv (delta^[p] f) (delta^[q] g) := by
    induction q with
    | zero => rfl
    | succ q ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact (conv_delta_right (pair_iterated h p q)).symm
  rw [Nat.add_comm p q, Function.iterate_add_apply, leftClear, rightClear]

private theorem same_order_finite {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (A C : VertexOperator ℂ E) (B G : VertexOperator ℂ F) (v : E) (w : F) :
    PairFinite (fun k l => (A[[k]]) ((C[[l]]) v))
      (fun p q => (B[[p]]) ((G[[q]]) w)) := by
  classical
  intro r s
  let I : Finset ℤ := Finset.Icc (s - cut G w) (cut C v - 1)
  let K (l : ℤ) : Finset ℤ :=
    Finset.Icc (r - cut B ((G[[s - 1 - l]]) w)) (cut A ((C[[l]]) v) - 1)
  let capture : Finset (ℤ × ℤ) := I.biUnion (fun l => (K l).image (fun k => (k, l)))
  apply capture.finite_toSet.subset
  intro z hz
  have hl : z.2 ∈ I := by
    by_contra h
    have hd : z.2 < s - cut G w ∨ cut C v - 1 < z.2 := by
      simpa only [I, Finset.mem_Icc, not_and_or, not_le] using h
    apply hz
    dsimp only
    rcases hd with hd | hd
    · rw [cut_kills G w _ (by omega), map_zero, TensorProduct.tmul_zero]
    · rw [cut_kills C v _ (by omega), map_zero, TensorProduct.zero_tmul]
  have hk : z.1 ∈ K z.2 := by
    by_contra h
    have hd : z.1 < r - cut B ((G[[s - 1 - z.2]]) w) ∨
        cut A ((C[[z.2]]) v) - 1 < z.1 := by
      simpa only [K, Finset.mem_Icc, not_and_or, not_le] using h
    apply hz
    dsimp only
    rcases hd with hd | hd
    · rw [cut_kills B _ _ (by omega), TensorProduct.tmul_zero]
    · rw [cut_kills A _ _ (by omega), TensorProduct.zero_tmul]
  exact Finset.mem_biUnion.mpr ⟨z.2, hl,
    Finset.mem_image.mpr ⟨z.1, hk, by cases z; rfl⟩⟩

private theorem conv_flip {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : ℤ → ℤ → E) (g : ℤ → ℤ → F)
    (r s : ℤ) : conv (fun k l => f l k) (fun p q => g q p) r s = conv f g s r := by
  exact finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
    (f := fun z : ℤ × ℤ => f z.1 z.2 ⊗ₜ[ℂ] g (s - 1 - z.1) (r - 1 - z.2))

private theorem conv_composition (D : LatticeData) (u v x : Carrier D)
    (a b w : Fock) (r s : ℤ) :
    (((Y D (u ⊗ₜ[ℂ] a))[[r]]) * ((Y D (v ⊗ₜ[ℂ] b))[[s]])) (x ⊗ₜ[ℂ] w) =
      conv
        (fun k l => ((LatticeAllStateField.Y D u)[[k]])
          (((LatticeAllStateField.Y D v)[[l]]) x))
        (fun p q => ((BcGhostStateField.Y a)[[p]])
          (((BcGhostStateField.Y b)[[q]]) w)) r s := by
  let f : ℤ × ℤ → State D := fun z =>
    ((LatticeAllStateField.Y D u)[[z.1]]) (((LatticeAllStateField.Y D v)[[z.2]]) x) ⊗ₜ[ℂ]
      ((BcGhostStateField.Y a)[[r - 1 - z.1]])
        (((BcGhostStateField.Y b)[[s - 1 - z.2]]) w)
  have hf : Function.HasFiniteSupport f := same_order_finite _ _ _ _ x w r s
  have hcurry : (∑ᶠ z : ℤ × ℤ, f z) = ∑ᶠ l : ℤ, ∑ᶠ k : ℤ, f (k, l) := by
    calc
      _ = ∑ᶠ z : ℤ × ℤ, f (Equiv.prodComm ℤ ℤ z) :=
        (finsum_comp_equiv (Equiv.prodComm ℤ ℤ)).symm
      _ = _ := finsum_curry _ (hf.fun_comp_of_injective (g := Equiv.prodComm ℤ ℤ) (Equiv.prodComm ℤ ℤ).injective)
  change ((Y D (u ⊗ₜ[ℂ] a))[[r]])
    (((Y D (v ⊗ₜ[ℂ] b))[[s]]) (x ⊗ₜ[ℂ] w)) = _
  rw [Y_tmul D v x b w s]
  rw [map_finsum _ (by
    simpa only [term_tmul] using term_finite D (v ⊗ₜ[ℂ] b) (x ⊗ₜ[ℂ] w) s)]
  simp only [Y_tmul]
  exact hcurry.symm

private theorem delta_left_tail {E : Type*} [AddCommGroup E] [Module ℂ E]
    (f : ℤ → ℤ → E) (M : ℤ)
    (h : ∀ p q : ℤ, M ≤ p → f p q = 0) (N : ℕ) :
    ∀ p q : ℤ, M ≤ p → (delta^[N] f) p q = 0 := by
  induction N with
  | zero => exact h
  | succ N ih =>
    intro p q hp
    rw [Function.iterate_succ_apply']
    simp only [delta, ih (p + 1) q (by omega), ih p (q + 1) hp, sub_self]

private theorem delta_right_tail {E : Type*} [AddCommGroup E] [Module ℂ E]
    (f : ℤ → ℤ → E) (M : ℤ)
    (h : ∀ p q : ℤ, M ≤ q → f p q = 0) (N : ℕ) :
    ∀ p q : ℤ, M ≤ q → (delta^[N] f) p q = 0 := by
  induction N with
  | zero => exact h
  | succ N ih =>
    intro p q hq
    rw [Function.iterate_succ_apply']
    simp only [delta, ih (p + 1) q hq, ih p (q + 1) (by omega), sub_self]

private theorem cleared_modes {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A C : VertexOperator ℂ E) (sign : ℂ) (N : ℕ)
    (h : delta^[N] (fun p q => (A[[p]]) * (C[[q]]) -
      sign • ((C[[q]]) * (A[[p]]))) = 0) (v : E) :
    let f := fun p q => (A[[p]]) ((C[[q]]) v)
    let rev := fun p q => (C[[q]]) ((A[[p]]) v)
    delta^[N] f = sign • delta^[N] rev ∧
      (∀ p q : ℤ, cut A v ≤ p ∨ cut C v ≤ q → (delta^[N] f) p q = 0) := by
  dsimp only
  let f := fun p q => (A[[p]]) ((C[[q]]) v)
  let rev := fun p q => (C[[q]]) ((A[[p]]) v)
  have he : delta^[N] (f - sign • rev) = 0 := by
    have hh := delta_evaluate
      (fun p q => (A[[p]]) * (C[[q]]) - sign • ((C[[q]]) * (A[[p]]))) v N
    rw [h] at hh
    simpa only [f, rev, Pi.sub_def, Pi.smul_def, Pi.zero_def, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
      LinearMap.zero_apply] using hh
  have eqClear : delta^[N] f = sign • delta^[N] rev := by
    have hh : (deltaLinear ^ N) (f - sign • rev) = 0 := by
      simpa only [deltaLinear_pow_apply] using he
    rw [map_sub, map_smul] at hh
    simpa only [deltaLinear_pow_apply] using sub_eq_zero.mp hh
  refine ⟨eqClear, ?_⟩
  intro p q hpq
  rcases hpq with hp | hq
  · rw [eqClear]
    change sign • (delta^[N] rev) p q = 0
    rw [delta_left_tail rev (cut A v) (by
      intro k l hk
      dsimp [rev]
      rw [cut_kills A v k hk, map_zero]) N p q hp, smul_zero]
  · exact delta_right_tail f (cut C v) (by
      intro k l hl
      dsimp [f]
      rw [cut_kills C v l hl, map_zero]) N p q hq

private theorem conv_rectangle {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : ℤ → ℤ → E) (g : ℤ → ℤ → F)
    (A C B G r s : ℤ)
    (hf : ∀ k l : ℤ, A ≤ k ∨ C ≤ l → f k l = 0)
    (hg : ∀ p q : ℤ, B ≤ p ∨ G ≤ q → g p q = 0) :
    conv f g r s = ∑ z ∈ (Finset.Icc (r - B) (A - 1)).product
        (Finset.Icc (s - G) (C - 1)),
      f z.1 z.2 ⊗ₜ[ℂ] g (r - 1 - z.1) (s - 1 - z.2) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro z hz
  by_contra h
  have hd : z.1 < r - B ∨ A - 1 < z.1 ∨ z.2 < s - G ∨ C - 1 < z.2 := by
    change z ∉ (Finset.Icc (r - B) (A - 1)).product (Finset.Icc (s - G) (C - 1)) at h
    simpa only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc,
      not_and_or, not_le, or_assoc] using h
  apply hz
  dsimp only
  rcases hd with h | h | h | h
  · rw [hg _ _ (Or.inl (by omega)), TensorProduct.tmul_zero]
  · rw [hf _ _ (Or.inl (by omega)), TensorProduct.zero_tmul]
  · rw [hg _ _ (Or.inr (by omega)), TensorProduct.tmul_zero]
  · rw [hf _ _ (Or.inr (by omega)), TensorProduct.zero_tmul]

private theorem conv_cleared_locality {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (A C : VertexOperator ℂ E) (B G : VertexOperator ℂ F)
    (sign : ℂ) (hsign : sign * sign = 1) (Nm Ng : ℕ)
    (hm : delta^[Nm] (fun p q => (A[[p]]) * (C[[q]]) - (C[[q]]) * (A[[p]])) = 0)
    (hg : delta^[Ng] (fun p q => (B[[p]]) * (G[[q]]) -
      sign • ((G[[q]]) * (B[[p]]))) = 0) (v : E) (w : F) :
    delta^[Nm + Ng]
      (conv (fun k l => (A[[k]]) ((C[[l]]) v))
        (fun p q => (B[[p]]) ((G[[q]]) w))) =
      sign • delta^[Nm + Ng]
        (conv (fun k l => (C[[l]]) ((A[[k]]) v))
          (fun p q => (G[[q]]) ((B[[p]]) w))) := by
  let f := fun k l => (A[[k]]) ((C[[l]]) v)
  let fr := fun k l => (C[[l]]) ((A[[k]]) v)
  let g := fun p q => (B[[p]]) ((G[[q]]) w)
  let gr := fun p q => (G[[q]]) ((B[[p]]) w)
  have hfm := cleared_modes A C 1 Nm (by simpa only [one_smul] using hm) v
  have hgg := cleared_modes B G sign Ng hg w
  have ef : delta^[Nm] f = delta^[Nm] fr := by simpa only [one_smul] using hfm.1
  have eg : delta^[Ng] g = sign • delta^[Ng] gr := hgg.1
  have er : delta^[Ng] gr = sign • delta^[Ng] g := by
    rw [eg, smul_smul, hsign, one_smul]
  have hfr : ∀ k l : ℤ, cut A v ≤ k ∨ cut C v ≤ l →
      (delta^[Nm] fr) k l = 0 := by
    rw [← ef]
    exact hfm.2
  have hgr : ∀ p q : ℤ, cut B w ≤ p ∨ cut G w ≤ q →
      (delta^[Ng] gr) p q = 0 := by
    intro p q h
    rw [er]
    change sign • (delta^[Ng] g) p q = 0
    rw [hgg.2 p q h, smul_zero]
  have forward : PairFinite f g := same_order_finite A C B G v w
  have reverse : PairFinite fr gr := by
    intro r s
    have h := same_order_finite C A G B v w s r
    simpa only [fr, gr, Equiv.prodComm_apply, Prod.swap] using
      h.fun_comp_of_injective (g := Equiv.prodComm ℤ ℤ) (Equiv.prodComm ℤ ℤ).injective
  rw [conv_clear forward Nm Ng, conv_clear reverse Nm Ng]
  funext r s
  simp only [Pi.smul_apply]
  rw [conv_rectangle (delta^[Nm] f) (delta^[Ng] g)
      (cut A v) (cut C v) (cut B w) (cut G w) r s hfm.2 hgg.2,
    conv_rectangle (delta^[Nm] fr) (delta^[Ng] gr)
      (cut A v) (cut C v) (cut B w) (cut G w) r s hfr hgr]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [ef, eg]
  exact TensorProduct.tmul_smul _ _ _

private def signedComm {E : Type*} [AddCommGroup E] [Module ℂ E]
    (sign : ℂ) (A B : VertexOperator ℂ E) : ℤ → ℤ → Module.End ℂ E :=
  fun r s => (A[[r]]) * (B[[s]]) - sign • ((B[[s]]) * (A[[r]]))

private def Local {E : Type*} [AddCommGroup E] [Module ℂ E]
    (sign : ℂ) (A B : VertexOperator ℂ E) : Prop :=
  ∃ N : ℕ, delta^[N] (signedComm sign A B) = 0

private theorem local_add_left {E : Type*} [AddCommGroup E] [Module ℂ E]
    (sign : ℂ) (A B C : VertexOperator ℂ E)
    (hA : Local sign A C) (hB : Local sign B C) : Local sign (A + B) C := by
  obtain ⟨p, hp⟩ := hA
  obtain ⟨q, hq⟩ := hB
  have hp' := FiniteFieldLocality.monotone (signedComm sign A C)
    p (max p q) (le_max_left _ _) hp
  have hq' := FiniteFieldLocality.monotone (signedComm sign B C)
    q (max p q) (le_max_right _ _) hq
  have split : signedComm sign (A + B) C = signedComm sign A C + signedComm sign B C := by
    funext r s
    simp only [signedComm, map_add, Pi.add_apply, mul_add, add_mul, smul_add]
    module
  refine ⟨max p q, ?_⟩
  rw [split]
  have he : (deltaLinear ^ max p q)
      (signedComm sign A C + signedComm sign B C) = 0 := by
    rw [map_add]
    simp only [deltaLinear_pow_apply, hp', hq', add_zero]
  simpa only [deltaLinear_pow_apply] using he

private theorem local_add_right {E : Type*} [AddCommGroup E] [Module ℂ E]
    (sign : ℂ) (A B C : VertexOperator ℂ E)
    (hB : Local sign A B) (hC : Local sign A C) : Local sign A (B + C) := by
  obtain ⟨p, hp⟩ := hB
  obtain ⟨q, hq⟩ := hC
  have hp' := FiniteFieldLocality.monotone (signedComm sign A B)
    p (max p q) (le_max_left _ _) hp
  have hq' := FiniteFieldLocality.monotone (signedComm sign A C)
    q (max p q) (le_max_right _ _) hq
  have split : signedComm sign A (B + C) = signedComm sign A B + signedComm sign A C := by
    funext r s
    simp only [signedComm, map_add, Pi.add_apply, mul_add, add_mul, smul_add]
    module
  refine ⟨max p q, ?_⟩
  rw [split]
  have he : (deltaLinear ^ max p q)
      (signedComm sign A B + signedComm sign A C) = 0 := by
    rw [map_add]
    simp only [deltaLinear_pow_apply, hp', hq', add_zero]
  simpa only [deltaLinear_pow_apply] using he

private theorem simple_locality (D : LatticeData) (u v : Carrier D) (a b : Fock)
    (p q : ℕ)
    (ha : CountableOccupationFock.parity a = (-1 : ℂ) ^ p • a)
    (hb : CountableOccupationFock.parity b = (-1 : ℂ) ^ q • b) :
    Local ((-1 : ℂ) ^ (p*q)) (Y D (u ⊗ₜ[ℂ] a)) (Y D (v ⊗ₜ[ℂ] b)) := by
  obtain ⟨Nm, hm⟩ := LatticeAllStateLocality.stateField_locality D u v
  obtain ⟨Ng, hg⟩ := BcGhostStateFieldLocality.stateField_locality a b p q ha hb
  let sign : ℂ := (-1 : ℂ) ^ (p*q)
  have hs : sign * sign = 1 := by
    simp [sign, ← mul_pow]
  refine ⟨Nm + Ng, ?_⟩
  funext r s
  apply TensorProduct.ext'
  intro x w
  let f := fun k l => ((LatticeAllStateField.Y D u)[[k]])
    (((LatticeAllStateField.Y D v)[[l]]) x)
  let fr := fun k l => ((LatticeAllStateField.Y D v)[[l]])
    (((LatticeAllStateField.Y D u)[[k]]) x)
  let g := fun k l => ((BcGhostStateField.Y a)[[k]]) (((BcGhostStateField.Y b)[[l]]) w)
  let gr := fun k l => ((BcGhostStateField.Y b)[[l]]) (((BcGhostStateField.Y a)[[k]]) w)
  have hclear : delta^[Nm + Ng] (conv f g) = sign • delta^[Nm + Ng] (conv fr gr) :=
    conv_cleared_locality _ _ _ _ sign hs Nm Ng hm hg x w
  have eforward : (fun r s =>
      (((Y D (u ⊗ₜ[ℂ] a))[[r]]) * ((Y D (v ⊗ₜ[ℂ] b))[[s]])) (x ⊗ₜ[ℂ] w)) =
      conv f g := by
    funext r s
    exact conv_composition D u v x a b w r s
  have ereverse : (fun r s =>
      (((Y D (v ⊗ₜ[ℂ] b))[[s]]) * ((Y D (u ⊗ₜ[ℂ] a))[[r]])) (x ⊗ₜ[ℂ] w)) =
      conv fr gr := by
    funext r s
    rw [conv_composition D v u x b a w s r]
    exact (conv_flip
      (fun k l => ((LatticeAllStateField.Y D v)[[k]])
        (((LatticeAllStateField.Y D u)[[l]]) x))
      (fun k l => ((BcGhostStateField.Y b)[[k]])
        (((BcGhostStateField.Y a)[[l]]) w)) r s).symm
  have einput : (fun r s => signedComm sign
      (Y D (u ⊗ₜ[ℂ] a)) (Y D (v ⊗ₜ[ℂ] b)) r s (x ⊗ₜ[ℂ] w)) =
      conv f g - sign • conv fr gr := by
    change (fun r s =>
      (((Y D (u ⊗ₜ[ℂ] a))[[r]]) * ((Y D (v ⊗ₜ[ℂ] b))[[s]])) (x ⊗ₜ[ℂ] w)) -
      sign • (fun r s =>
        (((Y D (v ⊗ₜ[ℂ] b))[[s]]) * ((Y D (u ⊗ₜ[ℂ] a))[[r]])) (x ⊗ₜ[ℂ] w)) = _
    rw [eforward, ereverse]
  have killed : delta^[Nm + Ng] (fun r s => signedComm sign
      (Y D (u ⊗ₜ[ℂ] a)) (Y D (v ⊗ₜ[ℂ] b)) r s (x ⊗ₜ[ℂ] w)) = 0 := by
    rw [einput]
    have he : (deltaLinear ^ (Nm + Ng)) (conv f g - sign • conv fr gr) = 0 := by
      rw [map_sub, map_smul]
      simpa only [deltaLinear_pow_apply] using sub_eq_zero.mpr hclear
    simpa only [deltaLinear_pow_apply] using he
  rw [delta_evaluate] at killed
  exact congrFun (congrFun killed r) s

/- Homogeneous projection extends simple-state locality through the original
tensor relations to all homogeneous states, changing neither carrier nor Y. -/

private def ghostProjection (p : ℕ) : Module.End ℂ Fock :=
  (2 : ℂ)⁻¹ • (LinearMap.id + (-1 : ℂ) ^ p • CountableOccupationFock.parity)

private theorem ghostProjection_homogeneous (p : ℕ) (a : Fock) :
    CountableOccupationFock.parity (ghostProjection p a) =
      (-1 : ℂ) ^ p • ghostProjection p a := by
  let z : ℂ := (-1 : ℂ) ^ p
  have hz : z * z = 1 := by
    simp [z, ← mul_pow]
  have hinv := LinearMap.congr_fun CountableOccupationFock.parity_involution a
  change CountableOccupationFock.parity (CountableOccupationFock.parity a) = a at hinv
  change CountableOccupationFock.parity ((2 : ℂ)⁻¹ •
    (a + z • CountableOccupationFock.parity a)) =
      z • ((2 : ℂ)⁻¹ • (a + z • CountableOccupationFock.parity a))
  rw [map_smul, map_add, map_smul, hinv, smul_comm z (2 : ℂ)⁻¹]
  congr 1
  rw [smul_add, smul_smul, hz, one_smul]
  exact add_comm _ _

private def project (D : LatticeData) (p : ℕ) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id (ghostProjection p)

private theorem project_formula (D : LatticeData) (p : ℕ) (x : State D) :
    project D p x = (2 : ℂ)⁻¹ • (x + (-1 : ℂ) ^ p • parity D x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v a =>
    simp only [project, ghostProjection, parity, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearMap.smul_apply, LinearMap.add_apply,
      TensorProduct.tmul_smul, TensorProduct.tmul_add]
  | add x y hx hy =>
    rw [map_add, hx, hy, map_add]
    module

private theorem project_fixed (D : LatticeData) (p : ℕ) (x : State D)
    (hx : parity D x = (-1 : ℂ) ^ p • x) : project D p x = x := by
  have hz : (-1 : ℂ) ^ p * (-1 : ℂ) ^ p = 1 := by
    simp [← mul_pow]
  rw [project_formula, hx, smul_smul, hz, one_smul, ← two_smul ℂ x, smul_smul]
  norm_num

/-- Genuine signed locality of the original all-state matter/ghost field.
The exponent is uniform over all input tensor states. Only the original
ghost parity of the two field states is assumed. No Jacobi law follows here. -/
theorem stateField_locality (D : LatticeData) (x y : State D) (p q : ℕ)
    (hx : parity D x = (-1 : ℂ) ^ p • x)
    (hy : parity D y = (-1 : ℂ) ^ q • y) :
    ∃ N : ℕ, delta^[N] (fun r s =>
      ((Y D x)[[r]]) * ((Y D y)[[s]]) - (-1 : ℂ) ^ (p*q) •
        (((Y D y)[[s]]) * ((Y D x)[[r]]))) = 0 := by
  let sign : ℂ := (-1 : ℂ) ^ (p*q)
  have allProjected (x y : State D) : Local sign
      (Y D (project D p x)) (Y D (project D q y)) := by
    induction x using TensorProduct.inductionOn with
    | tmul u a =>
      induction y using TensorProduct.inductionOn with
      | tmul v b =>
        simp only [project, TensorProduct.map_tmul, LinearMap.id_apply]
        exact simple_locality D u v (ghostProjection p a) (ghostProjection q b)
          p q (ghostProjection_homogeneous p a) (ghostProjection_homogeneous q b)
      | add y z hy hz =>
        simp only [map_add]
        exact local_add_right sign _ _ _ hy hz
    | add x z hx hz =>
      simp only [map_add]
      exact local_add_left sign _ _ _ hx hz
  have result := allProjected x y
  rw [project_fixed D p x hx, project_fixed D q y hy] at result
  exact result

end
end D5.S3.VertexAlgebra.LatticeMatterGhostStateField
