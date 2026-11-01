/- GID: D5/S3/VertexAlgebra/Lattice/CyclicIsometryLift
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/CyclicIsometryLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sign-character correction gives exact-order actual cyclic lattice lifts. -/

import D5.S3.VertexAlgebra.Lattice.IsometryLift
import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.ZMod

/-!
The lattice is integral, symmetric and even; its rank may be zero and its form
may be singular or indefinite. The orbit character factors through the reduced
norm, so a sign character corrects the actual lift without a normalization
hypothesis. The all-state field law is the existing lift_compatible theorem.

proof_shape: cyclic_lift: content
admission_basis: escape-witness
escape_witness: The orbit quadratic phase telescopes to its value on the norm
plus the norm pairing. It therefore vanishes on the reduced norm kernel.
A functional on the norm image extends to all reduced charges, cancelling the
actual operator power. Distinct actual charge sectors detect the lower order.

The central-extension and lattice-lift context is classical (FLM,
Dong--Nagatomo and Lepowsky). Borcherds, Monstrous moonshine and monstrous Lie
superalgebras, Lemma 12.1, gives the standard-lift orbit argument in the Leech
setting. That reference is not an attribution of the singular and indefinite
generality here. No whole-isometry-group splitting or standard normalization
is asserted. Imported residue proofs retain the attributions of their sources.
All assertions are unrestricted algebraic ones, rather than finite instances,
enumerations, checkers or numerical reductions, hence utility is none.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction LatticeSugawaraConformal
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open MvPolynomial
open scoped BigOperators VertexOperator
noncomputable section

open private defect defectMatrix defect_symmetric defect_pairing
  additive_expansion oscillator_X oscillator_charge mixingMatrix from
  D5.S3.VertexAlgebra.Lattice.IsometryLift

private def q (D : LatticeData) (g : Charge D ≃+ Charge D) (a : Charge D) : F₂ :=
  normalExponent (defectMatrix D g) (reduceCharge D a)

private theorem defect_diagonal (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b) (i : Fin D.rank) :
    defectMatrix D g i i = 0 := by
  change (lowerCocycleExponent D (g (unitCharge D i)) (g (unitCharge D i)) : F₂) +
    (lowerCocycleExponent D (unitCharge D i) (unitCharge D i) : F₂) = 0
  rw [integral_cocycle_square, integral_cocycle_square, hg]
  exact CharTwo.add_self_eq_zero _

private theorem phase_sign (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b) (a : Charge D) :
    (IsometryLift.phase D g a : ℂ) = complexSign (q D g a) := by
  change liftPhase (defectMatrix D g) (reduceCharge D a) = _
  simp [liftPhase, diagonalPhase, defect_diagonal D g hg, fourthRoot, q]

private theorem sign_injective : Function.Injective complexSign := by
  intro a b h
  have hh : complexSignEmbedding.val (Multiplicative.ofAdd a) =
      complexSignEmbedding.val (Multiplicative.ofAdd b) := Units.ext h
  exact congrArg Multiplicative.toAdd (complexSignEmbedding.property hh)

private theorem q_zero (D : LatticeData) (g : Charge D ≃+ Charge D) :
    q D g 0 = 0 := by simp [q, normalExponent, reduceCharge]

private theorem q_add (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b) (a b : Charge D) :
    q D g (a+b) = q D g a + q D g b +
      integralCocycle D (g a) (g b) + integralCocycle D a b := by
  have hn := normal_exponent_add (defectMatrix D g) (reduceCharge D a) (reduceCharge D b)
  have hs := symmetric_pairing_split (defectMatrix D g) (defect_symmetric D g hg)
    (reduceCharge D a) (reduceCharge D b)
  simp only [defect_diagonal D g hg, zero_mul, Finset.sum_const_zero, zero_add] at hs
  rw [defect_pairing] at hs
  rw [← map_add] at hn
  change q D g a + q D g b = _ + q D g (a+b) at hn
  change integralCocycle D (g a) (g b) + integralCocycle D a b = _ at hs
  linear_combination (norm := (ring_nf; simp [show (2 : F₂) = 0 by decide])) hn + hs

/-- Sum of the first m charge iterates, including the identity iterate. -/
def orbitNorm (D : LatticeData) (g : Charge D ≃+ Charge D) (m : ℕ) :
    Charge D →+ Charge D where
  toFun a := ∑ j ∈ Finset.range m, g^[j] a
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

private def orbitExponent (D : LatticeData) (g : Charge D ≃+ Charge D)
    (m : ℕ) (a : Charge D) : F₂ :=
  ∑ j ∈ Finset.range m, q D g (g^[j] a)

private theorem norm_succ (D : LatticeData) (g : Charge D ≃+ Charge D)
    (n : ℕ) (a : Charge D) :
    orbitNorm D g (n+1) a = orbitNorm D g n a + g^[n] a := by
  simp [orbitNorm, Finset.sum_range_succ]

private theorem orbit_succ (D : LatticeData) (g : Charge D ≃+ Charge D)
    (n : ℕ) (a : Charge D) :
    orbitExponent D g (n+1) a = orbitExponent D g n a + q D g (g^[n] a) := by
  simp [orbitExponent, Finset.sum_range_succ]

private theorem norm_shift (D : LatticeData) (g : Charge D ≃+ Charge D)
    (n : ℕ) (a : Charge D) :
    g (orbitNorm D g n a) = orbitNorm D g n a - a + g^[n] a := by
  induction n with
  | zero => simp [orbitNorm]
  | succ n ih =>
    rw [norm_succ, map_add, ih, Function.iterate_succ_apply']
    abel

private theorem orbit_add_defect (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (n : ℕ) (a b : Charge D) :
    orbitExponent D g n (a+b) = orbitExponent D g n a + orbitExponent D g n b +
      integralCocycle D (g^[n] a) (g^[n] b) + integralCocycle D a b := by
  induction n with
  | zero => simp [orbitExponent, CharTwo.add_self_eq_zero]
  | succ n ih =>
    simp only [orbit_succ, iterate_map_add, q_add D g hg, ih,
      Function.iterate_succ_apply']
    ring_nf
    simp [show (2 : F₂) = 0 by decide]

private theorem prefix_identity (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (n : ℕ) (a : Charge D) :
    q D g (orbitNorm D g n a) + orbitExponent D g n a =
      integralCocycle D (orbitNorm D g n a - a) (g^[n] a) +
        integralCocycle D a (orbitNorm D g n a - a) := by
  induction n with
  | zero =>
    simp [orbitNorm, orbitExponent, q_zero, CharTwo.add_self_eq_zero]
  | succ n ih =>
    simp only [norm_succ, q_add D g hg, orbit_succ, norm_shift,
      Function.iterate_succ_apply', map_add, map_sub,
      AddMonoidHom.add_apply, AddMonoidHom.sub_apply]
    simp only [map_sub, AddMonoidHom.sub_apply] at ih
    linear_combination (norm := (ring_nf; simp [show (2 : F₂) = 0 by decide])) ih

private theorem cocycle_sym (D : LatticeData) (a b : Charge D) :
    integralCocycle D a b + integralCocycle D b a = (bilinear D a b : F₂) := by
  change (lowerCocycleExponent D a b : F₂) + (lowerCocycleExponent D b a : F₂) = _
  rw [← Int.cast_add, integral_cocycle_symmetrization]

private theorem orbit_norm (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (m : ℕ) (hgm : ∀ a, g^[m] a = a) (a : Charge D) :
    orbitExponent D g m a = q D g (orbitNorm D g m a) +
      (bilinear D a (orbitNorm D g m a) : F₂) := by
  have h := prefix_identity D g hg m a
  rw [hgm] at h
  simp only [map_sub, AddMonoidHom.sub_apply] at h
  have hc := cocycle_sym D a (orbitNorm D g m a)
  linear_combination (norm := (ring_nf; simp [show (2 : F₂) = 0 by decide])) h + hc

/-- The additive orbit sign. Its additivity is proved by cocycle telescoping. -/
def orbitCharacter (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (m : ℕ) (hgm : ∀ a, g^[m] a = a) : Charge D →+ F₂ where
  toFun := orbitExponent D g m
  map_zero' := by simp [orbitExponent, q_zero]
  map_add' a b := by
    have h := orbit_add_defect D g hg m a b
    simpa only [hgm, add_assoc, CharTwo.add_self_eq_zero, add_zero] using h

private theorem orbitCharacter_apply (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (m : ℕ) (hgm : ∀ a, g^[m] a = a) (a : Charge D) :
    orbitCharacter D g hg m hgm a = orbitExponent D g m a := rfl

private theorem orbit_shift (D : LatticeData) (g : Charge D ≃+ Charge D)
    (n : ℕ) (a : Charge D) :
    orbitExponent D g n (g a) + q D g a =
      orbitExponent D g n a + q D g (g^[n] a) := by
  induction n with
  | zero => simp [orbitExponent]
  | succ n ih =>
    simp only [orbit_succ, Function.iterate_succ_apply]
    linear_combination ih

private def diagonalLinear (D : LatticeData) (chi : Charge D →+ F₂) :
    Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun a => complexSign (chi a) • Finsupp.lsingle a)

private theorem diagonalLinear_single (D : LatticeData) (chi : Charge D →+ F₂)
    (a : Charge D) (p : Oscillator D) :
    diagonalLinear D chi (Finsupp.single a p) =
      complexSign (chi a) • Finsupp.single a p := by
  simp [diagonalLinear]

private theorem diagonal_involutive (D : LatticeData) (chi : Charge D →+ F₂) :
    Function.Involutive (diagonalLinear D chi) := by
  have h : (diagonalLinear D chi).comp (diagonalLinear D chi) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro a p
    simp [LinearMap.comp_apply, diagonalLinear_single, smul_smul, sign_square]
  exact LinearMap.congr_fun h

/-- The actual charge-character action, with no pairing-character restriction. -/
def diagonal (D : LatticeData) (chi : Charge D →+ F₂) :
    Carrier D ≃ₗ[ℂ] Carrier D :=
  LinearEquiv.ofInvolutive (diagonalLinear D chi) (diagonal_involutive D chi)

private theorem diagonal_single (D : LatticeData) (chi : Charge D →+ F₂)
    (a : Charge D) (p : Oscillator D) :
    diagonal D chi (Finsupp.single a p) =
      complexSign (chi a) • Finsupp.single a p :=
  diagonalLinear_single D chi a p

private theorem diagonal_vacuum (D : LatticeData) (chi : Charge D →+ F₂) :
    diagonal D chi (vacuum D) = vacuum D := by
  simp [vacuum, diagonal_single, sign_zero]

private theorem diagonal_modes (D : LatticeData) (chi : Charge D →+ F₂)
    (u v : Carrier D) (n : ℤ) :
    diagonal D chi (((Y D u)[[n]]) v) =
      ((Y D (diagonal D chi u))[[n]]) (diagonal D chi v) := by
  let left : Carrier D →ₗ[ℂ] Carrier D :=
    { toFun := fun u => diagonalLinear D chi (((Y D u)[[n]]) v)
      map_add' := by intro u w; simp
      map_smul' := by intro c u; simp }
  let right : Carrier D →ₗ[ℂ] Carrier D :=
    { toFun := fun u => ((Y D (diagonalLinear D chi u))[[n]]) (diagonalLinear D chi v)
      map_add' := by intro u w; simp
      map_smul' := by intro c u; simp }
  have h : left = right := by
    apply Finsupp.lhom_ext
    intro a p
    let l : Carrier D →ₗ[ℂ] Carrier D :=
      (diagonalLinear D chi).comp ((Y D (Finsupp.single a p))[[n]])
    let r : Carrier D →ₗ[ℂ] Carrier D :=
      ((Y D (diagonalLinear D chi (Finsupp.single a p)))[[n]]).comp (diagonalLinear D chi)
    have he : l = r := by
      apply Finsupp.lhom_ext
      intro b p'
      change diagonalLinear D chi
        (((Y D (Finsupp.single a p))[[n]]) (Finsupp.single b p')) = _
      have hh := LatticeSectorIntertwiner.charge_homogeneity D a b p p' n
      rw [hh, diagonalLinear_single]
      change _ = ((Y D (diagonalLinear D chi (Finsupp.single a p)))[[n]])
        (diagonalLinear D chi (Finsupp.single b p'))
      rw [diagonalLinear_single, diagonalLinear_single, map_smul]
      simp only [VertexOperator.ncoeff, Pi.smul_apply, LinearMap.smul_apply, map_smul]
      rw [smul_smul, ← complexSign_add, ← map_add]
      simpa only [VertexOperator.ncoeff, LinearMap.smul_apply, add_comm] using
        congrArg (fun w : Carrier D => complexSign (chi (a+b)) • w) hh.symm
    exact LinearMap.congr_fun he v
  exact LinearMap.congr_fun h u

/-- U_g D_chi on the actual finite-support carrier. -/
def corrected (D : LatticeData) (g : Charge D ≃+ Charge D) (chi : Charge D →+ F₂) :
    Carrier D ≃ₗ[ℂ] Carrier D :=
  (diagonal D chi).trans (IsometryLift.lift D g)

private theorem corrected_single (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (chi : Charge D →+ F₂) (a : Charge D) (p : Oscillator D) :
    corrected D g chi (Finsupp.single a p) =
      complexSign (q D g a + chi a) •
        Finsupp.single (g a) (IsometryLift.oscillator D g p) := by
  simp only [corrected, LinearEquiv.trans_apply, diagonal_single, map_smul,
    IsometryLift.lift_single, phase_sign D g hg, smul_smul, complexSign_add]
  rw [mul_comm]

private theorem corrected_compatible (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (chi : Charge D →+ F₂) :
    corrected D g chi (vacuum D) = vacuum D ∧
    (∀ (u : Carrier D) (n : ℤ) (v : Carrier D),
      corrected D g chi (((Y D u)[[n]]) v) =
        ((Y D (corrected D g chi u))[[n]]) (corrected D g chi v)) ∧
    (∀ v : Carrier D, corrected D g chi (translation D v) =
      translation D (corrected D g chi v)) := by
  have h := IsometryLift.lift_compatible D g hg
  have hv : corrected D g chi (vacuum D) = vacuum D := by
    change IsometryLift.lift D g (diagonal D chi (vacuum D)) = _
    rw [diagonal_vacuum, h.1]
  have hy (u : Carrier D) (n : ℤ) (v : Carrier D) :
      corrected D g chi (((Y D u)[[n]]) v) =
        ((Y D (corrected D g chi u))[[n]]) (corrected D g chi v) := by
    change IsometryLift.lift D g (diagonal D chi (((Y D u)[[n]]) v)) = _
    rw [diagonal_modes, h.2.2.1]
    rfl
  refine ⟨hv, hy, ?_⟩
  intro v
  rw [LatticeActualVertexAlgebra.translation_as_mode, hy, hv,
    ← LatticeActualVertexAlgebra.translation_as_mode]

private theorem oscillator_pow_X (D : LatticeData) (g : Charge D ≃+ Charge D)
    (n : ℕ) (x : Index D) :
    (IsometryLift.oscillator D g ^ n) (X x) =
      ∑ j : Fin D.rank, (g^[n] (unitCharge D x.1) j : ℂ) • X (j,x.2) := by
  induction n with
  | zero =>
    simp [unitCharge, apply_ite, ite_smul]
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, oscillator_charge,
      Function.iterate_succ_apply']

private theorem oscillator_pow_fixed (D : LatticeData) (g : Charge D ≃+ Charge D)
    (m : ℕ) (hgm : ∀ a, g^[m] a = a) (p : Oscillator D) :
    (IsometryLift.oscillator D g ^ m) p = p := by
  induction p using MvPolynomial.induction_on with
  | C c => exact (IsometryLift.oscillator D g ^ m).commutes c
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p x hp =>
    rw [map_mul, hp, oscillator_pow_X, hgm]
    simp [unitCharge, apply_ite, ite_smul]

private theorem corrected_pow_single (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (chi : Charge D →+ F₂) (n : ℕ) (a : Charge D) (p : Oscillator D) :
    (corrected D g chi ^ n) (Finsupp.single a p) =
      complexSign (orbitExponent D g n a + chi (orbitNorm D g n a)) •
        Finsupp.single (g^[n] a) ((IsometryLift.oscillator D g ^ n) p) := by
  induction n with
  | zero => simp [orbitExponent, orbitNorm, sign_zero]
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, corrected_single D g hg]
    rw [orbit_succ, norm_succ, map_add, Function.iterate_succ_apply',
      pow_succ', AlgEquiv.mul_apply]
    rw [smul_smul, ← complexSign_add]
    congr 2
    ring

private theorem corrected_zero (D : LatticeData) (g : Charge D ≃+ Charge D) :
    corrected D g 0 = IsometryLift.lift D g := by
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro a p
  simp [corrected, diagonal_single, sign_zero]

/-- The canonical power is the orbit-character operator; its invariant sign is
the literal phase on the orbit norm times the actual integral norm pairing. -/
theorem canonical_power (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (m : ℕ) (hgm : ∀ a, g^[m] a = a) :
    (IsometryLift.lift D g)^m = diagonal D (orbitCharacter D g hg m hgm) ∧
    (∀ a, orbitCharacter D g hg m hgm (g a) = orbitCharacter D g hg m hgm a) ∧
    (∀ a, complexSign (orbitCharacter D g hg m hgm a) =
      ∏ j ∈ Finset.range m, (IsometryLift.phase D g (g^[j] a) : ℂ)) ∧
    (∀ a, complexSign (orbitCharacter D g hg m hgm a) =
      (IsometryLift.phase D g (orbitNorm D g m a) : ℂ) *
        paritySign (bilinear D a (orbitNorm D g m a))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply LinearEquiv.toLinearMap_injective
    apply Finsupp.lhom_ext
    intro a p
    change (IsometryLift.lift D g ^ m) (Finsupp.single a p) =
      diagonal D (orbitCharacter D g hg m hgm) (Finsupp.single a p)
    rw [diagonal_single]
    rw [orbitCharacter_apply]
    have h := corrected_pow_single D g hg 0 m a p
    rw [corrected_zero] at h
    simpa only [AddMonoidHom.zero_apply, add_zero, hgm,
      oscillator_pow_fixed D g m hgm] using h
  · intro a
    have h := orbit_shift D g m a
    rw [hgm] at h
    exact add_right_cancel h
  · intro a
    simp only [phase_sign D g hg]
    exact sign_sum (Finset.range m) (fun j => q D g (g^[j] a))
  · intro a
    rw [phase_sign D g hg, ← complexSign_integral, ← complexSign_add]
    exact congrArg complexSign (orbit_norm D g hg m hgm a)

private def reducedMap (D : LatticeData) {V : Type*} [AddCommGroup V] [Module F₂ V]
    (f : Charge D →+ V) : ModTwoCharge D →ₗ[F₂] V where
  toFun x := ∑ i : Fin D.rank, x i • f (unitCharge D i)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

private theorem reducedMap_reduce (D : LatticeData) {V : Type*}
    [AddCommGroup V] [Module F₂ V] (f : Charge D →+ V) (a : Charge D) :
    reducedMap D f (reduceCharge D a) = f a := by
  change (∑ i : Fin D.rank, (a i : F₂) • f (unitCharge D i)) = f a
  simpa only [Int.cast_smul_eq_zsmul] using (additive_expansion D f a).symm

private theorem reduce_surjective (D : LatticeData) :
    Function.Surjective (reduceCharge D) := by
  intro x
  refine ⟨fun i => (x i).val, ?_⟩
  ext i
  simp [reduceCharge]

private theorem correction_exists (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (m : ℕ) (hgm : ∀ a, g^[m] a = a) :
    ∃ chi : Charge D →+ F₂, ∀ a,
      chi (orbitNorm D g m a) = orbitCharacter D g hg m hgm a := by
  let Q := orbitCharacter D g hg m hgm
  let N := reducedMap D ((reduceCharge D).comp (orbitNorm D g m))
  let qbar := reducedMap D Q
  have hk : LinearMap.ker N ≤ LinearMap.ker qbar := by
    intro x hx
    obtain ⟨a, rfl⟩ := reduce_surjective D x
    have hn : reduceCharge D (orbitNorm D g m a) = 0 := by
      simpa only [N, reducedMap_reduce, AddMonoidHom.comp_apply, LinearMap.mem_ker] using hx
    have hq : q D g (orbitNorm D g m a) = 0 := by
      simp [q, hn, normalExponent]
    have hb : (bilinear D a (orbitNorm D g m a) : F₂) = 0 := by
      rw [← cocycle_sym]
      simp [← cocycle_reduction, hn]
    have hs := (canonical_power D g hg m hgm).2.2.2 a
    simp only [phase_sign D g hg, hq, ← complexSign_integral, hb, sign_zero,
      mul_one] at hs
    change qbar (reduceCharge D a) = 0
    rw [reducedMap_reduce]
    exact sign_injective (hs.trans sign_zero.symm)
  let f : N.range →ₗ[F₂] F₂ :=
    N.rangeRestrict.liftOfSurjective N.surjective_rangeRestrict
      ⟨qbar, by simpa only [LinearMap.ker_rangeRestrict] using hk⟩
  obtain ⟨ell, hell⟩ := f.exists_extend
  refine ⟨ell.toAddMonoidHom.comp (reduceCharge D), ?_⟩
  intro a
  have h := LinearMap.congr_fun hell (N.rangeRestrict (reduceCharge D a))
  have hf := LinearMap.equivOfSurjective_apply (f := N.rangeRestrict)
    N.surjective_rangeRestrict
    (by simpa only [LinearMap.ker_rangeRestrict] using hk)
    (m := reduceCharge D a)
  change ell (N (reduceCharge D a)) = f (N.rangeRestrict (reduceCharge D a)) at h
  rw [show f (N.rangeRestrict (reduceCharge D a)) = qbar (reduceCharge D a) from hf] at h
  change ell (reduceCharge D (orbitNorm D g m a)) = Q a
  simpa only [N, qbar, reducedMap_reduce, AddMonoidHom.comp_apply] using h

private theorem charge_detects_power (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (chi : Charge D →+ F₂) (k : ℕ) (hk : corrected D g chi ^ k = 1) :
    g.toEquiv ^ k = 1 := by
  classical
  apply Equiv.ext
  intro a
  have h := congrArg (fun W : Carrier D ≃ₗ[ℂ] Carrier D =>
    W (Finsupp.single a (1 : Oscillator D))) hk
  rw [corrected_pow_single D g hg, map_one] at h
  change complexSign (orbitExponent D g k a + chi (orbitNorm D g k a)) •
      Finsupp.single (g^[k] a) (1 : Oscillator D) = Finsupp.single a 1 at h
  rw [Finsupp.smul_single] at h
  have hh := (Finsupp.single_eq_single_iff _ _ _ _).mp h
  rcases hh with ⟨ha, _⟩ | ⟨_, hb⟩
  · exact ha
  · exact (one_ne_zero hb).elim

/-- Every finite-order additive lattice isometry admits a sign-character
correction on the actual carrier. It preserves the actual vacuum, translation
and every integer mode on arbitrary states. Exact charge order is also exact
operator order, for every natural exponent including zero. -/
theorem cyclic_lift (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (m : ℕ) (_hm : 0 < m) (hgm : ∀ a, g^[m] a = a) :
    ∃ chi : Charge D →+ F₂,
      corrected D g chi (vacuum D) = vacuum D ∧
      (∀ (u : Carrier D) (n : ℤ) (v : Carrier D),
        corrected D g chi (((Y D u)[[n]]) v) =
          ((Y D (corrected D g chi u))[[n]]) (corrected D g chi v)) ∧
      (∀ v : Carrier D, corrected D g chi (translation D v) =
        translation D (corrected D g chi v)) ∧
      corrected D g chi ^ m = 1 ∧
      (orderOf g.toEquiv = m → ∀ k : ℕ, corrected D g chi ^ k = 1 ↔ m ∣ k) := by
  obtain ⟨chi, hchi⟩ := correction_exists D g hg m hgm
  have hc := corrected_compatible D g hg chi
  have hp : corrected D g chi ^ m = 1 := by
    apply LinearEquiv.toLinearMap_injective
    apply Finsupp.lhom_ext
    intro a p
    change (corrected D g chi ^ m) (Finsupp.single a p) = Finsupp.single a p
    rw [corrected_pow_single D g hg, hchi, hgm, oscillator_pow_fixed D g m hgm]
    rw [orbitCharacter_apply, CharTwo.add_self_eq_zero, sign_zero, one_smul]
  refine ⟨chi, hc.1, hc.2.1, hc.2.2, hp, ?_⟩
  intro hord k
  constructor
  · intro hk
    rw [← hord, orderOf_dvd_iff_pow_eq_one]
    exact charge_detects_power D g hg chi k hk
  · rintro ⟨t, rfl⟩
    rw [pow_mul, hp, one_pow]

end
end D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
