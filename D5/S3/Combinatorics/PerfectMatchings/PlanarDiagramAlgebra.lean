/- GID: D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.MonoidAlgebra.Module]
   utility: none
   digest: The free module on planar rectangle matchings with loop-zero concatenation. -/
import D5.S3.Combinatorics.PerfectMatchings.PlanarSewing
import D5.S3.Topology.BrauerZeroMonoid
import D5.S3.Topology.FiniteMatchingAssociativity
import D5.S3.Topology.FiniteMatchingClosure
import D5.S3.Topology.FiniteMatchingComposition
import D5.S3.Topology.FiniteMatchingSewing
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.Finsupp.LSum

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra
open CupCapBridgeProposal
open D5.S3.Combinatorics.PerfectMatchings.PlanarSewing
open D5.S3.Topology.FiniteMatchingClosure
open D5.S3.Topology.FiniteMatchingComposition
open D5.S3.Topology.FiniteMatchingSewing
open D5.S3.Topology.FiniteMatchingAssociativity
open D5.S3.Topology.BrauerZeroMonoid

/-- All literal noncrossing rectangle diagrams, with no quotient on pairings. -/
abbrev Diagram (n : ℕ) := {d : Matching (Boundary n) // ∃ M : NCMatching (2*n), toMatching M = d}

private def identity (n : ℕ) : Diagram n := ⟨identityMatching n, identity_planar n⟩

private def concat {n : ℕ} (a b : Diagram n) : Diagram n := by
  refine ⟨composite a.val b.val, ?_⟩
  obtain ⟨M,hM⟩ := a.property
  obtain ⟨N,hN⟩ := b.property
  simpa only [hM,hN] using composite_planar M N

private theorem concat_assoc {n : ℕ} (a b c : Diagram n) :
    concat (concat a b) c = concat a (concat b c) := Subtype.ext (composite_assoc ..)

/-- The carrier is exactly the free coefficient module on the diagram basis.
No multiplication on the index type is installed. -/
abbrev TL (R : Type*) [CommRing R] (n : ℕ) := MonoidAlgebra R (Diagram n)

variable {R : Type*} [CommRing R] {n : ℕ}

private def basisProduct (a b : Diagram n) : TL R n :=
  if internalLoopCount a.val b.val = 0 then MonoidAlgebra.single (concat a b) 1 else 0

private def bilinear : TL R n →ₗ[R] TL R n →ₗ[R] TL R n :=
  (Finsupp.lift _ R _ (fun a =>
    (Finsupp.lift _ R _ (basisProduct a)).comp
      (MonoidAlgebra.coeffLinearEquiv R).toLinearMap)).comp
        (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

instance : Mul (TL R n) := ⟨fun a b => bilinear a b⟩
instance : One (TL R n) := ⟨MonoidAlgebra.single (identity n) 1⟩

private theorem mul_def (a b : TL R n) : a*b = bilinear a b := rfl

private theorem add_mul' (a b c : TL R n) : (a+b)*c = a*c+b*c := by
  simp only [mul_def, map_add, LinearMap.add_apply]

private theorem mul_add' (a b c : TL R n) : a*(b+c) = a*b+a*c := (bilinear a).map_add b c

private theorem zero_mul' (a : TL R n) : 0*a = 0 := by
  simp only [mul_def, map_zero, LinearMap.zero_apply]

private theorem mul_zero' (a : TL R n) : a*0 = 0 := (bilinear a).map_zero

private theorem smul_mul' (r : R) (a b : TL R n) : (r • a)*b = r • (a*b) := by
  simp only [mul_def, map_smul, LinearMap.smul_apply]

private theorem mul_smul' (r : R) (a b : TL R n) : a*(r • b) = r • (a*b) :=
  (bilinear a).map_smul r b

private theorem basis_mul (a b : Diagram n) :
    (MonoidAlgebra.single a 1 : TL R n) * MonoidAlgebra.single b 1 = basisProduct a b := by
  simp [mul_def, bilinear, Finsupp.lift_apply]

private theorem induction {P : TL R n → Prop} (a : TL R n)
    (hz : P 0) (ha : ∀ a b, P a → P b → P (a+b))
    (hs : ∀ (r : R) a, P a → P (r • a))
    (hb : ∀ d : Diagram n, P (MonoidAlgebra.single d 1)) : P a := by
  have h : ∀ x : Diagram n →₀ R, P (MonoidAlgebra.ofCoeff x) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => exact hz
    | add x y hx hy => exact ha _ _ hx hy
    | single d r =>
      simpa only [MonoidAlgebra.smul_single, smul_eq_mul, mul_one, MonoidAlgebra.ofCoeff_single] using hs r _ (hb d)
  exact h a.coeff

private theorem flags {N : ℕ} (d e f : Matching (Boundary N)) :
    (0 < internalLoopCount d e ∨ 0 < internalLoopCount (composite d e) f) ↔
    (0 < internalLoopCount e f ∨ 0 < internalLoopCount d (composite e f)) := by
  have h := mul_assoc (some d : ZeroMatching N) (some e) (some f)
  have hl : ((some d : ZeroMatching N) * some e) * some f = none ↔
      (0 < internalLoopCount d e ∨ 0 < internalLoopCount (composite d e) f) := by
    rw [some_mul_some]
    by_cases hde : internalLoopCount d e = 0
    · rw [ite_eq_left hde, some_mul_some]
      split_ifs <;> simp_all <;> omega
    · rw [ite_eq_right hde]
      change (0 : ZeroMatching N) * some f = none ↔ _
      rw [zero_mul]
      exact ⟨fun _ => Or.inl (Nat.pos_of_ne_zero hde), fun _ => rfl⟩
  have hr : (some d : ZeroMatching N) * (some e * some f) = none ↔
      (0 < internalLoopCount e f ∨ 0 < internalLoopCount d (composite e f)) := by
    rw [some_mul_some e f]
    by_cases hef : internalLoopCount e f = 0
    · rw [ite_eq_left hef, some_mul_some]
      split_ifs <;> simp_all <;> omega
    · rw [ite_eq_right hef]
      change (some d : ZeroMatching N) * 0 = none ↔ _
      rw [mul_zero]
      exact ⟨fun _ => Or.inl (Nat.pos_of_ne_zero hef), fun _ => rfl⟩
  exact hl.symm.trans ((congrArg (fun a => a = none) h) ▸ hr)

private theorem basis_assoc (a b c : Diagram n) :
    ((MonoidAlgebra.single a 1 : TL R n) * MonoidAlgebra.single b 1) *
      MonoidAlgebra.single c 1 =
    MonoidAlgebra.single a 1 * (MonoidAlgebra.single b 1 * MonoidAlgebra.single c 1) := by
  have h := flags a.val b.val c.val
  rw [basis_mul, basis_mul]
  unfold basisProduct
  by_cases hab : internalLoopCount a.val b.val = 0
  · rw [ite_eq_left hab]
    by_cases hbc : internalLoopCount b.val c.val = 0
    · rw [ite_eq_left hbc, basis_mul, basis_mul]
      have he : (internalLoopCount (concat a b).val c.val = 0) ↔
          internalLoopCount a.val (concat b c).val = 0 := by dsimp [concat]; omega
      simp only [basisProduct, he, concat_assoc]
    · rw [ite_eq_right hbc, mul_zero', basis_mul]
      have he : internalLoopCount (concat a b).val c.val ≠ 0 := by dsimp [concat]; omega
      simp only [basisProduct, ite_eq_right he]
  · rw [ite_eq_right hab, zero_mul']
    by_cases hbc : internalLoopCount b.val c.val = 0
    · rw [ite_eq_left hbc, basis_mul]
      have he : internalLoopCount a.val (concat b c).val ≠ 0 := by dsimp [concat]; omega
      simp only [basisProduct, ite_eq_right he]
    · rw [ite_eq_right hbc, mul_zero']

private theorem mul_assoc' (a b c : TL R n) : a*b*c = a*(b*c) := by
  induction a using induction with
  | hz => simp only [zero_mul']
  | ha a b ha hb => simp only [add_mul', ha, hb]
  | hs r a ha => simp only [smul_mul', ha]
  | hb a =>
    induction b using induction with
    | hz => simp only [zero_mul', mul_zero']
    | ha b d hb hd => simp only [add_mul', mul_add', hb, hd]
    | hs r b hb => simp only [smul_mul', mul_smul', hb]
    | hb b =>
      induction c using induction with
      | hz => simp only [mul_zero']
      | ha c d hc hd => simp only [mul_add', hc, hd]
      | hs r c hc => simp only [mul_smul', hc]
      | hb c => exact basis_assoc a b c

private theorem one_mul' (a : TL R n) : 1*a = a := by
  induction a using induction with
  | hz => exact mul_zero' _
  | ha a b ha hb => simp only [mul_add', ha, hb]
  | hs r a ha => simp only [mul_smul', ha]
  | hb a =>
    change (MonoidAlgebra.single (identity n) 1 : TL R n) * _ = _
    rw [basis_mul]
    simp only [basisProduct, identity, internalLoopCount_left_identity, ite_eq_left rfl]
    exact congrArg (fun d => MonoidAlgebra.single d (1 : R))
      (show concat (identity n) a = a from Subtype.ext (composite_left_identity a.val))

private theorem mul_one' (a : TL R n) : a*1 = a := by
  induction a using induction with
  | hz => exact zero_mul' _
  | ha a b ha hb => simp only [add_mul', ha, hb]
  | hs r a ha => simp only [smul_mul', ha]
  | hb a =>
    change (MonoidAlgebra.single a 1 : TL R n) * MonoidAlgebra.single (identity n) 1 = _
    rw [basis_mul]
    simp only [basisProduct, identity, internalLoopCount_right_identity, ite_eq_left rfl]
    exact congrArg (fun d => MonoidAlgebra.single d (1 : R))
      (show concat a (identity n) = a from Subtype.ext (composite_right_identity a.val))

instance additiveWithOne : AddCommGroupWithOne (TL R n) where
  __ := (inferInstance : AddCommGroup (TL R n))
  one := MonoidAlgebra.single (identity n) 1

instance ring : Ring (TL R n) where
  __ := additiveWithOne
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  left_distrib := mul_add'
  right_distrib := add_mul'
  zero_mul := zero_mul'
  mul_zero := mul_zero'

instance algebra : Algebra R (TL R n) := Algebra.ofModule smul_mul' mul_smul'

/-- Bilinear concatenation kills a basis product exactly when it contains a loop. -/
theorem single_mul_single (a b : Diagram n) (r s : R) :
    (MonoidAlgebra.single a r : TL R n) * MonoidAlgebra.single b s =
      if internalLoopCount a.val b.val = 0 then MonoidAlgebra.single (concat a b) (r*s) else 0 := by
  have ha : MonoidAlgebra.single a r = r • (MonoidAlgebra.single a 1 : TL R n) := by simp
  have hb : MonoidAlgebra.single b s = s • (MonoidAlgebra.single b 1 : TL R n) := by simp
  rw [ha, hb, smul_mul', mul_smul', basis_mul]
  unfold basisProduct
  split_ifs <;> simp [smul_smul]

/-- The standard cup-cap generator at a zero-based index. -/
def generator (i : Fin (n-1)) : TL R n :=
  MonoidAlgebra.single ⟨cupcapMatching i.val (by omega),
    cupcap_planar n i.val (by omega)⟩ 1

/-- The open-boundary Hamiltonian with the sign convention of B.1. -/
def h (R : Type*) [CommRing R] (n : ℕ) : TL R n := -∑ i : Fin (n-1), generator i

end D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra
