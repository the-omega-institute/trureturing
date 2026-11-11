/- GID: D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.GroupExtension.Defs]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample.claim; result=D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample.result; claim=D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample.claim
   digest: The sign action on F3 has bijective native quotient norm but its D9 extension does not split. -/

import D5.S3.FiniteGroups.GroupAlgebra.SemilinearKernelNorm
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.Tactic.Abel

/-!
For the sign action of D₃ on F₃, native coinvariants and invariants both vanish,
so the actual quotient norm is bijective. The compatible extension
1 → C₃ → D₉ → D₃ → 1 nevertheless has no homomorphic splitting.
This refutes the implication from bijective coinvariant norm to splitting for
arbitrary finite base groups and compatible abelian kernels. It makes no claim
that the underlying norm on the nonzero module F₃ is injective.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.NoncyclicNormSplittingCounterexample

open DihedralGroup

private abbrev F3 := ZMod 3
private abbrev Kernel := Multiplicative F3
private abbrev Base := DihedralGroup 3
private abbrev Total := DihedralGroup 9

/-- Rotations act as the identity and reflections act as negation. -/
private def signRepresentation : Representation F3 Base F3 where
  toFun
    | r _ => LinearMap.id
    | sr _ => -LinearMap.id
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;> apply LinearMap.ext <;> intro a
    · rfl
    · rfl
    · rfl
    · exact (neg_neg a).symm

@[simp] private theorem sign_r (i : ZMod 3) (a : F3) :
    signRepresentation (r i) a = a := rfl

@[simp] private theorem sign_sr (i : ZMod 3) (a : F3) :
    signRepresentation (sr i) a = -a := rfl

private theorem neg_fixed_zero : ∀ a : F3, -a = a → a = 0 := by decide

private theorem reflection_difference : ∀ a : F3, -a - a = a := by decide

/-- A reflection kills every invariant, since 2 is nonzero in F₃. -/
private theorem invariant_eq_zero (a : signRepresentation.invariants) : a = 0 := by
  apply Subtype.ext
  change (a : F3) = 0
  have h := (Representation.mem_invariants signRepresentation (a : F3)).mp
    a.property (sr 0)
  exact neg_fixed_zero (a : F3) (by simpa only [sign_sr] using h)

/-- Every vector is an actual generator difference for the native kernel. -/
private theorem mem_coinvariants_ker (a : F3) :
    a ∈ Representation.Coinvariants.ker signRepresentation := by
  apply Representation.Coinvariants.mem_ker_of_eq (ρ := signRepresentation) (sr 0) a a
  simpa only [sign_sr] using reflection_difference a

private theorem coinvariant_eq_zero (q : signRepresentation.Coinvariants) : q = 0 := by
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective signRepresentation q
  exact (Representation.Coinvariants.mk_eq_zero signRepresentation).2 (mem_coinvariants_ker a)

/-- Bijectivity of the imported norm on the actual native quotient.
This theorem does not claim injectivity of the norm on the original module F₃. -/
private theorem coinvariantsNorm_bijective :
    Function.Bijective (SemilinearKernelNorm.coinvariantsNorm signRepresentation) := by
  constructor
  · intro x y _
    exact (coinvariant_eq_zero x).trans (coinvariant_eq_zero y).symm
  · intro y
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact (invariant_eq_zero y).symm

/-- The native residue homomorphism Z/9 → Z/3. -/
private def reduction : ZMod 9 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3)

/-- Reduction of the rotation index, preserving the reflection tag. -/
private def quotientMap : Total →* Base where
  toFun
    | r i => r (reduction i)
    | sr i => sr (reduction i)
  map_one' := by
    change r (reduction 0) = r 0
    rw [map_zero]
  map_mul' := by
    rintro (i | i) (j | j)
    · change r (reduction (i + j)) = r (reduction i + reduction j)
      rw [map_add]
    · change sr (reduction (j - i)) = sr (reduction j - reduction i)
      rw [map_sub]
    · change sr (reduction (i + j)) = sr (reduction i + reduction j)
      rw [map_add]
    · change r (reduction (j - i)) = r (reduction j - reduction i)
      rw [map_sub]

private theorem quotientMap_surjective : Function.Surjective quotientMap := by
  have hred : Function.Surjective reduction :=
    ZMod.castHom_surjective (by decide : 3 ∣ 9)
  rintro (i | i)
  · obtain ⟨j, hj⟩ := hred i
    exact ⟨r j, congrArg DihedralGroup.r hj⟩
  · obtain ⟨j, hj⟩ := hred i
    exact ⟨sr j, congrArg DihedralGroup.sr hj⟩

/-- Additive embedding a ↦ 3a; `val` chooses the representatives 0, 1, 2.
The additivity decision checks just nine pairs of residues. -/
private def triple : F3 →+ ZMod 9 where
  toFun a := 3 * (a.val : ZMod 9)
  map_zero' := by decide
  map_add' := by decide

private theorem triple_injective : Function.Injective triple := by decide

/-- Exact residue description of the kernel: the only indices are 0, 3, 6. -/
private theorem reduction_zero_iff :
    ∀ i : ZMod 9, reduction i = 0 ↔ ∃ a : F3, triple a = i := by decide

/-- Kernel inclusion C₃ → D₉, with the additive kernel written multiplicatively. -/
private def kernelInclusion : Kernel →* Total where
  toFun a := r (triple a.toAdd)
  map_one' := by
    change r (triple 0) = 1
    rw [map_zero, r_zero]
  map_mul' a b := by
    change r (triple (a.toAdd + b.toAdd)) = r (triple a.toAdd) * r (triple b.toAdd)
    rw [map_add, r_mul_r]

private theorem kernelInclusion_injective : Function.Injective kernelInclusion := by
  intro a b hab
  change r (triple a.toAdd) = r (triple b.toAdd) at hab
  exact Multiplicative.toAdd.injective (triple_injective (DihedralGroup.r.inj hab))

private theorem kernelInclusion_range : kernelInclusion.range = quotientMap.ker := by
  apply Subgroup.ext
  intro x
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  cases x with
  | r i =>
      change (∃ a : Kernel, r (triple a.toAdd) = r i) ↔ r (reduction i) = r 0
      simp only [DihedralGroup.r.injEq]
      constructor
      · rintro ⟨a, ha⟩
        exact (reduction_zero_iff i).2 ⟨a.toAdd, ha⟩
      · intro hi
        obtain ⟨a, ha⟩ := (reduction_zero_iff i).1 hi
        exact ⟨Multiplicative.ofAdd a, ha⟩
  | sr i =>
      constructor
      · rintro ⟨a, ha⟩
        change r (triple a.toAdd) = sr i at ha
        cases ha
      · intro hi
        change sr (reduction i) = r 0 at hi
        cases hi

/-- The actual native extension 1 → C₃ → D₉ → D₃ → 1. -/
private def extension : GroupExtension Kernel Total Base where
  inl := kernelInclusion
  rightHom := quotientMap
  inl_injective := kernelInclusion_injective
  range_inl_eq_ker_rightHom := kernelInclusion_range
  rightHom_surjective := quotientMap_surjective

/-- Explicitly remove both group-law type tags from the abelian kernel. -/
private def kernelAddEquiv : Additive Kernel ≃+ F3 where
  toFun a := a.toMul.toAdd
  invFun a := Additive.ofMul (Multiplicative.ofAdd a)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Concrete conjugation calculation in D₉: rotations fix, reflections invert. -/
private theorem conjugation_kernel (e : Total) (a : F3) :
    e * kernelInclusion (Multiplicative.ofAdd a) * e⁻¹ =
      kernelInclusion (Multiplicative.ofAdd (signRepresentation (quotientMap e) a)) := by
  cases e with
  | r i =>
      change r (i + triple a + -i) = r (triple a)
      congr 1
      abel
  | sr i =>
      change r (i - (i + triple a)) = r (triple (-a))
      rw [map_neg]
      congr 1
      abel

/-- The native extension conjugation action, under the displayed identification,
is exactly the representation used by the quotient norm. -/
private theorem extension_action_compatible (e : Total) (a : Additive Kernel) :
    kernelAddEquiv (Additive.ofMul (extension.conjAct e a.toMul)) =
      signRepresentation (extension.rightHom e) (kernelAddEquiv a) := by
  have h : extension.conjAct e a.toMul =
      Multiplicative.ofAdd (signRepresentation (extension.rightHom e) (kernelAddEquiv a)) := by
    apply extension.inl_injective
    rw [extension.inl_conjAct_comm]
    exact conjugation_kernel e (kernelAddEquiv a)
  exact congrArg (fun x : Kernel => x.toAdd) h

/-- The three actual rotation-index lifts of 1 ∈ Z/3. -/
private theorem reduction_one_lifts :
    ∀ i : ZMod 9, reduction i = 1 → i = 1 ∨ i = 4 ∨ i = 7 := by decide

/-- A lift of the rotation generator cannot have cube equal to the identity.
Only its three possible rotation indices are checked, using native `r_pow`. -/
private theorem lift_cube_ne_one (x : Total) (hx : quotientMap x = r 1) : x ^ 3 ≠ 1 := by
  cases x with
  | r i =>
      have hi : reduction i = 1 := DihedralGroup.r.inj hx
      rcases reduction_one_lifts i hi with rfl | rfl | rfl <;>
        rw [DihedralGroup.r_pow, DihedralGroup.one_def] <;> decide
  | sr i =>
      change sr (reduction i) = r 1 at hx
      cases hx

/-- No native splitting exists; a homomorphic section would preserve r₁³ = 1. -/
private theorem no_splitting : ¬ Nonempty extension.Splitting := by
  rintro ⟨s⟩
  have hx : quotientMap (s (r 1)) = r 1 := s.rightInverse_rightHom (r 1)
  have hc : (s (r 1)) ^ 3 = 1 := by
    calc
      (s (r 1)) ^ 3 = s ((r (1 : ZMod 3)) ^ 3) := (map_pow s _ 3).symm
      _ = s 1 := congrArg s (DihedralGroup.r_one_pow_n (n := 3))
      _ = 1 := map_one s
  exact lift_cube_ne_one (s (r 1)) hx hc

/-- A single noncyclic specimen has bijective native quotient norm and a
compatible nonsplit extension with nontrivial abelian kernel. -/
theorem noncyclic_norm_splitting_counterexample :
    ∃ (ρ : Representation (ZMod 3) (DihedralGroup 3) (ZMod 3))
      (S : GroupExtension (Multiplicative (ZMod 3)) (DihedralGroup 9) (DihedralGroup 3))
      (ι : Additive (Multiplicative (ZMod 3)) ≃+ ZMod 3),
      (∀ (i : ZMod 3) (a : ZMod 3), ρ (r i) a = a) ∧
      (∀ (i : ZMod 3) (a : ZMod 3), ρ (sr i) a = -a) ∧
      ¬ IsCyclic (DihedralGroup 3) ∧
      Function.Bijective (SemilinearKernelNorm.coinvariantsNorm ρ) ∧
      (∀ (e : DihedralGroup 9) (a : Additive (Multiplicative (ZMod 3))),
        ι (Additive.ofMul (S.conjAct e a.toMul)) = ρ (S.rightHom e) (ι a)) ∧
      ¬ Nonempty S.Splitting := by
  exact ⟨signRepresentation, extension, kernelAddEquiv, sign_r, sign_sr,
    DihedralGroup.not_isCyclic (by decide : (3 : ℕ) ≠ 1),
    coinvariantsNorm_bijective, extension_action_compatible, no_splitting⟩

/-- The proposed unrestricted norm-splitting implication, using the native norm,
conjugation action and group-extension splitting. All carriers lie in `Type`.
There is no cyclicity or trace-one hypothesis. -/
def claim : Prop :=
  ∀ (R G V N E : Type) [CommRing R] [Group G] [Fintype G]
    [AddCommGroup V] [Module R V] [CommGroup N] [Group E]
    (ρ : Representation R G V) (S : GroupExtension N E G) (ι : Additive N ≃+ V),
    Function.Bijective (SemilinearKernelNorm.coinvariantsNorm ρ) →
    (∀ (e : E) (a : Additive N),
      ι (Additive.ofMul (S.conjAct e a.toMul)) = ρ (S.rightHom e) (ι a)) →
    Nonempty S.Splitting

/-- Bijective native coinvariant norm alone does not force compatible
abelian-kernel extensions over a general finite group to split. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨ρ, S, ι, _, _, _, hnorm, haction, hns⟩ :=
    noncyclic_norm_splitting_counterexample
  exact hns (h (ZMod 3) (DihedralGroup 3) (ZMod 3) (Multiplicative (ZMod 3))
    (DihedralGroup 9) ρ S ι hnorm haction)

end D5.S3.FiniteGroups.GroupAlgebra.NoncyclicNormSplittingCounterexample
