/- GID: D5/S3/Combinatorics/Geometry/MiuraPartitionCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraPartitionCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The original residual count is the sum of actual exact-core fiber cardinalities. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraPartitionCore

/-! A disjoint partition of individual normalized arrays, with no quotient. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraPartitionCount
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreJoint MiuraCoreNormal
  MiuraSlabIncidence MiuraPolynomialCoreSum MiuraCanonicalJoint MiuraPartitionCore
open scoped BigOperators

/-- This is the actual residual/JointReduction/per-side fiber used by
`MiuraFiberCore.core_positive_vectors_inject`, with the identical full functions. -/
abbrev Fiber (a b m n : ℕ) (K : Core a b) :=
  {g : Cell m n → ℤ // Residual a b g ∧ JointReduction g K.2.2.val ∧
    ∀ sd, AllOnSide (fun v : Cell m n => ((v.1.val : ℤ) + 1,(v.2.val : ℤ) + 1))
      (minima g) (m : ℤ) (n : ℤ) sd ↔
    AllOnSide (fun v : Cell K.1.val K.2.1.val => ((v.1.val : ℤ) + 1,(v.2.val : ℤ) + 1))
      (minima K.2.2.val) (K.1.val : ℤ) (K.2.1.val : ℤ) sd}

private theorem core_raw_injective (a b : ℕ) :
    Function.Injective (fun K : Core a b =>
      (⟨K.1.val,K.2.1.val,K.2.2.val⟩ : Σ M : ℕ, Σ N : ℕ, Cell M N → ℤ)) := by
  rintro ⟨⟨M,hM⟩,⟨N,hN⟩,⟨g,hg⟩⟩ ⟨⟨P,hP⟩,⟨Q,hQ⟩,⟨f,hf⟩⟩ he
  have hMP : M = P := congrArg Sigma.fst he
  subst P
  have he' : (⟨N,g⟩ : Σ N : ℕ, Cell M N → ℤ) = ⟨Q,f⟩ :=
    eq_of_heq (Sigma.mk.inj he).2
  have hNQ : N = Q := congrArg Sigma.fst he'
  subst Q
  have hgf : g = f := eq_of_heq (Sigma.mk.inj he').2
  subst f
  rfl

/-- A single actual unit-edge array cannot reduce to two distinct members of Core. -/
theorem residual_core_unique {a b m n : ℕ} (h : Cell m n → ℤ) (hh : IsHeight h)
    {K L : Core a b} (hK : JointReduction h K.2.2.val)
    (hL : JointReduction h L.2.2.val) : K = L := by
  apply core_raw_injective a b
  exact joint_reduced_core_unique hh hK hL K.2.2.property.2.2.2.1
    K.2.2.property.2.2.2.2.1 L.2.2.property.2.2.2.1 L.2.2.property.2.2.2.2.1

/-- Every individual normalized residual array is retained once in its unique
actual-core fiber; the inverse simply forgets its core index. -/
noncomputable def residualCoreEquiv (a b m n : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd : 5 ≤ a + b) (hm : 2 * (a + b) - 1 ≤ m) (hn : 2 * (a + b) - 1 ≤ n) :
    {g : Cell m n → ℤ // Residual a b g} ≃ Σ K : Core a b, Fiber a b m n K := by
  let forget : (Σ K : Core a b, Fiber a b m n K) →
      {g : Cell m n → ℤ // Residual a b g} := fun x => ⟨x.2.val, x.2.property.1⟩
  apply Equiv.symm
  apply Equiv.ofBijective forget
  constructor
  · rintro ⟨K, ⟨g, hg⟩⟩ ⟨L, ⟨f, hf⟩⟩ he
    have hgf : g = f := congrArg Subtype.val he
    subst f
    have hKL := residual_core_unique g hg.1.1.1 hg.2.1 hf.2.1
    subst L
    rfl
  · rintro ⟨g, hg⟩
    obtain ⟨K, hred, hs⟩ := residual_core_exists a b ha hb hd hm hn g hg
    exact ⟨⟨K, ⟨g, hg, hred, hs⟩⟩, rfl⟩

/-- The original count, without redefining it, equals the finite sum of the
cardinalities of the actual fixed-core fibers at every original large rectangle. -/
theorem residual_count_eq_sum_fibers (a b m n : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd : 5 ≤ a + b) (hm : 2 * (a + b) - 1 ≤ m) (hn : 2 * (a + b) - 1 ≤ n) :
    residualCount a b m n (by omega) (by omega) =
      ∑ K : Core a b, Nat.card (Fiber a b m n K) := by
  classical
  let : Finite {g : Cell m n → ℤ // Residual a b g} :=
    (residual_finite a b (by omega) (by omega)).to_subtype
  let (K : Core a b) : Finite (Fiber a b m n K) :=
    Finite.of_injective (fun g => (⟨g.val,g.property.1⟩ : {g : Cell m n → ℤ // Residual a b g}))
      (by
        intro x y he
        apply Subtype.ext
        exact congrArg (fun z : {g : Cell m n → ℤ // Residual a b g} => z.val) he)
  rw [residualCount,←Nat.card_eq_card_finite_toFinset (residual_finite a b (by omega) (by omega))]
  exact (Nat.card_congr (residualCoreEquiv a b m n ha hb hd hm hn)).trans Nat.card_sigma

end D5.S3.Combinatorics.Geometry.MiuraPartitionCount
