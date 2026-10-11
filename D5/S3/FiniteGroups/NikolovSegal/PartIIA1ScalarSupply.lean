/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary-automorphism A1 scalar, twisted and transitive products. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIPSL2RootNormalization
import D5.S3.FiniteGroups.NikolovSegal.PartIISL2RootSylow
import D5.S3.FiniteGroups.NikolovSegal.PartIILemma41
set_option autoImplicit false
namespace NikolovSegal.PartIIA1RootSupply
open PartIISL2RootSylow
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F] [Finite F]
private def pi : SL(2,F) →* PSL(2,F) := QuotientGroup.mk' (Subgroup.center _)

private theorem upper_root_carrier : (upperRoot (F := F) : Set SL(2,F)) = Set.range upper := by
  ext g
  exact mem_upperRoot g

private theorem arbitrary_SL2_upper_conjugacy (beta : MulAut SL(2,F)) :
    ∃ A : SL(2,F), Set.range (fun t : F => beta (upper t)) =
      Set.range (fun t : F => MulAut.conj A (upper t)) := by
  letI : Fact (Nat.Prime (ringChar F)) := ⟨CharP.char_is_prime F (ringChar F)⟩
  obtain ⟨A,hA⟩ := automorphism_upperRoot_conjugate (ringChar F) beta
  refine ⟨A,?_⟩
  have hh := congrArg (fun U : Subgroup SL(2,F) => (U : Set SL(2,F))) hA
  rw [Subgroup.coe_map,Subgroup.coe_map,upper_root_carrier,
    ← Set.range_comp',← Set.range_comp'] at hh
  exact hh

private theorem arbitrary_SL2_lower_conjugacy (beta : MulAut SL(2,F)) :
    ∃ B : SL(2,F), Set.range (fun t : F => beta (lower t)) =
      Set.range (fun t : F => MulAut.conj B (upper t)) := by
  obtain ⟨B,hB⟩ := arbitrary_SL2_upper_conjugacy (beta*MulAut.conj (a1Weyl (1:F) one_ne_zero))
  refine ⟨B,?_⟩
  have he : Set.range (fun t : F => (beta*MulAut.conj (a1Weyl (1:F) one_ne_zero)) (upper t)) =
      Set.range (fun t : F => beta (lower t)) := by
    simp only [MulAut.mul_apply,a1Weyl_upper,inv_one,one_pow,neg_one_mul]
    simpa only [Function.comp_def] using (neg_surjective : Function.Surjective (fun t : F => -t)).range_comp (fun t : F => beta (lower t))
  rw [he] at hB
  exact hB

/-- Genuine PartII A1 scalar PRODUCT for ALL prescribed SL2 automorphisms,
not just root-stabilizing or semilinear tuples. Sylow conjugacy and actual
root alignment/field reconstruction supply the root laws without hypotheses. -/
theorem actual_SL2_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (beta : Fin (4*M) → MulAut SL(2,F)) (e : Fin (4*M) → ℕ) :
    PartIIScalarProductInput q (4*M) beta e := by
  classical
  choose A hA using fun j => arbitrary_SL2_upper_conjugacy (beta j)
  choose B hB using fun j => arbitrary_SL2_lower_conjugacy (beta j)
  exact actual_root_conjugate_SL2_scalar_product hq hM hF beta e A B hA hB

private theorem pi_conj (A : SL(2,F)) (t : F) :
    MulAut.conj (pi A) (projectiveUpper t) = pi (MulAut.conj A (upper t)) := by
  change MulAut.conj (pi A) (pi (upper t)) = pi (MulAut.conj A (upper t))
  simp only [MulAut.conj_apply,map_mul,map_inv]

private theorem arbitrary_PSL2_upper_conjugacy (beta : MulAut PSL(2,F)) :
    ∃ A : SL(2,F), Set.range (fun t : F => beta (projectiveUpper t)) =
      Set.range (fun t : F => pi (MulAut.conj A (upper t))) := by
  letI : Fact (Nat.Prime (ringChar F)) := ⟨CharP.char_is_prime F (ringChar F)⟩
  let P := (upperSylow (F := F) (ringChar F)).mapSurjective (f := pi) (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective (f := beta.toMonoidHom) beta.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(2,F) P Q
  obtain ⟨A,hA⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2,F)) g
  change pi A = g at hA
  have he := congrArg (fun R : Sylow (ringChar F) PSL(2,F) => (R : Subgroup PSL(2,F))) hg
  change (upperRoot.map pi).map (MulAut.conj g).toMonoidHom =
      (upperRoot.map pi).map beta.toMonoidHom at he
  rw [← hA] at he
  have hh := congrArg (fun U : Subgroup PSL(2,F) => (U : Set PSL(2,F))) he.symm
  simp only [Subgroup.coe_map,upper_root_carrier,← Set.range_comp'] at hh
  change Set.range (fun t : F => beta (pi (upper t))) =
    Set.range (fun t : F => MulAut.conj (pi A) (pi (upper t))) at hh
  refine ⟨A,?_⟩
  change Set.range (fun t : F => beta (projectiveUpper t)) = Set.range (fun t : F => MulAut.conj (pi A) (projectiveUpper t)) at hh
  simpa only [pi_conj] using hh

private theorem arbitrary_PSL2_lower_conjugacy (beta : MulAut PSL(2,F)) :
    ∃ B : SL(2,F), Set.range (fun t : F => beta (projectiveLower t)) =
      Set.range (fun t : F => pi (MulAut.conj B (upper t))) := by
  obtain ⟨B,hB⟩ := arbitrary_PSL2_upper_conjugacy (beta*MulAut.conj (pi (a1Weyl (1:F) one_ne_zero)))
  have hw : ∀ t : F, MulAut.conj (pi (a1Weyl (1:F) one_ne_zero)) (projectiveUpper t) = projectiveLower (-t) := by
    intro t
    rw [pi_conj,a1Weyl_upper,inv_one,one_pow,neg_one_mul]
    rfl
  have he : Set.range (fun t : F => (beta*MulAut.conj (pi (a1Weyl (1:F) one_ne_zero))) (projectiveUpper t)) =
      Set.range (fun t : F => beta (projectiveLower t)) := by
    simp only [MulAut.mul_apply,hw]
    simpa only [Function.comp_def] using (neg_surjective : Function.Surjective (fun t : F => -t)).range_comp (fun t : F => beta (projectiveLower t))
  rw [he] at hB
  exact ⟨B,hB⟩

/-- Genuine full A1 scalar PRODUCT for arbitrary PSL2 automorphism tuples.
No lift, semilinearity, root-image law, classification or coverage is a premise.
ONE globally consistent correction precedes every full projective target. -/
theorem actual_PSL2_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (beta : Fin (4*M) → MulAut PSL(2,F)) (e : Fin (4*M) → ℕ) :
    PartIIScalarProductInput q (4*M) beta e := by
  classical
  choose A hA using fun j => arbitrary_PSL2_upper_conjugacy (beta j)
  choose B hB using fun j => arbitrary_PSL2_lower_conjugacy (beta j)
  exact actual_root_conjugate_PSL2_scalar_product hq hM hF beta e A B hA hB

/-- PartII chosen-length scalar PRODUCT for arbitrary PSL2 automorphisms.
The explicit constants precede EVERY finite field and automorphism/divisor
sequence, using the actual GROUP cardinality as cutoff. -/
theorem uniform_PSL2_scalar_products (q : ℕ) (hq : 0 < q) :
    ∃ m C : ℕ, 0 < m ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C < Nat.card PSL(2,F) → ∀ beta : Fin m → MulAut PSL(2,F),
      ∀ e : Fin m → ℕ, PartIIScalarProductInput q m beta e := by
  let M := q*(2*q+1)+1
  let K := 2*(2*q+1)^q
  refine ⟨4*M,K^4,by dsimp [M]; positivity,?_⟩
  intro F _ _ _ hcard beta e
  have hf : K < Fintype.card F := by
    by_contra hn
    have hle : Fintype.card F ≤ K := Nat.le_of_not_gt hn
    have hb : Nat.card PSL(2,F) ≤ Fintype.card F ^ 4 := a1Kernel% projective_card_bound
    exact (not_lt_of_ge (hb.trans (Nat.pow_le_pow_left hle 4))) hcard
  exact actual_PSL2_scalar_product hq (by dsimp [M]; omega) hf beta e

/-- The published Lemma4.1 deduction now has a PROVED arbitrary-auto A1
scalar input, giving the actual 16-fold twisted PRODUCT theorem. -/
theorem actual_PSL2_twisted_product [Fintype F] [DecidableEq F]
    (hF : 6 < Fintype.card F) : Equation47WordCoupling.PartIITwistedProductInput PSL(2,F) 16 := by
  apply twisted_input_of_scalar_one
  intro beta
  exact actual_PSL2_scalar_product (q := 1) (M := 4)
    (by omega) (by omega) (by simpa using hF) beta (fun _ => 1)

/-- A genuine family of the unchanged transitive target, with no scalar or
twisted PRODUCT premises: all PSL2 fields above a uniform GROUP cutoff,
all finite ranks and all genuine prescribed component/permutation tuples.
The accepted mixed powered-component reconstruction is reused unchanged.
This is A1 support; exhaustion of all finite-simple families remains open. -/
theorem uniform_PSL2_transitive_coverage (q : ℕ) (hq : 0 < q) :
    ∃ m C : ℕ, 0 < m ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C < Nat.card PSL(2,F) → ∀ (I : Type u) [Finite I] [Nonempty I],
      ∀ (k : Fin m → MulAut (I → PSL(2,F))) (sigma : Fin m → Equiv.Perm I)
        (beta : Fin m → I → MulAut PSL(2,F)),
      (∀ j z i, k j z (sigma j i) = beta j i (z i)) →
      PrescribedCommutatorCoverage (I → PSL(2,F)) q m k := by
  let M := 4*(q*(2*q+1)+1)
  let K := 2*(2*q+1)^q
  let m := M*36*(q+36)
  refine ⟨m,max (K^4) (6^4),by dsimp [m,M]; positivity,?_⟩
  intro F _ _ _ hcard I _ _ k sigma beta hcoord
  classical
  letI : Fintype I := Fintype.ofFinite I
  have hfield : ∀ A : ℕ, A^4 < Nat.card PSL(2,F) → A < Fintype.card F := by
    intro A ha
    by_contra hn
    have hb : Nat.card PSL(2,F) ≤ Fintype.card F ^ 4 := a1Kernel% projective_card_bound
    exact (not_lt_of_ge (hb.trans (Nat.pow_le_pow_left (Nat.le_of_not_gt hn) 4))) ha
  have hfq : K < Fintype.card F := hfield K ((le_max_left _ _).trans_lt hcard)
  have hf1 : 6 < Fintype.card F := hfield 6 ((le_max_right _ _).trans_lt hcard)
  exact prescribed_coverage_from_published_products (M := M) (D := 16) hq
    (by dsimp [M]; positivity) (by dsimp [m]; norm_num)
    k sigma beta hcoord
    (fun b e => actual_PSL2_scalar_product hq (by omega) hfq b e)
    (actual_PSL2_twisted_product hf1)
end NikolovSegal.PartIIA1RootSupply
