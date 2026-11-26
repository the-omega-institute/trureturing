import GRH.Lib.General.LinearAlgebra.ValuedMatrix
import GRH.Lib.LocalGL.Green.FrobeniusOrbits
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Cuspidal class functions vanish unless the characteristic polynomial is a prime power. -/

open Hall LinearMap Module Polynomial StableSubspace Submodule

variable {k V} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V] {g : End k V}

omit [Finite k] in
lemma charpoly_eq_pow_of_isNilpotent {P} (hP : Irreducible P) (hm : Monic P) (h :
  IsNilpotent (aeval g P)) : charpoly g = P ^ (finrank k V / P.natDegree) := by
  have := charpoly_dvd_charpoly_aeval_comp (Y := g.toMatrixAlgEquiv (finBasis ..)) P
  simp_all [↓aeval_algHom_apply, toMatrixAlgEquiv, h.charpoly_eq_X_pow_finrank]
  grind [charpoly_natDegree, natDegree_pow, Nat.mul_div_left, dvd_prime_pow hP.prime,
    eq_of_monic_of_associated, charpoly_monic, Monic.pow]

/-- Over a finite field k, if F is cuspidal (`Hall.IsCuspidal`) and does not vanish at the class
of an endomorphism g, then the characteristic polynomial of g is a power of an irreducible
polynomial. -/
lemma Hall.IsCuspidal.exists_charpoly_eq_pow {F} (h : IsCuspidal F) (hF : F (simClassOf g) ≠ 0) :
  ∃ P j, Irreducible P ∧ charpoly g =
  P ^ j := by_cases (⟨X, 0, irreducible_X, g.charpoly_monic.eq_one_of_isUnit ·⟩) fun u ↦ by
  have ⟨P, m, i, d⟩ := (g.toMatrixAlgEquiv _).charpoly.exists_monic_irreducible_factor u
  have ⟨N, I, n⟩ := ((aeval g P).eventually_isCompl_ker_pow_range_pow.and Nat.eventually_pos).exists
  have c Y h := DFunLike.congr_fun (Algebra.commute_of_mem_adjoin_singleton_of_commute
    ((P ^ N).aeval_mem_adjoin_singleton k g) ((Y * g).ext h))
  simp_all [aeval_algHom_apply, i.dvd_iff_not_isCoprime,
    ← isUnit_aeval_iff_isCoprime.trans isCoprime_comm]
  let C : StableSubspace g := ⟨ker (aeval g P ^ N), by simp_all [← c]⟩
  have E : ∀ x, simClassOf (blockTriangularEnd C.endOnSub C.endOnQuot x) = simClassOf g :=
    (surjective_of_injective (.of_ker (C.endOnSub.compRight k - C.endOnQuot.lcomp ..) fun y e ↦
    y.ext ((reindex_equiv (quotientEquivOfIsCompl _ _ I).symm).1.2 fun ⟨_, v, rfl⟩ ↦ Subtype.ext
    ((c (C.1.subtype ∘ₗ y ∘ₗ mkQ _) (congr($(sub_eq_zero.1 e) ⟦·⟧ |>.1).symm) v).trans
    (y _).2)))).forall.2 fun y ↦ simClassOf_eq_of_equiv (.skewProd (quotKerEquivRange _) 1 y ≪≫ₗ
    prodEquivOfIsCompl _ _ I.symm)
    (by simp [Submodule.Quotient.forall, endOnSub, endOnQuot, C]; grind)
  exact ⟨P, i, _, charpoly_eq_pow_of_isNilpotent i m
    ⟨N, by simpa [*, C, blockAverage_simClassOf, n.ne', ← isUnit_iff_ker_eq_bot,
    finrank_zero_iff, ↓finrank_eq_zero] using h (simClassOf C.endOnSub) (simClassOf C.endOnQuot)⟩⟩

lemma greenCuspidal_congr {K} [Field K] [Algebra k K] η η' {a} (h : ∀ z, g.charpoly.aroots K =
  .map (z ^ .card k ^ ·) (.range (finrank k V)) ∧ z ^ .card k ^ finrank k V = z → a * η z = η' z) :
  greenCuspidal k η' (simClassOf g) = a * greenCuspidal k η (simClassOf g) := by_contra (· <| by
  simp [greenCuspidal, mul_simClassOf, mulMu, Finset.mul_sum, ← mul_assoc,
    ← Multiset.sum_map_mul_left]
  congr! with W _ z; grind +splitImp [isCuspidal_greenCuspidal, → IsCuspidal.exists_charpoly_eq_pow,
    aroots_pow_eq_frobenius_orbit, mem_aroots,
    pow_ne_zero, congr(aeval z $(charpoly_endOnSub_mul_endOnQuot _ W)), charpoly_natDegree])
