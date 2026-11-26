import GRH.Lib.LocalGL.Green.InductionMean
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: The Brauer lift is a virtual character; cuspidal times Steinberg is induced from a
torus (known result; see Lib.LocalGL.Green.CuspidalInnerProduct).

Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Adjoint of multiplication; it is a derivation for cuspidal functions (Zelevinsky). Möbius
function (Steinberg) lives on semisimple classes; minus the Brauer lift divided by `constOne` is
cuspidal. -/

attribute [local simp] Finset.mul_sum Hall.IsCuspidal Hall.blockAverage_of_dim_eq_zero
  Hall.rankInner Hall.skew

variable {k} [Field k] [Finite k] {F H c f : Hall k} {d n} {o : SimClass k} (hc :
  c.IsCuspidal) (hd : d ≠ 0)

lemma Hall.rankInner_mul_eq_rankInner_skew (hf : ∀ c, c.dim ≠ d → f c = 0) :
  rankInner (d + n) (f * H) F = rankInner n H (skew d f F) := by
  rw [mul_comm, rankInner_mul_eq_sum_skew,
    Finset.sum_eq_single (n, d)] <;> simp +contextual (disch := simp; lia) [*]

omit [Finite k] in
lemma Hall.simClassOf_eq_of_dim_zero (h : o.dim = 0) : o = simClassOf (0 :
  Module.End k (Fin 0 → k)) := simClassOf_out o ▸ simClassOf_eq_of_equiv (h ▸ 1) (by subsingleton)

@[simp] lemma Hall.mul_apply_of_dim_zero (h : o.dim = 0) : (F * H) o = F o * H o := by
  simpa [simClassOf_eq_of_dim_zero, h] using star_inj.2 (rankInner_mul_eq_sum_skew 0 1 F H)

include hc hd

lemma Hall.rankInner_mul_of_isCuspidal : rankInner d c (F * H) =
  rankInner d c F * rankInner 0 constOne H + rankInner 0 constOne F * rankInner d c H := by
  have := star_inj.2 (rankInner_mul_eq_sum_skew d c F H)
  rw [Finset.sum_eq_add (d, 0) (0, d)] at this <;> simp_all [← finMean_conj, mul_comm]
  simp [finMean, Finset.sum_mul, field, mul_assoc]; aesop

lemma Hall.skew_of_isCuspidal : skew d f c = rankInner d f c • 1 := by aesop

lemma Hall.skew_mul : skew d c (F * H) = skew d c F * H + F * skew d c H := by
  ext; simp [mul_simClassOf]
  simp [blockAverage_mul, finMean_sum, @id (finMean _ = _) (rankInner_mul_of_isCuspidal hc hd)]

omit hc hd

namespace Hall

open Module Finset StableSubspace Submodule LinearMap ComplexConjugate End Polynomial

-- Crapo; cf. P. Hall, Krasula arXiv 2403.05656, Lemma 23.

lemma crapo_complementation {L} [Lattice L] [BoundedOrder L] [IsModularLattice L] [Fintype L] {μ :
  L → ℂ} (M : ∀ X ≠ ⊥, ∑ U with U ≤ X, μ U = 0) (h : μ ⊤ ≠ 0) (W : L) : IsComplemented W :=
  (exists_maximal_of_wellFoundedGT _ ⟨⊥, by simp⟩).imp fun C ⟨d, m⟩ ↦ ⟨d,
  codisjoint_iff_le_sup.2 (by_contra (h ∘ (wellFounded_lt.1 ⊤).rec fun U _ _ _ ↦ by rw [← M U,
  ← @sum_sdiff L _ {A | A ≤ U ⊓ (W ⊔ C)}, M, sum_eq_single U] <;> grind [Ne.lt_of_le, disjoint_iff,
  le_sup_left, le_sup_right, le_inf_iff, d.disjoint_sup_right_of_disjoint_sup_left (c := U)]))⟩

variable {k : _} {V K} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V] {g :
  End k V} {o : SimClass k} (B : Hall k) [Field K] [Algebra k K] (η : K → ℂ)

lemma mu_mul_constOne : moebius * constOne = (1 : Hall k) := by grind [isUnit_constOne]

lemma sum_inverse_constOne : ∑ W : StableSubspace g, moebius (simClassOf W.endOnSub) =
  (1 : Hall k) (simClassOf g) := by rw [← mu_mul_constOne]; simp [mul_simClassOf]

attribute [local simp] mul_simClassOf sum_filter projection_apply_of_mem_left greenCuspidal
  aroots_mul charpoly_monic Monic.ne_zero sum_inverse_constOne

lemma isSemisimple_of_mu_ne_zero (h : moebius (simClassOf g) ≠ 0) : g.IsSemisimple :=
  isSemisimple_iff'.2
  (@crapo_complementation _ _ _ ⟨(sup_inf_le_assoc_of_le ·.1)⟩ fintypeStableSubspace _ (fun X n ↦ by
  simpa +contextual [n, by simpa using sum_comap (g := endOnSub X) X.1.subtype (by aesop)]
    using! sum_inverse_constOne (g := endOnSub X)) (by rwa [simClassOf_eq_of_equiv topEquiv]))

@[simp] lemma mu_apply_of_dim_zero (h : o.dim = 0) :
  moebius o = 1 := by simpa [*] using congr($mu_mul_constOne o)

@[simp ↓] lemma blockAverage_mulMu a b : B.mulMu.blockAverage a b =
  moebius a * moebius b * B (simClassOf (b.out.2.prodMap a.out.2)) := by
  erw [← congr($((isUnit_constOne.mul_right_cancel (by
    simp; ext _ b; apply congrFun (isUnit_constOne.mul_right_cancel _) a; ext _ g
    have := blockAverage_mul moebius constOne g b; simp_all [blockAverage_simClassOf, ite_and]) :
    blockAverage moebius a = moebius a • moebius)) b * _),
    blockAverage, mul_comm, ← finMean_const_mul]; congr! 2
  simp [or_iff_not_imp_right]; intro
  obtain ⟨C, c, h⟩ :=
    isSemisimple_iff.1 (isSemisimple_of_mu_ne_zero ‹_›) (.prod ⊥ ⊤) fun _ ↦ by aesop
  rcases projection_apply_mem h, (isIdempotentElem_projection h).ker_mem_invtSubmodule_iff.1
    (by simpa)
  rw [simClassOf_eq_of_equiv (.ofInjectiveEndo (.prod (fst ..) (snd .. ∘ₗ projection _ _ h)) _)
    _] <;> simp_all [injective_iff_map_eq_zero, Prod.ext_iff, ↓mem_prod, DFunLike.ext_iff]

@[simp] lemma conj_mu : ∀ c : SimClass k, conj (moebius c) = moebius c := congrFun
  (isUnit_constOne.mul_right_cancel (ext (by simp [← map_sum])))

@[simp] lemma greenCuspidal_mul_constOne :
  greenCuspidal k η * constOne = -brauerLift k η := by grind [mu_mul_constOne, (ext fun _ g ↦ by
  simp +contextual [← sum_add_distrib, mul_comm (moebius _), ← add_mul, ← Multiset.sum_add,
  ← mul_sum, ← Multiset.map_add, ← aroots_mul, charpoly_endOnSub_mul_endOnQuot,
    ← g.charpoly_natDegree] : greenCuspidal k η + moebius * brauerLift k η = 0)]

lemma greenCuspidal_eq_zero_of_dim_lt_one c : c.dim < 1 →
  greenCuspidal k η c = 0 := by simp_all [simClassOf_eq_of_dim_zero]

lemma isCuspidal_greenCuspidal : (greenCuspidal k η).IsCuspidal := fun a b _ _ ↦
  simClassOf_out a ▸ simClassOf_out b ▸ (blockAverage_mul ..).trans (by simp_all
  [blockAverage, -simClassOf_out, charpoly_prodMap, mul_add, ← mul_sum, ← sum_mul, mul_assoc])
